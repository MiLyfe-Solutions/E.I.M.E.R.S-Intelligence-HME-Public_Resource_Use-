import V185TrunkScan23Chunk1304

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_7729910 : List Nat := [5, 1, 1, 1, 1, 2, 4, 1, 1, 1, 5]
def baseStart_7729910 : Nat := 118140960795 + 7729910 * 2 ^ 59
def prefixEnd_7729910 : Nat := 4983230072969 + 3 ^ 40 * 7729910 * 2
def baseEnd_7729910 : Nat := 3969159245995956925275797

theorem tailTrace_7729910 : CollatzResearch.WordTrace tailWord_7729910 prefixEnd_7729910 3969159245995956925275797 := by
  unfold tailWord_7729910
  simp only [CollatzResearch.WordTrace]
  refine ⟨17620811214116481773095199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 187955319617242472246348789 17620811214116481773095199)
  ·
    refine ⟨26431216821174722659642799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17620811214116481773095199 26431216821174722659642799)
    ·
      refine ⟨39646825231762083989464199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26431216821174722659642799 39646825231762083989464199)
      ·
        refine ⟨59470237847643125984196299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39646825231762083989464199 59470237847643125984196299)
        ·
          refine ⟨89205356771464688976294449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59470237847643125984196299 89205356771464688976294449)
          ·
            refine ⟨66904017578598516732220837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 89205356771464688976294449 66904017578598516732220837)
            ·
              refine ⟨12544503295987221887291407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 66904017578598516732220837 12544503295987221887291407)
              ·
                refine ⟨18816754943980832830937111, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12544503295987221887291407 18816754943980832830937111)
                ·
                  refine ⟨28225132415971249246405667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18816754943980832830937111 28225132415971249246405667)
                  ·
                    refine ⟨42337698623956873869608501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28225132415971249246405667 42337698623956873869608501)
                    ·
                      refine ⟨3969159245995956925275797, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42337698623956873869608501 3969159245995956925275797)
                      ·
                        rfl

theorem cell23_7729910_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 4, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 4, 1, 1, 1, 5].length) (baseStart_7729910 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7729910 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7729910 prefixEnd_7729910 := by exact prefixLift 7729910
  have htrace : WordTrace (prefixWord ++ tailWord_7729910) baseStart_7729910 baseEnd_7729910 := by
    simpa [prefixWord, tailWord_7729910, baseEnd_7729910] using wordTrace_append hprefix tailTrace_7729910
  have hstable : (prefixWord ++ tailWord_7729910).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7729910).length < 2 ^ (prefixWord ++ tailWord_7729910).sum := by decide
  have hdescent : baseEnd_7729910 < baseStart_7729910 := by decide
  rcases family_descends (prefixWord ++ tailWord_7729910) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7729980 : List Nat := [2, 2, 2, 2, 1, 1, 1, 1, 5, 4, 2]
def baseStart_7729980 : Nat := 118140960795 + 7729980 * 2 ^ 59
def prefixEnd_7729980 : Nat := 4983230072969 + 3 ^ 40 * 7729980 * 2
def baseEnd_7729980 : Nat := 3969195189641771651400475

theorem tailTrace_7729980 : CollatzResearch.WordTrace tailWord_7729980 prefixEnd_7729980 3969195189641771651400475 := by
  unfold tailWord_7729980
  simp only [CollatzResearch.WordTrace]
  refine ⟨140967766267805055162285697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 187957021690406740216380929 140967766267805055162285697)
  ·
    refine ⟨105725824700853791371714273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 140967766267805055162285697 105725824700853791371714273)
    ·
      refine ⟨79294368525640343528785705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 105725824700853791371714273 79294368525640343528785705)
      ·
        refine ⟨59470776394230257646589279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79294368525640343528785705 59470776394230257646589279)
        ·
          refine ⟨89206164591345386469883919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59470776394230257646589279 89206164591345386469883919)
          ·
            refine ⟨133809246887018079704825879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89206164591345386469883919 133809246887018079704825879)
            ·
              refine ⟨200713870330527119557238819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 133809246887018079704825879 200713870330527119557238819)
              ·
                refine ⟨301070805495790679335858229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 200713870330527119557238819 301070805495790679335858229)
                ·
                  refine ⟨28225388015230376187736709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 301070805495790679335858229 28225388015230376187736709)
                  ·
                    refine ⟨5292260252855695535200633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28225388015230376187736709 5292260252855695535200633)
                    ·
                      refine ⟨3969195189641771651400475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5292260252855695535200633 3969195189641771651400475)
                      ·
                        rfl

theorem cell23_7729980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 1, 1, 5, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 1, 1, 5, 4, 2].length) (baseStart_7729980 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7729980 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7729980 prefixEnd_7729980 := by exact prefixLift 7729980
  have htrace : WordTrace (prefixWord ++ tailWord_7729980) baseStart_7729980 baseEnd_7729980 := by
    simpa [prefixWord, tailWord_7729980, baseEnd_7729980] using wordTrace_append hprefix tailTrace_7729980
  have hstable : (prefixWord ++ tailWord_7729980).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7729980).length < 2 ^ (prefixWord ++ tailWord_7729980).sum := by decide
  have hdescent : baseEnd_7729980 < baseStart_7729980 := by decide
  rcases family_descends (prefixWord ++ tailWord_7729980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7729993 : List Nat := [1, 2, 1, 1, 2, 5, 1, 1, 1, 4, 4]
def baseStart_7729993 : Nat := 118140960795 + 7729993 * 2 ^ 59
def prefixEnd_7729993 : Nat := 4983230072969 + 3 ^ 40 * 7729993 * 2
def baseEnd_7729993 : Nat := 3969201864890280100537915

theorem tailTrace_7729993 : CollatzResearch.WordTrace tailWord_7729993 prefixEnd_7729993 3969201864890280100537915 := by
  unfold tailWord_7729993
  simp only [CollatzResearch.WordTrace]
  refine ⟨281936006684563013544794633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187957337789708675696529755 281936006684563013544794633)
  ·
    refine ⟨211452005013422260158595975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 281936006684563013544794633 211452005013422260158595975)
    ·
      refine ⟨317178007520133390237893963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 211452005013422260158595975 317178007520133390237893963)
      ·
        refine ⟨475767011280200085356840945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 317178007520133390237893963 475767011280200085356840945)
        ·
          refine ⟨356825258460150064017630709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 475767011280200085356840945 356825258460150064017630709)
          ·
            refine ⟨33452367980639068501652879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 356825258460150064017630709 33452367980639068501652879)
            ·
              refine ⟨50178551970958602752479319, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33452367980639068501652879 50178551970958602752479319)
              ·
                refine ⟨75267827956437904128718979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50178551970958602752479319 75267827956437904128718979)
                ·
                  refine ⟨112901741934656856193078469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 75267827956437904128718979 112901741934656856193078469)
                  ·
                    refine ⟨21169076612748160536202213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 112901741934656856193078469 21169076612748160536202213)
                    ·
                      refine ⟨3969201864890280100537915, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21169076612748160536202213 3969201864890280100537915)
                      ·
                        rfl

theorem cell23_7729993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 1, 1, 1, 4, 4].length) (baseStart_7729993 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7729993 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7729993 prefixEnd_7729993 := by exact prefixLift 7729993
  have htrace : WordTrace (prefixWord ++ tailWord_7729993) baseStart_7729993 baseEnd_7729993 := by
    simpa [prefixWord, tailWord_7729993, baseEnd_7729993] using wordTrace_append hprefix tailTrace_7729993
  have hstable : (prefixWord ++ tailWord_7729993).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7729993).length < 2 ^ (prefixWord ++ tailWord_7729993).sum := by decide
  have hdescent : baseEnd_7729993 < baseStart_7729993 := by decide
  rcases family_descends (prefixWord ++ tailWord_7729993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7730018 : List Nat := [3, 3, 2, 1, 3, 2, 2, 1, 1, 3, 2]
def baseStart_7730018 : Nat := 118140960795 + 7730018 * 2 ^ 59
def prefixEnd_7730018 : Nat := 4983230072969 + 3 ^ 40 * 7730018 * 2
def baseEnd_7730018 : Nat := 3969214701906642502725301

theorem tailTrace_7730018 : CollatzResearch.WordTrace tailWord_7730018 prefixEnd_7730018 3969214701906642502725301 := by
  unfold tailWord_7730018
  simp only [CollatzResearch.WordTrace]
  refine ⟨70484229627368110703613677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 187957945672981628542969805 70484229627368110703613677)
  ·
    refine ⟨26431586110263041513855129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 70484229627368110703613677 26431586110263041513855129)
    ·
      refine ⟨19823689582697281135391347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26431586110263041513855129 19823689582697281135391347)
      ·
        refine ⟨29735534374045921703087021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19823689582697281135391347 29735534374045921703087021)
        ·
          refine ⟨11150825390267220638657633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29735534374045921703087021 11150825390267220638657633)
          ·
            refine ⟨8363119042700415478993225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11150825390267220638657633 8363119042700415478993225)
            ·
              refine ⟨6272339282025311609244919, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8363119042700415478993225 6272339282025311609244919)
              ·
                refine ⟨9408508923037967413867379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6272339282025311609244919 9408508923037967413867379)
                ·
                  refine ⟨14112763384556951120801069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9408508923037967413867379 14112763384556951120801069)
                  ·
                    refine ⟨5292286269208856670300401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14112763384556951120801069 5292286269208856670300401)
                    ·
                      refine ⟨3969214701906642502725301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5292286269208856670300401 3969214701906642502725301)
                      ·
                        rfl

theorem cell23_7730018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 3, 2, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 3, 2, 2, 1, 1, 3, 2].length) (baseStart_7730018 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7730018 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7730018 prefixEnd_7730018 := by exact prefixLift 7730018
  have htrace : WordTrace (prefixWord ++ tailWord_7730018) baseStart_7730018 baseEnd_7730018 := by
    simpa [prefixWord, tailWord_7730018, baseEnd_7730018] using wordTrace_append hprefix tailTrace_7730018
  have hstable : (prefixWord ++ tailWord_7730018).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7730018).length < 2 ^ (prefixWord ++ tailWord_7730018).sum := by decide
  have hdescent : baseEnd_7730018 < baseStart_7730018 := by decide
  rcases family_descends (prefixWord ++ tailWord_7730018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7730037 : List Nat := [1, 3, 4, 1, 1, 2, 2, 4, 5]
def baseStart_7730037 : Nat := 118140960795 + 7730037 * 2 ^ 59
def prefixEnd_7730037 : Nat := 4983230072969 + 3 ^ 40 * 7730037 * 2
def baseEnd_7730037 : Nat := 441024939782119769820857

theorem tailTrace_7730037 : CollatzResearch.WordTrace tailWord_7730037 prefixEnd_7730037 441024939782119769820857 := by
  unfold tailWord_7730037
  simp only [CollatzResearch.WordTrace]
  refine ⟨281937611496403609059396365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187958407664269072706264243 281937611496403609059396365)
  ·
    refine ⟨105726604311151353397273637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 281937611496403609059396365 105726604311151353397273637)
    ·
      refine ⟨19823738308340878761988807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 105726604311151353397273637 19823738308340878761988807)
      ·
        refine ⟨29735607462511318142983211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19823738308340878761988807 29735607462511318142983211)
        ·
          refine ⟨44603411193766977214474817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29735607462511318142983211 44603411193766977214474817)
          ·
            refine ⟨33452558395325232910856113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44603411193766977214474817 33452558395325232910856113)
            ·
              refine ⟨25089418796493924683142085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33452558395325232910856113 25089418796493924683142085)
              ·
                refine ⟨4704266024342610878089141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25089418796493924683142085 4704266024342610878089141)
                ·
                  refine ⟨441024939782119769820857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4704266024342610878089141 441024939782119769820857)
                  ·
                    rfl

theorem cell23_7730037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 2, 4, 5].length) (baseStart_7730037 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7730037 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7730037 prefixEnd_7730037 := by exact prefixLift 7730037
  have htrace : WordTrace (prefixWord ++ tailWord_7730037) baseStart_7730037 baseEnd_7730037 := by
    simpa [prefixWord, tailWord_7730037, baseEnd_7730037] using wordTrace_append hprefix tailTrace_7730037
  have hstable : (prefixWord ++ tailWord_7730037).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7730037).length < 2 ^ (prefixWord ++ tailWord_7730037).sum := by decide
  have hdescent : baseEnd_7730037 < baseStart_7730037 := by decide
  rcases family_descends (prefixWord ++ tailWord_7730037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7730040 : List Nat := [2, 1, 2, 1, 1, 1, 1, 5, 2, 5, 2]
def baseStart_7730040 : Nat := 118140960795 + 7730040 * 2 ^ 59
def prefixEnd_7730040 : Nat := 4983230072969 + 3 ^ 40 * 7730040 * 2
def baseEnd_7730040 : Nat := 3969225998481041416650199

theorem tailTrace_7730040 : CollatzResearch.WordTrace tailWord_7730040 prefixEnd_7730040 3969225998481041416650199 := by
  unfold tailWord_7730040
  simp only [CollatzResearch.WordTrace]
  refine ⟨140968860457696370285877787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 187958480610261827047837049 140968860457696370285877787)
  ·
    refine ⟨211453290686544555428816681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140968860457696370285877787 211453290686544555428816681)
    ·
      refine ⟨158589968014908416571612511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 211453290686544555428816681 158589968014908416571612511)
      ·
        refine ⟨237884952022362624857418767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 158589968014908416571612511 237884952022362624857418767)
        ·
          refine ⟨356827428033543937286128151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 237884952022362624857418767 356827428033543937286128151)
          ·
            refine ⟨535241142050315905929192227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 356827428033543937286128151 535241142050315905929192227)
            ·
              refine ⟨802861713075473858893788341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 535241142050315905929192227 802861713075473858893788341)
              ·
                refine ⟨75268285600825674271292657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 802861713075473858893788341 75268285600825674271292657)
                ·
                  refine ⟨56451214200619255703469493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 75268285600825674271292657 56451214200619255703469493)
                  ·
                    refine ⟨5292301331308055222200265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 56451214200619255703469493 5292301331308055222200265)
                    ·
                      refine ⟨3969225998481041416650199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5292301331308055222200265 3969225998481041416650199)
                      ·
                        rfl

theorem cell23_7730040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 5, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 5, 2, 5, 2].length) (baseStart_7730040 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7730040 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7730040 prefixEnd_7730040 := by exact prefixLift 7730040
  have htrace : WordTrace (prefixWord ++ tailWord_7730040) baseStart_7730040 baseEnd_7730040 := by
    simpa [prefixWord, tailWord_7730040, baseEnd_7730040] using wordTrace_append hprefix tailTrace_7730040
  have hstable : (prefixWord ++ tailWord_7730040).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7730040).length < 2 ^ (prefixWord ++ tailWord_7730040).sum := by decide
  have hdescent : baseEnd_7730040 < baseStart_7730040 := by decide
  rcases family_descends (prefixWord ++ tailWord_7730040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7730043 : List Nat := [1, 1, 1, 1, 1, 5, 2, 3, 1, 2, 5]
def baseStart_7730043 : Nat := 118140960795 + 7730043 * 2 ^ 59
def prefixEnd_7730043 : Nat := 4983230072969 + 3 ^ 40 * 7730043 * 2
def baseEnd_7730043 : Nat := 3969227538923004904912685

theorem tailTrace_7730043 : CollatzResearch.WordTrace tailWord_7730043 prefixEnd_7730043 3969227538923004904912685 := by
  unfold tailWord_7730043
  simp only [CollatzResearch.WordTrace]
  refine ⟨281937830334381872084114783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187958553556254581389409855 281937830334381872084114783)
  ·
    refine ⟨422906745501572808126172175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 281937830334381872084114783 422906745501572808126172175)
    ·
      refine ⟨634360118252359212189258263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 422906745501572808126172175 634360118252359212189258263)
      ·
        refine ⟨951540177378538818283887395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 634360118252359212189258263 951540177378538818283887395)
        ·
          refine ⟨1427310266067808227425831093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 951540177378538818283887395 1427310266067808227425831093)
          ·
            refine ⟨133810337443857021321171665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 1427310266067808227425831093 133810337443857021321171665)
            ·
              refine ⟨100357753082892765990878749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 133810337443857021321171665 100357753082892765990878749)
              ·
                refine ⟨37634157406084787246579531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 100357753082892765990878749 37634157406084787246579531)
                ·
                  refine ⟨56451236109127180869869297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37634157406084787246579531 56451236109127180869869297)
                  ·
                    refine ⟨42338427081845385652401973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 56451236109127180869869297 42338427081845385652401973)
                    ·
                      refine ⟨3969227538923004904912685, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42338427081845385652401973 3969227538923004904912685)
                      ·
                        rfl

theorem cell23_7730043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 2, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 2, 3, 1, 2, 5].length) (baseStart_7730043 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7730043 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7730043 prefixEnd_7730043 := by exact prefixLift 7730043
  have htrace : WordTrace (prefixWord ++ tailWord_7730043) baseStart_7730043 baseEnd_7730043 := by
    simpa [prefixWord, tailWord_7730043, baseEnd_7730043] using wordTrace_append hprefix tailTrace_7730043
  have hstable : (prefixWord ++ tailWord_7730043).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7730043).length < 2 ^ (prefixWord ++ tailWord_7730043).sum := by decide
  have hdescent : baseEnd_7730043 < baseStart_7730043 := by decide
  rcases family_descends (prefixWord ++ tailWord_7730043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7730073 : List Nat := [1, 2, 1, 2, 1, 3, 1, 2, 2, 3, 5]
def baseStart_7730073 : Nat := 118140960795 + 7730073 * 2 ^ 59
def prefixEnd_7730073 : Nat := 4983230072969 + 3 ^ 40 * 7730073 * 2
def baseEnd_7730073 : Nat := 3969242943342639787537547

theorem tailTrace_7730073 : CollatzResearch.WordTrace tailWord_7730073 prefixEnd_7730073 3969242943342639787537547 := by
  unfold tailWord_7730073
  simp only [CollatzResearch.WordTrace]
  refine ⟨281938924524273187207706873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187959283016182124805137915 281938924524273187207706873)
  ·
    refine ⟨211454193393204890405780155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 281938924524273187207706873 211454193393204890405780155)
    ·
      refine ⟨317181290089807335608670233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 211454193393204890405780155 317181290089807335608670233)
      ·
        refine ⟨237885967567355501706502675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 317181290089807335608670233 237885967567355501706502675)
        ·
          refine ⟨356828951351033252559754013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 237885967567355501706502675 356828951351033252559754013)
          ·
            refine ⟨133810856756637469709907755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 356828951351033252559754013 133810856756637469709907755)
            ·
              refine ⟨200716285134956204564861633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 133810856756637469709907755 200716285134956204564861633)
              ·
                refine ⟨150537213851217153423646225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 200716285134956204564861633 150537213851217153423646225)
                ·
                  refine ⟨112902910388412865067734669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 150537213851217153423646225 112902910388412865067734669)
                  ·
                    refine ⟨42338591395654824400400501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 112902910388412865067734669 42338591395654824400400501)
                    ·
                      refine ⟨3969242943342639787537547, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42338591395654824400400501 3969242943342639787537547)
                      ·
                        rfl

theorem cell23_7730073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 1, 2, 2, 3, 5].length) (baseStart_7730073 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7730073 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7730073 prefixEnd_7730073 := by exact prefixLift 7730073
  have htrace : WordTrace (prefixWord ++ tailWord_7730073) baseStart_7730073 baseEnd_7730073 := by
    simpa [prefixWord, tailWord_7730073, baseEnd_7730073] using wordTrace_append hprefix tailTrace_7730073
  have hstable : (prefixWord ++ tailWord_7730073).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7730073).length < 2 ^ (prefixWord ++ tailWord_7730073).sum := by decide
  have hdescent : baseEnd_7730073 < baseStart_7730073 := by decide
  rcases family_descends (prefixWord ++ tailWord_7730073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7730080 : List Nat := [2, 1, 1, 4, 1, 1, 2, 2, 5, 4]
def baseStart_7730080 : Nat := 118140960795 + 7730080 * 2 ^ 59
def prefixEnd_7730080 : Nat := 4983230072969 + 3 ^ 40 * 7730080 * 2
def baseEnd_7730080 : Nat := 1323082179235740420050005

theorem tailTrace_7730080 : CollatzResearch.WordTrace tailWord_7730080 prefixEnd_7730080 1323082179235740420050005 := by
  unfold tailWord_7730080
  simp only [CollatzResearch.WordTrace]
  refine ⟨140969589917623913701605847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 187959453223498551602141129 140969589917623913701605847)
  ·
    refine ⟨211454384876435870552408771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140969589917623913701605847 211454384876435870552408771)
    ·
      refine ⟨317181577314653805828613157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 211454384876435870552408771 317181577314653805828613157)
      ·
        refine ⟨59471545746497588592864967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 317181577314653805828613157 59471545746497588592864967)
        ·
          refine ⟨89207318619746382889297451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59471545746497588592864967 89207318619746382889297451)
          ·
            refine ⟨133810977929619574333946177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89207318619746382889297451 133810977929619574333946177)
            ·
              refine ⟨100358233447214680750459633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 133810977929619574333946177 100358233447214680750459633)
              ·
                refine ⟨75268675085411010562844725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 100358233447214680750459633 75268675085411010562844725)
                ·
                  refine ⟨7056438289257282240266693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 75268675085411010562844725 7056438289257282240266693)
                  ·
                    refine ⟨1323082179235740420050005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7056438289257282240266693 1323082179235740420050005)
                    ·
                      rfl

theorem cell23_7730080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 2, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 2, 2, 5, 4].length) (baseStart_7730080 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7730080 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7730080 prefixEnd_7730080 := by exact prefixLift 7730080
  have htrace : WordTrace (prefixWord ++ tailWord_7730080) baseStart_7730080 baseEnd_7730080 := by
    simpa [prefixWord, tailWord_7730080, baseEnd_7730080] using wordTrace_append hprefix tailTrace_7730080
  have hstable : (prefixWord ++ tailWord_7730080).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7730080).length < 2 ^ (prefixWord ++ tailWord_7730080).sum := by decide
  have hdescent : baseEnd_7730080 < baseStart_7730080 := by decide
  rcases family_descends (prefixWord ++ tailWord_7730080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7730083 : List Nat := [1, 1, 1, 4, 1, 2, 2, 1, 1, 3, 6]
def baseStart_7730083 : Nat := 118140960795 + 7730083 * 2 ^ 59
def prefixEnd_7730083 : Nat := 4983230072969 + 3 ^ 40 * 7730083 * 2
def baseEnd_7730083 : Nat := 3969248078149184748412501

theorem tailTrace_7730083 : CollatzResearch.WordTrace tailWord_7730083 prefixEnd_7730083 3969248078149184748412501 := by
  unfold tailWord_7730083
  simp only [CollatzResearch.WordTrace]
  refine ⟨281939289254236958915570903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187959526169491305943713935 281939289254236958915570903)
  ·
    refine ⟨422908933881355438373356355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 281939289254236958915570903 422908933881355438373356355)
    ·
      refine ⟨634363400822033157560034533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 422908933881355438373356355 634363400822033157560034533)
      ·
        refine ⟨118943137654131217042506475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 634363400822033157560034533 118943137654131217042506475)
        ·
          refine ⟨178414706481196825563759713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 118943137654131217042506475 178414706481196825563759713)
          ·
            refine ⟨133811029860897619172819785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 178414706481196825563759713 133811029860897619172819785)
            ·
              refine ⟨100358272395673214379614839, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 133811029860897619172819785 100358272395673214379614839)
              ·
                refine ⟨150537408593509821569422259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 100358272395673214379614839 150537408593509821569422259)
                ·
                  refine ⟨225806112890264732354133389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 150537408593509821569422259 225806112890264732354133389)
                  ·
                    refine ⟨84677292333849274632800021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 225806112890264732354133389 84677292333849274632800021)
                    ·
                      refine ⟨3969248078149184748412501, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 84677292333849274632800021 3969248078149184748412501)
                      ·
                        rfl

theorem cell23_7730083_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 2, 1, 1, 3, 6].length) (baseStart_7730083 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7730083 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7730083 prefixEnd_7730083 := by exact prefixLift 7730083
  have htrace : WordTrace (prefixWord ++ tailWord_7730083) baseStart_7730083 baseEnd_7730083 := by
    simpa [prefixWord, tailWord_7730083, baseEnd_7730083] using wordTrace_append hprefix tailTrace_7730083
  have hstable : (prefixWord ++ tailWord_7730083).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7730083).length < 2 ^ (prefixWord ++ tailWord_7730083).sum := by decide
  have hdescent : baseEnd_7730083 < baseStart_7730083 := by decide
  rcases family_descends (prefixWord ++ tailWord_7730083) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7730177 : List Nat := [1, 2, 4, 1, 2, 2, 2, 1, 3, 1, 4]
def baseStart_7730177 : Nat := 118140960795 + 7730177 * 2 ^ 59
def prefixEnd_7730177 : Nat := 4983230072969 + 3 ^ 40 * 7730177 * 2
def baseEnd_7730177 : Nat := 3969296345330707380637069

theorem tailTrace_7730177 : CollatzResearch.WordTrace tailWord_7730177 prefixEnd_7730177 3969296345330707380637069 := by
  unfold tailWord_7730177
  simp only [CollatzResearch.WordTrace]
  refine ⟨281942717715896412969492785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187961811810597608646328523 281942717715896412969492785)
  ·
    refine ⟨211457038286922309727119589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 281942717715896412969492785 211457038286922309727119589)
    ·
      refine ⟨39648194678797933073834923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 211457038286922309727119589 39648194678797933073834923)
      ·
        refine ⟨59472292018196899610752385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39648194678797933073834923 59472292018196899610752385)
        ·
          refine ⟨44604219013647674708064289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59472292018196899610752385 44604219013647674708064289)
          ·
            refine ⟨33453164260235756031048217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44604219013647674708064289 33453164260235756031048217)
            ·
              refine ⟨25089873195176817023286163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33453164260235756031048217 25089873195176817023286163)
              ·
                refine ⟨37634809792765225534929245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25089873195176817023286163 37634809792765225534929245)
                ·
                  refine ⟨14113053672286959575598467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37634809792765225534929245 14113053672286959575598467)
                  ·
                    refine ⟨21169580508430439363397701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14113053672286959575598467 21169580508430439363397701)
                    ·
                      refine ⟨3969296345330707380637069, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21169580508430439363397701 3969296345330707380637069)
                      ·
                        rfl

theorem cell23_7730177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 2, 1, 3, 1, 4].length) (baseStart_7730177 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7730177 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7730177 prefixEnd_7730177 := by exact prefixLift 7730177
  have htrace : WordTrace (prefixWord ++ tailWord_7730177) baseStart_7730177 baseEnd_7730177 := by
    simpa [prefixWord, tailWord_7730177, baseEnd_7730177] using wordTrace_append hprefix tailTrace_7730177
  have hstable : (prefixWord ++ tailWord_7730177).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7730177).length < 2 ^ (prefixWord ++ tailWord_7730177).sum := by decide
  have hdescent : baseEnd_7730177 < baseStart_7730177 := by decide
  rcases family_descends (prefixWord ++ tailWord_7730177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7730200 : List Nat := [2, 1, 2, 3, 2, 3, 10]
def baseStart_7730200 : Nat := 118140960795 + 7730200 * 2 ^ 59
def prefixEnd_7730200 : Nat := 4983230072969 + 3 ^ 40 * 7730200 * 2
def baseEnd_7730200 : Nat := 49003804387478528279623

theorem tailTrace_7730200 : CollatzResearch.WordTrace tailWord_7730200 prefixEnd_7730200 49003804387478528279623 := by
  unfold tailWord_7730200
  simp only [CollatzResearch.WordTrace]
  refine ⟨140971778297406543948790027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 187962371063208725265053369 140971778297406543948790027)
  ·
    refine ⟨211457667446109815923185041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140971778297406543948790027 211457667446109815923185041)
    ·
      refine ⟨158593250584582361942388781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 211457667446109815923185041 158593250584582361942388781)
      ·
        refine ⟨59472468969218385728395793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 158593250584582361942388781 59472468969218385728395793)
        ·
          refine ⟨44604351726913789296296845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59472468969218385728395793 44604351726913789296296845)
          ·
            refine ⟨16726631897592670986111317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44604351726913789296296845 16726631897592670986111317)
            ·
              refine ⟨49003804387478528279623, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 16726631897592670986111317 49003804387478528279623)
              ·
                rfl

theorem cell23_7730200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 3, 10].length) (baseStart_7730200 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7730200 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7730200 prefixEnd_7730200 := by exact prefixLift 7730200
  have htrace : WordTrace (prefixWord ++ tailWord_7730200) baseStart_7730200 baseEnd_7730200 := by
    simpa [prefixWord, tailWord_7730200, baseEnd_7730200] using wordTrace_append hprefix tailTrace_7730200
  have hstable : (prefixWord ++ tailWord_7730200).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7730200).length < 2 ^ (prefixWord ++ tailWord_7730200).sum := by decide
  have hdescent : baseEnd_7730200 < baseStart_7730200 := by decide
  rcases family_descends (prefixWord ++ tailWord_7730200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7730204 : List Nat := [2, 2, 3, 1, 4, 1, 1, 1, 4, 4]
def baseStart_7730204 : Nat := 118140960795 + 7730204 * 2 ^ 59
def prefixEnd_7730204 : Nat := 4983230072969 + 3 ^ 40 * 7730204 * 2
def baseEnd_7730204 : Nat := 1323103403102792924999815

theorem tailTrace_7730204 : CollatzResearch.WordTrace tailWord_7730204 prefixEnd_7730204 1323103403102792924999815 := by
  unfold tailWord_7730204
  simp only [CollatzResearch.WordTrace]
  refine ⟨140971851243399298290362833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 187962468324532397720483777 140971851243399298290362833)
  ·
    refine ⟨105728888432549473717772125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 140971851243399298290362833 105728888432549473717772125)
    ·
      refine ⟨39648333162206052644164547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 105728888432549473717772125 39648333162206052644164547)
      ·
        refine ⟨59472499743309078966246821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39648333162206052644164547 59472499743309078966246821)
        ·
          refine ⟨11151093701870452306171279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 59472499743309078966246821 11151093701870452306171279)
          ·
            refine ⟨16726640552805678459256919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11151093701870452306171279 16726640552805678459256919)
            ·
              refine ⟨25089960829208517688885379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16726640552805678459256919 25089960829208517688885379)
              ·
                refine ⟨37634941243812776533328069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25089960829208517688885379 37634941243812776533328069)
                ·
                  refine ⟨7056551483214895599999013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 37634941243812776533328069 7056551483214895599999013)
                  ·
                    refine ⟨1323103403102792924999815, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7056551483214895599999013 1323103403102792924999815)
                    ·
                      rfl

theorem cell23_7730204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 4, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 4, 1, 1, 1, 4, 4].length) (baseStart_7730204 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7730204 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7730204 prefixEnd_7730204 := by exact prefixLift 7730204
  have htrace : WordTrace (prefixWord ++ tailWord_7730204) baseStart_7730204 baseEnd_7730204 := by
    simpa [prefixWord, tailWord_7730204, baseEnd_7730204] using wordTrace_append hprefix tailTrace_7730204
  have hstable : (prefixWord ++ tailWord_7730204).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7730204).length < 2 ^ (prefixWord ++ tailWord_7730204).sum := by decide
  have hdescent : baseEnd_7730204 < baseStart_7730204 := by decide
  rcases family_descends (prefixWord ++ tailWord_7730204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7730211 : List Nat := [1, 1, 1, 4, 3, 3, 2, 1, 3, 2, 2]
def baseStart_7730211 : Nat := 118140960795 + 7730211 * 2 ^ 59
def prefixEnd_7730211 : Nat := 4983230072969 + 3 ^ 40 * 7730211 * 2
def baseEnd_7730211 : Nat := 3969313803672960247611913

theorem tailTrace_7730211 : CollatzResearch.WordTrace tailWord_7730211 prefixEnd_7730211 3969313803672960247611913 := by
  unfold tailWord_7730211
  simp only [CollatzResearch.WordTrace]
  refine ⟨281943957797773236776230487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187962638531848824517486991 281943957797773236776230487)
  ·
    refine ⟨422915936696659855164345731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 281943957797773236776230487 422915936696659855164345731)
    ·
      refine ⟨634373905044989782746518597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 422915936696659855164345731 634373905044989782746518597)
      ·
        refine ⟨118945107195935584264972237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 634373905044989782746518597 118945107195935584264972237)
        ·
          refine ⟨44604415198475844099364589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 118945107195935584264972237 44604415198475844099364589)
          ·
            refine ⟨16726655699428441537261721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44604415198475844099364589 16726655699428441537261721)
            ·
              refine ⟨12544991774571331152946291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16726655699428441537261721 12544991774571331152946291)
              ·
                refine ⟨18817487661856996729419437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12544991774571331152946291 18817487661856996729419437)
                ·
                  refine ⟨7056557873196373773532289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18817487661856996729419437 7056557873196373773532289)
                  ·
                    refine ⟨5292418404897280330149217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7056557873196373773532289 5292418404897280330149217)
                    ·
                      refine ⟨3969313803672960247611913, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5292418404897280330149217 3969313803672960247611913)
                      ·
                        rfl

theorem cell23_7730211_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 3, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 3, 2, 1, 3, 2, 2].length) (baseStart_7730211 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7730211 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7730211 prefixEnd_7730211 := by exact prefixLift 7730211
  have htrace : WordTrace (prefixWord ++ tailWord_7730211) baseStart_7730211 baseEnd_7730211 := by
    simpa [prefixWord, tailWord_7730211, baseEnd_7730211] using wordTrace_append hprefix tailTrace_7730211
  have hstable : (prefixWord ++ tailWord_7730211).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7730211).length < 2 ^ (prefixWord ++ tailWord_7730211).sum := by decide
  have hdescent : baseEnd_7730211 < baseStart_7730211 := by decide
  rcases family_descends (prefixWord ++ tailWord_7730211) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7730228 : List Nat := [2, 5, 1, 2, 1, 1, 2, 2, 3, 2, 2]
def baseStart_7730228 : Nat := 118140960795 + 7730228 * 2 ^ 59
def prefixEnd_7730228 : Nat := 4983230072969 + 3 ^ 40 * 7730228 * 2
def baseEnd_7730228 : Nat := 3969322532844086681099335

theorem tailTrace_7730228 : CollatzResearch.WordTrace tailWord_7730228 prefixEnd_7730228 3969322532844086681099335 := by
  unfold tailWord_7730228
  simp only [CollatzResearch.WordTrace]
  refine ⟨140972288919355824339799669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 187963051892474432453066225 140972288919355824339799669)
  ·
    refine ⟨13216152086189608531856219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 140972288919355824339799669 13216152086189608531856219)
    ·
      refine ⟨19824228129284412797784329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13216152086189608531856219 19824228129284412797784329)
      ·
        refine ⟨14868171096963309598338247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19824228129284412797784329 14868171096963309598338247)
        ·
          refine ⟨22302256645444964397507371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14868171096963309598338247 22302256645444964397507371)
          ·
            refine ⟨33453384968167446596261057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22302256645444964397507371 33453384968167446596261057)
            ·
              refine ⟨25090038726125584947195793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33453384968167446596261057 25090038726125584947195793)
              ·
                refine ⟨18817529044594188710396845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25090038726125584947195793 18817529044594188710396845)
                ·
                  refine ⟨7056573391722820766398817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18817529044594188710396845 7056573391722820766398817)
                  ·
                    refine ⟨5292430043792115574799113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7056573391722820766398817 5292430043792115574799113)
                    ·
                      refine ⟨3969322532844086681099335, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5292430043792115574799113 3969322532844086681099335)
                      ·
                        rfl

theorem cell23_7730228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 2, 2, 3, 2, 2].length) (baseStart_7730228 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7730228 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7730228 prefixEnd_7730228 := by exact prefixLift 7730228
  have htrace : WordTrace (prefixWord ++ tailWord_7730228) baseStart_7730228 baseEnd_7730228 := by
    simpa [prefixWord, tailWord_7730228, baseEnd_7730228] using wordTrace_append hprefix tailTrace_7730228
  have hstable : (prefixWord ++ tailWord_7730228).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7730228).length < 2 ^ (prefixWord ++ tailWord_7730228).sum := by decide
  have hdescent : baseEnd_7730228 < baseStart_7730228 := by decide
  rcases family_descends (prefixWord ++ tailWord_7730228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7730240 : List Nat := [2, 1, 1, 2, 2, 3, 1, 1, 1, 4, 5]
def baseStart_7730240 : Nat := 118140960795 + 7730240 * 2 ^ 59
def prefixEnd_7730240 : Nat := 4983230072969 + 3 ^ 40 * 7730240 * 2
def baseEnd_7730240 : Nat := 3969328694611940634149279

theorem tailTrace_7730240 : CollatzResearch.WordTrace tailWord_7730240 prefixEnd_7730240 3969328694611940634149279 := by
  unfold tailWord_7730240
  simp only [CollatzResearch.WordTrace]
  refine ⟨140972507757334087364518087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 187963343676445449819357449 140972507757334087364518087)
  ·
    refine ⟨211458761636001131046777131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140972507757334087364518087 211458761636001131046777131)
    ·
      refine ⟨317188142454001696570165697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 211458761636001131046777131 317188142454001696570165697)
      ·
        refine ⟨237891106840501272427624273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 317188142454001696570165697 237891106840501272427624273)
        ·
          refine ⟨178418330130375954320718205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 237891106840501272427624273 178418330130375954320718205)
          ·
            refine ⟨66906873798890982870269327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 178418330130375954320718205 66906873798890982870269327)
            ·
              refine ⟨100360310698336474305403991, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66906873798890982870269327 100360310698336474305403991)
              ·
                refine ⟨150540466047504711458105987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 100360310698336474305403991 150540466047504711458105987)
                ·
                  refine ⟨225810699071257067187158981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 150540466047504711458105987 225810699071257067187158981)
                  ·
                    refine ⟨42339506075860700097592309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 225810699071257067187158981 42339506075860700097592309)
                    ·
                      refine ⟨3969328694611940634149279, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42339506075860700097592309 3969328694611940634149279)
                      ·
                        rfl

theorem cell23_7730240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 1, 1, 1, 4, 5].length) (baseStart_7730240 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7730240 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7730240 prefixEnd_7730240 := by exact prefixLift 7730240
  have htrace : WordTrace (prefixWord ++ tailWord_7730240) baseStart_7730240 baseEnd_7730240 := by
    simpa [prefixWord, tailWord_7730240, baseEnd_7730240] using wordTrace_append hprefix tailTrace_7730240
  have hstable : (prefixWord ++ tailWord_7730240).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7730240).length < 2 ^ (prefixWord ++ tailWord_7730240).sum := by decide
  have hdescent : baseEnd_7730240 < baseStart_7730240 := by decide
  rcases family_descends (prefixWord ++ tailWord_7730240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7730262 : List Nat := [5, 2, 2, 1, 2, 2, 1, 1, 3, 2, 2]
def baseStart_7730262 : Nat := 118140960795 + 7730262 * 2 ^ 59
def prefixEnd_7730262 : Nat := 4983230072969 + 3 ^ 40 * 7730262 * 2
def baseEnd_7730262 : Nat := 3969339991186339548074179

theorem tailTrace_7730262 : CollatzResearch.WordTrace tailWord_7730262 prefixEnd_7730262 3969339991186339548074179 := by
  unfold tailWord_7730262
  simp only [CollatzResearch.WordTrace]
  refine ⟨17621613620036779530396065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 187963878613725648324224693 17621613620036779530396065)
  ·
    refine ⟨13216210215027584647797049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17621613620036779530396065 13216210215027584647797049)
    ·
      refine ⟨9912157661270688485847787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13216210215027584647797049 9912157661270688485847787)
      ·
        refine ⟨14868236491906032728771681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9912157661270688485847787 14868236491906032728771681)
        ·
          refine ⟨11151177368929524546578761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14868236491906032728771681 11151177368929524546578761)
          ·
            refine ⟨8363383026697143409934071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11151177368929524546578761 8363383026697143409934071)
            ·
              refine ⟨12545074540045715114901107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8363383026697143409934071 12545074540045715114901107)
              ·
                refine ⟨18817611810068572672351661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12545074540045715114901107 18817611810068572672351661)
                ·
                  refine ⟨7056604428775714752131873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18817611810068572672351661 7056604428775714752131873)
                  ·
                    refine ⟨5292453321581786064098905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7056604428775714752131873 5292453321581786064098905)
                    ·
                      refine ⟨3969339991186339548074179, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5292453321581786064098905 3969339991186339548074179)
                      ·
                        rfl

theorem cell23_7730262_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 2, 2, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 2, 2, 1, 1, 3, 2, 2].length) (baseStart_7730262 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7730262 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7730262 prefixEnd_7730262 := by exact prefixLift 7730262
  have htrace : WordTrace (prefixWord ++ tailWord_7730262) baseStart_7730262 baseEnd_7730262 := by
    simpa [prefixWord, tailWord_7730262, baseEnd_7730262] using wordTrace_append hprefix tailTrace_7730262
  have hstable : (prefixWord ++ tailWord_7730262).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7730262).length < 2 ^ (prefixWord ++ tailWord_7730262).sum := by decide
  have hdescent : baseEnd_7730262 < baseStart_7730262 := by decide
  rcases family_descends (prefixWord ++ tailWord_7730262) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7730284 : List Nat := [2, 2, 1, 1, 3, 2, 2, 3, 1, 4, 2]
def baseStart_7730284 : Nat := 118140960795 + 7730284 * 2 ^ 59
def prefixEnd_7730284 : Nat := 4983230072969 + 3 ^ 40 * 7730284 * 2
def baseEnd_7730284 : Nat := 3969351287760738461999077

theorem tailTrace_7730284 : CollatzResearch.WordTrace tailWord_7730284 prefixEnd_7730284 3969351287760738461999077 := by
  unfold tailWord_7730284
  simp only [CollatzResearch.WordTrace]
  refine ⟨140973310163254385121818953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 187964413551005846829091937 140973310163254385121818953)
  ·
    refine ⟨105729982622440788841364215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 140973310163254385121818953 105729982622440788841364215)
    ·
      refine ⟨158594973933661183262046323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105729982622440788841364215 158594973933661183262046323)
      ·
        refine ⟨237892460900491774893069485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 158594973933661183262046323 237892460900491774893069485)
        ·
          refine ⟨89209672837684415584901057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 237892460900491774893069485 89209672837684415584901057)
          ·
            refine ⟨66907254628263311688675793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 89209672837684415584901057 66907254628263311688675793)
            ·
              refine ⟨50180440971197483766506845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66907254628263311688675793 50180440971197483766506845)
              ·
                refine ⟨18817665364199056412440067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 50180440971197483766506845 18817665364199056412440067)
                ·
                  refine ⟨28226498046298584618660101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18817665364199056412440067 28226498046298584618660101)
                  ·
                    refine ⟨5292468383680984615998769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28226498046298584618660101 5292468383680984615998769)
                    ·
                      refine ⟨3969351287760738461999077, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5292468383680984615998769 3969351287760738461999077)
                      ·
                        rfl

theorem cell23_7730284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 4, 2].length) (baseStart_7730284 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7730284 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7730284 prefixEnd_7730284 := by exact prefixLift 7730284
  have htrace : WordTrace (prefixWord ++ tailWord_7730284) baseStart_7730284 baseEnd_7730284 := by
    simpa [prefixWord, tailWord_7730284, baseEnd_7730284] using wordTrace_append hprefix tailTrace_7730284
  have hstable : (prefixWord ++ tailWord_7730284).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7730284).length < 2 ^ (prefixWord ++ tailWord_7730284).sum := by decide
  have hdescent : baseEnd_7730284 < baseStart_7730284 := by decide
  rcases family_descends (prefixWord ++ tailWord_7730284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7730318 : List Nat := [4, 1, 1, 3, 2, 1, 1, 4, 2, 2, 2]
def baseStart_7730318 : Nat := 118140960795 + 7730318 * 2 ^ 59
def prefixEnd_7730318 : Nat := 4983230072969 + 3 ^ 40 * 7730318 * 2
def baseEnd_7730318 : Nat := 3969368746102991328973921

theorem tailTrace_7730318 : CollatzResearch.WordTrace tailWord_7730318 prefixEnd_7730318 3969368746102991328973921 := by
  unfold tailWord_7730318
  simp only [CollatzResearch.WordTrace]
  refine ⟨35243482551048199256296951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 187965240272257062700250405 35243482551048199256296951)
  ·
    refine ⟨52865223826572298884445427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35243482551048199256296951 52865223826572298884445427)
    ·
      refine ⟨79297835739858448326668141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52865223826572298884445427 79297835739858448326668141)
      ·
        refine ⟨29736688402446918122500553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 79297835739858448326668141 29736688402446918122500553)
        ·
          refine ⟨22302516301835188591875415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29736688402446918122500553 22302516301835188591875415)
          ·
            refine ⟨33453774452752782887813123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22302516301835188591875415 33453774452752782887813123)
            ·
              refine ⟨50180661679129174331719685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33453774452752782887813123 50180661679129174331719685)
              ·
                refine ⟨9408874064836720187197441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 50180661679129174331719685 9408874064836720187197441)
                ·
                  refine ⟨7056655548627540140398081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9408874064836720187197441 7056655548627540140398081)
                  ·
                    refine ⟨5292491661470655105298561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7056655548627540140398081 5292491661470655105298561)
                    ·
                      refine ⟨3969368746102991328973921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5292491661470655105298561 3969368746102991328973921)
                      ·
                        rfl

theorem cell23_7730318_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 1, 4, 2, 2, 2].length) (baseStart_7730318 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7730318 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7730318 prefixEnd_7730318 := by exact prefixLift 7730318
  have htrace : WordTrace (prefixWord ++ tailWord_7730318) baseStart_7730318 baseEnd_7730318 := by
    simpa [prefixWord, tailWord_7730318, baseEnd_7730318] using wordTrace_append hprefix tailTrace_7730318
  have hstable : (prefixWord ++ tailWord_7730318).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7730318).length < 2 ^ (prefixWord ++ tailWord_7730318).sum := by decide
  have hdescent : baseEnd_7730318 < baseStart_7730318 := by decide
  rcases family_descends (prefixWord ++ tailWord_7730318) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7730337 : List Nat := [1, 2, 3, 3, 1, 1, 2, 2, 1, 7]
def baseStart_7730337 : Nat := 118140960795 + 7730337 * 2 ^ 59
def prefixEnd_7730337 : Nat := 4983230072969 + 3 ^ 40 * 7730337 * 2
def baseEnd_7730337 : Nat := 1323126167411808918212111

theorem tailTrace_7730337 : CollatzResearch.WordTrace tailWord_7730337 prefixEnd_7730337 1323126167411808918212111 := by
  unfold tailWord_7730337
  simp only [CollatzResearch.WordTrace]
  refine ⟨281948553395316760295317265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187965702263544506863544843 281948553395316760295317265)
  ·
    refine ⟨211461415046487570221487949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 281948553395316760295317265 211461415046487570221487949)
    ·
      refine ⟨79298030642432838833057981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 211461415046487570221487949 79298030642432838833057981)
      ·
        refine ⟨29736761490912314562396743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 79298030642432838833057981 29736761490912314562396743)
        ·
          refine ⟨44605142236368471843595115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29736761490912314562396743 44605142236368471843595115)
          ·
            refine ⟨66907713354552707765392673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44605142236368471843595115 66907713354552707765392673)
            ·
              refine ⟨50180785015914530824044505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66907713354552707765392673 50180785015914530824044505)
              ·
                refine ⟨37635588761935898118033379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50180785015914530824044505 37635588761935898118033379)
                ·
                  refine ⟨56453383142903847177050069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37635588761935898118033379 56453383142903847177050069)
                  ·
                    refine ⟨1323126167411808918212111, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 56453383142903847177050069 1323126167411808918212111)
                    ·
                      rfl

theorem cell23_7730337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 2, 2, 1, 7].length) (baseStart_7730337 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7730337 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7730337 prefixEnd_7730337 := by exact prefixLift 7730337
  have htrace : WordTrace (prefixWord ++ tailWord_7730337) baseStart_7730337 baseEnd_7730337 := by
    simpa [prefixWord, tailWord_7730337, baseEnd_7730337] using wordTrace_append hprefix tailTrace_7730337
  have hstable : (prefixWord ++ tailWord_7730337).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7730337).length < 2 ^ (prefixWord ++ tailWord_7730337).sum := by decide
  have hdescent : baseEnd_7730337 < baseStart_7730337 := by decide
  rcases family_descends (prefixWord ++ tailWord_7730337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7730354 : List Nat := [3, 2, 1, 1, 1, 4, 3, 1, 2, 5]
def baseStart_7730354 : Nat := 118140960795 + 7730354 * 2 ^ 59
def prefixEnd_7730354 : Nat := 4983230072969 + 3 ^ 40 * 7730354 * 2
def baseEnd_7730354 : Nat := 1323129077135517729374585

theorem tailTrace_7730354 : CollatzResearch.WordTrace tailWord_7730354 prefixEnd_7730354 1323129077135517729374585 := by
  unfold tailWord_7730354
  simp only [CollatzResearch.WordTrace]
  refine ⟨70487293359063793049671529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 187966115624170114799124077 70487293359063793049671529)
  ·
    refine ⟨52865470019297844787253647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70487293359063793049671529 52865470019297844787253647)
    ·
      refine ⟨79298205028946767180880471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52865470019297844787253647 79298205028946767180880471)
      ·
        refine ⟨118947307543420150771320707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79298205028946767180880471 118947307543420150771320707)
        ·
          refine ⟨178420961315130226156981061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 118947307543420150771320707 178420961315130226156981061)
          ·
            refine ⟨33453930246586917404433949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 178420961315130226156981061 33453930246586917404433949)
            ·
              refine ⟨12545223842470094026662731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33453930246586917404433949 12545223842470094026662731)
              ·
                refine ⟨18817835763705141039994097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12545223842470094026662731 18817835763705141039994097)
                ·
                  refine ⟨14113376822778855779995573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18817835763705141039994097 14113376822778855779995573)
                  ·
                    refine ⟨1323129077135517729374585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14113376822778855779995573 1323129077135517729374585)
                    ·
                      rfl

theorem cell23_7730354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 3, 1, 2, 5].length) (baseStart_7730354 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7730354 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7730354 prefixEnd_7730354 := by exact prefixLift 7730354
  have htrace : WordTrace (prefixWord ++ tailWord_7730354) baseStart_7730354 baseEnd_7730354 := by
    simpa [prefixWord, tailWord_7730354, baseEnd_7730354] using wordTrace_append hprefix tailTrace_7730354
  have hstable : (prefixWord ++ tailWord_7730354).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7730354).length < 2 ^ (prefixWord ++ tailWord_7730354).sum := by decide
  have hdescent : baseEnd_7730354 < baseStart_7730354 := by decide
  rcases family_descends (prefixWord ++ tailWord_7730354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7730447 : List Nat := [1, 1, 2, 1, 1, 1, 3, 1, 1, 7, 4]
def baseStart_7730447 : Nat := 118140960795 + 7730447 * 2 ^ 59
def prefixEnd_7730447 : Nat := 4983230072969 + 3 ^ 40 * 7730447 * 2
def baseEnd_7730447 : Nat := 3969434985107421324260827

theorem tailTrace_7730447 : CollatzResearch.WordTrace tailWord_7730447 prefixEnd_7730447 3969434985107421324260827 := by
  unfold tailWord_7730447
  simp only [CollatzResearch.WordTrace]
  refine ⟨281952565424918249081821595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187968376949945499387881063 281952565424918249081821595)
  ·
    refine ⟨422928848137377373622732393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 281952565424918249081821595 422928848137377373622732393)
    ·
      refine ⟨317196636103033030217049295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 422928848137377373622732393 317196636103033030217049295)
      ·
        refine ⟨475794954154549545325573943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 317196636103033030217049295 475794954154549545325573943)
        ·
          refine ⟨713692431231824317988360915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 475794954154549545325573943 713692431231824317988360915)
          ·
            refine ⟨1070538646847736476982541373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 713692431231824317988360915 1070538646847736476982541373)
            ·
              refine ⟨401451992567901178868453015, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1070538646847736476982541373 401451992567901178868453015)
              ·
                refine ⟨602177988851851768302679523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 401451992567901178868453015 602177988851851768302679523)
                ·
                  refine ⟨903266983277777652454019285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 602177988851851768302679523 903266983277777652454019285)
                  ·
                    refine ⟨21170319920572913729391077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 903266983277777652454019285 21170319920572913729391077)
                    ·
                      refine ⟨3969434985107421324260827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21170319920572913729391077 3969434985107421324260827)
                      ·
                        rfl

theorem cell23_7730447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 1, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 1, 1, 7, 4].length) (baseStart_7730447 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7730447 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7730447 prefixEnd_7730447 := by exact prefixLift 7730447
  have htrace : WordTrace (prefixWord ++ tailWord_7730447) baseStart_7730447 baseEnd_7730447 := by
    simpa [prefixWord, tailWord_7730447, baseEnd_7730447] using wordTrace_append hprefix tailTrace_7730447
  have hstable : (prefixWord ++ tailWord_7730447).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7730447).length < 2 ^ (prefixWord ++ tailWord_7730447).sum := by decide
  have hdescent : baseEnd_7730447 < baseStart_7730447 := by decide
  rcases family_descends (prefixWord ++ tailWord_7730447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7730457 : List Nat := [1, 2, 1, 2, 1, 1, 1, 1, 7, 6]
def baseStart_7730457 : Nat := 118140960795 + 7730457 * 2 ^ 59
def prefixEnd_7730457 : Nat := 4983230072969 + 3 ^ 40 * 7730457 * 2
def baseEnd_7730457 : Nat := 1323146706637988761711927

theorem tailTrace_7730457 : CollatzResearch.WordTrace tailWord_7730457 prefixEnd_7730457 1323146706637988761711927 := by
  unfold tailWord_7730457
  simp only [CollatzResearch.WordTrace]
  refine ⟨281952930154882020789685625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187968620103254680526457083 281952930154882020789685625)
  ·
    refine ⟨211464697616161515592264219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 281952930154882020789685625 211464697616161515592264219)
    ·
      refine ⟨317197046424242273388396329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 211464697616161515592264219 317197046424242273388396329)
      ·
        refine ⟨237897784818181705041297247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 317197046424242273388396329 237897784818181705041297247)
        ·
          refine ⟨356846677227272557561945871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 237897784818181705041297247 356846677227272557561945871)
          ·
            refine ⟨535270015840908836342918807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 356846677227272557561945871 535270015840908836342918807)
            ·
              refine ⟨802905023761363254514378211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 535270015840908836342918807 802905023761363254514378211)
              ·
                refine ⟨1204357535642044881771567317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 802905023761363254514378211 1204357535642044881771567317)
                ·
                  refine ⟨28227129741610426916521109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1204357535642044881771567317 28227129741610426916521109)
                  ·
                    refine ⟨1323146706637988761711927, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28227129741610426916521109 1323146706637988761711927)
                    ·
                      rfl

theorem cell23_7730457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 1, 7, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 1, 7, 6].length) (baseStart_7730457 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7730457 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7730457 prefixEnd_7730457 := by exact prefixLift 7730457
  have htrace : WordTrace (prefixWord ++ tailWord_7730457) baseStart_7730457 baseEnd_7730457 := by
    simpa [prefixWord, tailWord_7730457, baseEnd_7730457] using wordTrace_append hprefix tailTrace_7730457
  have hstable : (prefixWord ++ tailWord_7730457).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7730457).length < 2 ^ (prefixWord ++ tailWord_7730457).sum := by decide
  have hdescent : baseEnd_7730457 < baseStart_7730457 := by decide
  rcases family_descends (prefixWord ++ tailWord_7730457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7730461 : List Nat := [1, 4, 2, 3, 1, 2, 1, 1, 3, 5]
def baseStart_7730461 : Nat := 118140960795 + 7730461 * 2 ^ 59
def prefixEnd_7730461 : Nat := 4983230072969 + 3 ^ 40 * 7730461 * 2
def baseEnd_7730461 : Nat := 1323147391278861423161921

theorem tailTrace_7730461 : CollatzResearch.WordTrace tailWord_7730461 prefixEnd_7730461 1323147391278861423161921 := by
  unfold tailWord_7730461
  simp only [CollatzResearch.WordTrace]
  refine ⟨281953076046867529472831237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187968717364578352981887491 281953076046867529472831237)
  ·
    refine ⟨52866201758787661776155857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 281953076046867529472831237 52866201758787661776155857)
    ·
      refine ⟨39649651319090746332116893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52866201758787661776155857 39649651319090746332116893)
      ·
        refine ⟨14868619244659029874543835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39649651319090746332116893 14868619244659029874543835)
        ·
          refine ⟨22302928866988544811815753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14868619244659029874543835 22302928866988544811815753)
          ·
            refine ⟨16727196650241408608861815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22302928866988544811815753 16727196650241408608861815)
            ·
              refine ⟨25090794975362112913292723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16727196650241408608861815 25090794975362112913292723)
              ·
                refine ⟨37636192463043169369939085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25090794975362112913292723 37636192463043169369939085)
                ·
                  refine ⟨14113572173641188513727157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37636192463043169369939085 14113572173641188513727157)
                  ·
                    refine ⟨1323147391278861423161921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14113572173641188513727157 1323147391278861423161921)
                    ·
                      rfl

theorem cell23_7730461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 2, 1, 1, 3, 5].length) (baseStart_7730461 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7730461 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7730461 prefixEnd_7730461 := by exact prefixLift 7730461
  have htrace : WordTrace (prefixWord ++ tailWord_7730461) baseStart_7730461 baseEnd_7730461 := by
    simpa [prefixWord, tailWord_7730461, baseEnd_7730461] using wordTrace_append hprefix tailTrace_7730461
  have hstable : (prefixWord ++ tailWord_7730461).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7730461).length < 2 ^ (prefixWord ++ tailWord_7730461).sum := by decide
  have hdescent : baseEnd_7730461 < baseStart_7730461 := by decide
  rcases family_descends (prefixWord ++ tailWord_7730461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7730468 : List Nat := [2, 3, 1, 3, 1, 1, 4, 1, 2, 3, 2]
def baseStart_7730468 : Nat := 118140960795 + 7730468 * 2 ^ 59
def prefixEnd_7730468 : Nat := 4983230072969 + 3 ^ 40 * 7730468 * 2
def baseEnd_7730468 : Nat := 3969445768201165742098231

theorem tailTrace_7730468 : CollatzResearch.WordTrace tailWord_7730468 prefixEnd_7730468 3969445768201165742098231 := by
  unfold tailWord_7730468
  simp only [CollatzResearch.WordTrace]
  refine ⟨140976665678921084834168029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 187968887571894779778890705 140976665678921084834168029)
  ·
    refine ⟨52866249629595406812813011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 140976665678921084834168029 52866249629595406812813011)
    ·
      refine ⟨79299374444393110219219517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52866249629595406812813011 79299374444393110219219517)
      ·
        refine ⟨29737265416647416332207319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 79299374444393110219219517 29737265416647416332207319)
        ·
          refine ⟨44605898124971124498310979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29737265416647416332207319 44605898124971124498310979)
          ·
            refine ⟨66908847187456686747466469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44605898124971124498310979 66908847187456686747466469)
            ·
              refine ⟨12545408847648128765149963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 66908847187456686747466469 12545408847648128765149963)
              ·
                refine ⟨18818113271472193147724945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12545408847648128765149963 18818113271472193147724945)
                ·
                  refine ⟨14113584953604144860793709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18818113271472193147724945 14113584953604144860793709)
                  ·
                    refine ⟨5292594357601554322797641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14113584953604144860793709 5292594357601554322797641)
                    ·
                      refine ⟨3969445768201165742098231, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5292594357601554322797641 3969445768201165742098231)
                      ·
                        rfl

theorem cell23_7730468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 4, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 4, 1, 2, 3, 2].length) (baseStart_7730468 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7730468 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7730468 prefixEnd_7730468 := by exact prefixLift 7730468
  have htrace : WordTrace (prefixWord ++ tailWord_7730468) baseStart_7730468 baseEnd_7730468 := by
    simpa [prefixWord, tailWord_7730468, baseEnd_7730468] using wordTrace_append hprefix tailTrace_7730468
  have hstable : (prefixWord ++ tailWord_7730468).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7730468).length < 2 ^ (prefixWord ++ tailWord_7730468).sum := by decide
  have hdescent : baseEnd_7730468 < baseStart_7730468 := by decide
  rcases family_descends (prefixWord ++ tailWord_7730468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7730486 : List Nat := [5, 1, 2, 3, 2, 1, 2, 2, 1, 4]
def baseStart_7730486 : Nat := 118140960795 + 7730486 * 2 ^ 59
def prefixEnd_7730486 : Nat := 4983230072969 + 3 ^ 40 * 7730486 * 2
def baseEnd_7730486 : Nat := 1323151670284315557224383

theorem tailTrace_7730486 : CollatzResearch.WordTrace tailWord_7730486 prefixEnd_7730486 1323151670284315557224383 := by
  unfold tailWord_7730486
  simp only [CollatzResearch.WordTrace]
  refine ⟨17622124241986059921405707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 187969325247851305828327541 17622124241986059921405707)
  ·
    refine ⟨26433186362979089882108561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17622124241986059921405707 26433186362979089882108561)
    ·
      refine ⟨19824889772234317411581421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26433186362979089882108561 19824889772234317411581421)
      ·
        refine ⟨7434333664587869029343033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19824889772234317411581421 7434333664587869029343033)
        ·
          refine ⟨5575750248440901772007275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7434333664587869029343033 5575750248440901772007275)
          ·
            refine ⟨8363625372661352658010913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5575750248440901772007275 8363625372661352658010913)
            ·
              refine ⟨6272719029496014493508185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8363625372661352658010913 6272719029496014493508185)
              ·
                refine ⟨4704539272122010870131139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6272719029496014493508185 4704539272122010870131139)
                ·
                  refine ⟨7056808908183016305196709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4704539272122010870131139 7056808908183016305196709)
                  ·
                    refine ⟨1323151670284315557224383, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7056808908183016305196709 1323151670284315557224383)
                    ·
                      rfl

theorem cell23_7730486_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 2, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 2, 1, 2, 2, 1, 4].length) (baseStart_7730486 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7730486 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7730486 prefixEnd_7730486 := by exact prefixLift 7730486
  have htrace : WordTrace (prefixWord ++ tailWord_7730486) baseStart_7730486 baseEnd_7730486 := by
    simpa [prefixWord, tailWord_7730486, baseEnd_7730486] using wordTrace_append hprefix tailTrace_7730486
  have hstable : (prefixWord ++ tailWord_7730486).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7730486).length < 2 ^ (prefixWord ++ tailWord_7730486).sum := by decide
  have hdescent : baseEnd_7730486 < baseStart_7730486 := by decide
  rcases family_descends (prefixWord ++ tailWord_7730486) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7730492 : List Nat := [2, 2, 2, 2, 1, 5, 2, 2, 1, 1, 3]
def baseStart_7730492 : Nat := 118140960795 + 7730492 * 2 ^ 59
def prefixEnd_7730492 : Nat := 4983230072969 + 3 ^ 40 * 7730492 * 2
def baseEnd_7730492 : Nat := 3969458091736873648198121

theorem tailTrace_7730492 : CollatzResearch.WordTrace tailWord_7730492 prefixEnd_7730492 3969458091736873648198121 := by
  unfold tailWord_7730492
  simp only [CollatzResearch.WordTrace]
  refine ⟨140977103354877610883604865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 187969471139836814511473153 140977103354877610883604865)
  ·
    refine ⟨105732827516158208162703649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 140977103354877610883604865 105732827516158208162703649)
    ·
      refine ⟨79299620637118656122027737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 105732827516158208162703649 79299620637118656122027737)
      ·
        refine ⟨59474715477838992091520803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79299620637118656122027737 59474715477838992091520803)
        ·
          refine ⟨89212073216758488137281205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59474715477838992091520803 89212073216758488137281205)
          ·
            refine ⟨8363631864071108262870113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 89212073216758488137281205 8363631864071108262870113)
            ·
              refine ⟨6272723898053331197152585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8363631864071108262870113 6272723898053331197152585)
              ·
                refine ⟨4704542923539998397864439, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6272723898053331197152585 4704542923539998397864439)
                ·
                  refine ⟨7056814385309997596796659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4704542923539998397864439 7056814385309997596796659)
                  ·
                    refine ⟨10585221577964996395194989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7056814385309997596796659 10585221577964996395194989)
                    ·
                      refine ⟨3969458091736873648198121, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10585221577964996395194989 3969458091736873648198121)
                      ·
                        rfl

theorem cell23_7730492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 5, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 5, 2, 2, 1, 1, 3].length) (baseStart_7730492 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7730492 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7730492 prefixEnd_7730492 := by exact prefixLift 7730492
  have htrace : WordTrace (prefixWord ++ tailWord_7730492) baseStart_7730492 baseEnd_7730492 := by
    simpa [prefixWord, tailWord_7730492, baseEnd_7730492] using wordTrace_append hprefix tailTrace_7730492
  have hstable : (prefixWord ++ tailWord_7730492).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7730492).length < 2 ^ (prefixWord ++ tailWord_7730492).sum := by decide
  have hdescent : baseEnd_7730492 < baseStart_7730492 := by decide
  rcases family_descends (prefixWord ++ tailWord_7730492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7730531 : List Nat := [1, 1, 1, 5, 2, 2, 2, 2, 1, 3, 3]
def baseStart_7730531 : Nat := 118140960795 + 7730531 * 2 ^ 59
def prefixEnd_7730531 : Nat := 4983230072969 + 3 ^ 40 * 7730531 * 2
def baseEnd_7730531 : Nat := 3969478117482398995610441

theorem tailTrace_7730531 : CollatzResearch.WordTrace tailWord_7730531 prefixEnd_7730531 3969478117482398995610441 := by
  unfold tailWord_7730531
  simp only [CollatzResearch.WordTrace]
  refine ⟨281955629156613931427879447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187970419437742620951919631 281955629156613931427879447)
  ·
    refine ⟨422933443734920897141819171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 281955629156613931427879447 422933443734920897141819171)
    ·
      refine ⟨634400165602381345712728757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 422933443734920897141819171 634400165602381345712728757)
      ·
        refine ⟨59475015525223251160568321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 634400165602381345712728757 59475015525223251160568321)
        ·
          refine ⟨44606261643917438370426241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59475015525223251160568321 44606261643917438370426241)
          ·
            refine ⟨33454696232938078777819681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44606261643917438370426241 33454696232938078777819681)
            ·
              refine ⟨25091022174703559083364761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33454696232938078777819681 25091022174703559083364761)
              ·
                refine ⟨18818266631027669312523571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25091022174703559083364761 18818266631027669312523571)
                ·
                  refine ⟨28227399946541503968785357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18818266631027669312523571 28227399946541503968785357)
                  ·
                    refine ⟨10585274979953063988294509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28227399946541503968785357 10585274979953063988294509)
                    ·
                      refine ⟨3969478117482398995610441, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10585274979953063988294509 3969478117482398995610441)
                      ·
                        rfl

theorem cell23_7730531_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 2, 2, 1, 3, 3].length) (baseStart_7730531 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7730531 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7730531 prefixEnd_7730531 := by exact prefixLift 7730531
  have htrace : WordTrace (prefixWord ++ tailWord_7730531) baseStart_7730531 baseEnd_7730531 := by
    simpa [prefixWord, tailWord_7730531, baseEnd_7730531] using wordTrace_append hprefix tailTrace_7730531
  have hstable : (prefixWord ++ tailWord_7730531).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7730531).length < 2 ^ (prefixWord ++ tailWord_7730531).sum := by decide
  have hdescent : baseEnd_7730531 < baseStart_7730531 := by decide
  rcases family_descends (prefixWord ++ tailWord_7730531) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7730532 : List Nat := [2, 3, 1, 1, 3, 3, 2, 3, 1, 2, 2]
def baseStart_7730532 : Nat := 118140960795 + 7730532 * 2 ^ 59
def prefixEnd_7730532 : Nat := 4983230072969 + 3 ^ 40 * 7730532 * 2
def baseEnd_7730532 : Nat := 3969478630963053491697937

theorem tailTrace_7730532 : CollatzResearch.WordTrace tailWord_7730532 prefixEnd_7730532 3969478630963053491697937 := by
  unfold tailWord_7730532
  simp only [CollatzResearch.WordTrace]
  refine ⟨140977832814805154299332925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 187970443753073539065777233 140977832814805154299332925)
  ·
    refine ⟨52866687305551932862249847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 140977832814805154299332925 52866687305551932862249847)
    ·
      refine ⟨79300030958327899293374771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52866687305551932862249847 79300030958327899293374771)
      ·
        refine ⟨118950046437491848940062157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79300030958327899293374771 118950046437491848940062157)
        ·
          refine ⟨44606267414059443352523309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 118950046437491848940062157 44606267414059443352523309)
          ·
            refine ⟨16727350280272291257196241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44606267414059443352523309 16727350280272291257196241)
            ·
              refine ⟨12545512710204218442897181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16727350280272291257196241 12545512710204218442897181)
              ·
                refine ⟨4704567266326581916086443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12545512710204218442897181 4704567266326581916086443)
                ·
                  refine ⟨7056850899489872874129665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4704567266326581916086443 7056850899489872874129665)
                  ·
                    refine ⟨5292638174617404655597249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7056850899489872874129665 5292638174617404655597249)
                    ·
                      refine ⟨3969478630963053491697937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5292638174617404655597249 3969478630963053491697937)
                      ·
                        rfl

theorem cell23_7730532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 3, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 3, 2, 3, 1, 2, 2].length) (baseStart_7730532 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7730532 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7730532 prefixEnd_7730532 := by exact prefixLift 7730532
  have htrace : WordTrace (prefixWord ++ tailWord_7730532) baseStart_7730532 baseEnd_7730532 := by
    simpa [prefixWord, tailWord_7730532, baseEnd_7730532] using wordTrace_append hprefix tailTrace_7730532
  have hstable : (prefixWord ++ tailWord_7730532).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7730532).length < 2 ^ (prefixWord ++ tailWord_7730532).sum := by decide
  have hdescent : baseEnd_7730532 < baseStart_7730532 := by decide
  rcases family_descends (prefixWord ++ tailWord_7730532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7730542 : List Nat := [4, 1, 2, 4, 1, 2, 1, 2, 2, 4]
def baseStart_7730542 : Nat := 118140960795 + 7730542 * 2 ^ 59
def prefixEnd_7730542 : Nat := 4983230072969 + 3 ^ 40 * 7730542 * 2
def baseEnd_7730542 : Nat := 1323161255256532817524297

theorem tailTrace_7730542 : CollatzResearch.WordTrace tailWord_7730542 prefixEnd_7730542 1323161255256532817524297 := by
  unfold tailWord_7730542
  simp only [CollatzResearch.WordTrace]
  refine ⟨35244503794946760038316235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 187970686906382720204353253 35244503794946760038316235)
  ·
    refine ⟨52866755692420140057474353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35244503794946760038316235 52866755692420140057474353)
    ·
      refine ⟨39650066769315105043105765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52866755692420140057474353 39650066769315105043105765)
      ·
        refine ⟨7434387519246582195582331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 39650066769315105043105765 7434387519246582195582331)
        ·
          refine ⟨11151581278869873293373497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7434387519246582195582331 11151581278869873293373497)
          ·
            refine ⟨8363685959152404970030123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11151581278869873293373497 8363685959152404970030123)
            ·
              refine ⟨12545528938728607455045185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8363685959152404970030123 12545528938728607455045185)
              ·
                refine ⟨9409146704046455591283889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12545528938728607455045185 9409146704046455591283889)
                ·
                  refine ⟨7056860028034841693462917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9409146704046455591283889 7056860028034841693462917)
                  ·
                    refine ⟨1323161255256532817524297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7056860028034841693462917 1323161255256532817524297)
                    ·
                      rfl

theorem cell23_7730542_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 1, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 1, 2, 1, 2, 2, 4].length) (baseStart_7730542 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7730542 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7730542 prefixEnd_7730542 := by exact prefixLift 7730542
  have htrace : WordTrace (prefixWord ++ tailWord_7730542) baseStart_7730542 baseEnd_7730542 := by
    simpa [prefixWord, tailWord_7730542, baseEnd_7730542] using wordTrace_append hprefix tailTrace_7730542
  have hstable : (prefixWord ++ tailWord_7730542).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7730542).length < 2 ^ (prefixWord ++ tailWord_7730542).sum := by decide
  have hdescent : baseEnd_7730542 < baseStart_7730542 := by decide
  rcases family_descends (prefixWord ++ tailWord_7730542) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7730591 : List Nat := [1, 1, 2, 5, 1, 3, 1, 1, 2, 1, 5]
def baseStart_7730591 : Nat := 118140960795 + 7730591 * 2 ^ 59
def prefixEnd_7730591 : Nat := 4983230072969 + 3 ^ 40 * 7730591 * 2
def baseEnd_7730591 : Nat := 3969508926321668760860165

theorem tailTrace_7730591 : CollatzResearch.WordTrace tailWord_7730591 prefixEnd_7730591 3969508926321668760860165 := by
  unfold tailWord_7730591
  simp only [CollatzResearch.WordTrace]
  refine ⟨281957817536396561675063627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187971878357597707783375751 281957817536396561675063627)
  ·
    refine ⟨422936726304594842512595441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 281957817536396561675063627 422936726304594842512595441)
    ·
      refine ⟨317202544728446131884446581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 422936726304594842512595441 317202544728446131884446581)
      ·
        refine ⟨29737738568291824864166867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 317202544728446131884446581 29737738568291824864166867)
        ·
          refine ⟨44606607852437737296250301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29737738568291824864166867 44606607852437737296250301)
          ·
            refine ⟨16727477944664151486093863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44606607852437737296250301 16727477944664151486093863)
            ·
              refine ⟨25091216916996227229140795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16727477944664151486093863 25091216916996227229140795)
              ·
                refine ⟨37636825375494340843711193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25091216916996227229140795 37636825375494340843711193)
                ·
                  refine ⟨28227619031620755632783395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37636825375494340843711193 28227619031620755632783395)
                  ·
                    refine ⟨42341428547431133449175093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28227619031620755632783395 42341428547431133449175093)
                    ·
                      refine ⟨3969508926321668760860165, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42341428547431133449175093 3969508926321668760860165)
                      ·
                        rfl

theorem cell23_7730591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 3, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 3, 1, 1, 2, 1, 5].length) (baseStart_7730591 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7730591 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7730591 prefixEnd_7730591 := by exact prefixLift 7730591
  have htrace : WordTrace (prefixWord ++ tailWord_7730591) baseStart_7730591 baseEnd_7730591 := by
    simpa [prefixWord, tailWord_7730591, baseEnd_7730591] using wordTrace_append hprefix tailTrace_7730591
  have hstable : (prefixWord ++ tailWord_7730591).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7730591).length < 2 ^ (prefixWord ++ tailWord_7730591).sum := by decide
  have hdescent : baseEnd_7730591 < baseStart_7730591 := by decide
  rcases family_descends (prefixWord ++ tailWord_7730591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7730611 : List Nat := [1, 1, 1, 2, 3, 1, 1, 8, 5]
def baseStart_7730611 : Nat := 118140960795 + 7730611 * 2 ^ 59
def prefixEnd_7730611 : Nat := 4983230072969 + 3 ^ 40 * 7730611 * 2
def baseEnd_7730611 : Nat := 441057688437195409178897

theorem tailTrace_7730611 : CollatzResearch.WordTrace tailWord_7730611 prefixEnd_7730611 441057688437195409178897 := by
  unfold tailWord_7730611
  simp only [CollatzResearch.WordTrace]
  refine ⟨281958546996324105090791687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187972364664216070060527791 281958546996324105090791687)
  ·
    refine ⟨422937820494486157636187531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 281958546996324105090791687 422937820494486157636187531)
    ·
      refine ⟨634406730741729236454281297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 422937820494486157636187531 634406730741729236454281297)
      ·
        refine ⟨475805048056296927340710973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 634406730741729236454281297 475805048056296927340710973)
        ·
          refine ⟨178426893021111347752766615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 475805048056296927340710973 178426893021111347752766615)
          ·
            refine ⟨267640339531667021629149923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 178426893021111347752766615 267640339531667021629149923)
            ·
              refine ⟨401460509297500532443724885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 267640339531667021629149923 401460509297500532443724885)
              ·
                refine ⟨4704615343330084364574901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 401460509297500532443724885 4704615343330084364574901)
                ·
                  refine ⟨441057688437195409178897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4704615343330084364574901 441057688437195409178897)
                  ·
                    rfl

theorem cell23_7730611_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 8, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 8, 5].length) (baseStart_7730611 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7730611 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7730611 prefixEnd_7730611 := by exact prefixLift 7730611
  have htrace : WordTrace (prefixWord ++ tailWord_7730611) baseStart_7730611 baseEnd_7730611 := by
    simpa [prefixWord, tailWord_7730611, baseEnd_7730611] using wordTrace_append hprefix tailTrace_7730611
  have hstable : (prefixWord ++ tailWord_7730611).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7730611).length < 2 ^ (prefixWord ++ tailWord_7730611).sum := by decide
  have hdescent : baseEnd_7730611 < baseStart_7730611 := by decide
  rcases family_descends (prefixWord ++ tailWord_7730611) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7730621 : List Nat := [1, 4, 1, 2, 2, 1, 2, 1, 1, 5, 3]
def baseStart_7730621 : Nat := 118140960795 + 7730621 * 2 ^ 59
def prefixEnd_7730621 : Nat := 4983230072969 + 3 ^ 40 * 7730621 * 2
def baseEnd_7730621 : Nat := 3969524330741303643485027

theorem tailTrace_7730621 : CollatzResearch.WordTrace tailWord_7730621 prefixEnd_7730621 3969524330741303643485027 := by
  unfold tailWord_7730621
  simp only [CollatzResearch.WordTrace]
  refine ⟨281958911726287876798655717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187972607817525251199103811 281958911726287876798655717)
  ·
    refine ⟨52867295948678976899747947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 281958911726287876798655717 52867295948678976899747947)
    ·
      refine ⟨79300943923018465349621921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52867295948678976899747947 79300943923018465349621921)
      ·
        refine ⟨59475707942263849012216441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79300943923018465349621921 59475707942263849012216441)
        ·
          refine ⟨44606780956697886759162331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59475707942263849012216441 44606780956697886759162331)
          ·
            refine ⟨66910171435046830138743497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44606780956697886759162331 66910171435046830138743497)
            ·
              refine ⟨50182628576285122604057623, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66910171435046830138743497 50182628576285122604057623)
              ·
                refine ⟨75273942864427683906086435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50182628576285122604057623 75273942864427683906086435)
                ·
                  refine ⟨112910914296641525859129653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 75273942864427683906086435 112910914296641525859129653)
                  ·
                    refine ⟨10585398215310143049293405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 112910914296641525859129653 10585398215310143049293405)
                    ·
                      refine ⟨3969524330741303643485027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10585398215310143049293405 3969524330741303643485027)
                      ·
                        rfl

theorem cell23_7730621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 2, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 2, 1, 1, 5, 3].length) (baseStart_7730621 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7730621 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7730621 prefixEnd_7730621 := by exact prefixLift 7730621
  have htrace : WordTrace (prefixWord ++ tailWord_7730621) baseStart_7730621 baseEnd_7730621 := by
    simpa [prefixWord, tailWord_7730621, baseEnd_7730621] using wordTrace_append hprefix tailTrace_7730621
  have hstable : (prefixWord ++ tailWord_7730621).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7730621).length < 2 ^ (prefixWord ++ tailWord_7730621).sum := by decide
  have hdescent : baseEnd_7730621 < baseStart_7730621 := by decide
  rcases family_descends (prefixWord ++ tailWord_7730621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7730624 : List Nat := [2, 1, 1, 2, 3, 1, 2, 1, 3, 7]
def baseStart_7730624 : Nat := 118140960795 + 7730624 * 2 ^ 59
def prefixEnd_7730624 : Nat := 4983230072969 + 3 ^ 40 * 7730624 * 2
def baseEnd_7730624 : Nat := 1323175290394422377249171

theorem tailTrace_7730624 : CollatzResearch.WordTrace tailWord_7730624 prefixEnd_7730624 1323175290394422377249171 := by
  unfold tailWord_7730624
  simp only [CollatzResearch.WordTrace]
  refine ⟨140979510572638504155507463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 187972680763518005540676617 140979510572638504155507463)
  ·
    refine ⟨211469265858957756233261195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140979510572638504155507463 211469265858957756233261195)
    ·
      refine ⟨317203898788436634349891793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 211469265858957756233261195 317203898788436634349891793)
      ·
        refine ⟨237902924091327475762418845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 317203898788436634349891793 237902924091327475762418845)
        ·
          refine ⟨89213596534247803410907067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 237902924091327475762418845 89213596534247803410907067)
          ·
            refine ⟨133820394801371705116360601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89213596534247803410907067 133820394801371705116360601)
            ·
              refine ⟨100365296101028778837270451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 133820394801371705116360601 100365296101028778837270451)
              ·
                refine ⟨150547944151543168255905677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 100365296101028778837270451 150547944151543168255905677)
                ·
                  refine ⟨56455479056828688095964629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 150547944151543168255905677 56455479056828688095964629)
                  ·
                    refine ⟨1323175290394422377249171, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 56455479056828688095964629 1323175290394422377249171)
                    ·
                      rfl

theorem cell23_7730624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 2, 1, 3, 7].length) (baseStart_7730624 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7730624 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7730624 prefixEnd_7730624 := by exact prefixLift 7730624
  have htrace : WordTrace (prefixWord ++ tailWord_7730624) baseStart_7730624 baseEnd_7730624 := by
    simpa [prefixWord, tailWord_7730624, baseEnd_7730624] using wordTrace_append hprefix tailTrace_7730624
  have hstable : (prefixWord ++ tailWord_7730624).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7730624).length < 2 ^ (prefixWord ++ tailWord_7730624).sum := by decide
  have hdescent : baseEnd_7730624 < baseStart_7730624 := by decide
  rcases family_descends (prefixWord ++ tailWord_7730624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7730626 : List Nat := [3, 5, 2, 1, 1, 1, 1, 1, 3, 3, 2]
def baseStart_7730626 : Nat := 118140960795 + 7730626 * 2 ^ 59
def prefixEnd_7730626 : Nat := 4983230072969 + 3 ^ 40 * 7730626 * 2
def baseEnd_7730626 : Nat := 3969526898144576123922505

theorem tailTrace_7730626 : CollatzResearch.WordTrace tailWord_7730626 prefixEnd_7730626 3969526898144576123922505 := by
  unfold tailWord_7730626
  simp only [CollatzResearch.WordTrace]
  refine ⟨70489773522817440663146933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 187972729394179841768391821 70489773522817440663146933)
  ·
    refine ⟨6608416267764135062170025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 70489773522817440663146933 6608416267764135062170025)
    ·
      refine ⟨4956312200823101296627519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6608416267764135062170025 4956312200823101296627519)
      ·
        refine ⟨7434468301234651944941279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4956312200823101296627519 7434468301234651944941279)
        ·
          refine ⟨11151702451851977917411919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7434468301234651944941279 11151702451851977917411919)
          ·
            refine ⟨16727553677777966876117879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11151702451851977917411919 16727553677777966876117879)
            ·
              refine ⟨25091330516666950314176819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16727553677777966876117879 25091330516666950314176819)
              ·
                refine ⟨37636995775000425471265229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25091330516666950314176819 37636995775000425471265229)
                ·
                  refine ⟨14113873415625159551724461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37636995775000425471265229 14113873415625159551724461)
                  ·
                    refine ⟨5292702530859434831896673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14113873415625159551724461 5292702530859434831896673)
                    ·
                      refine ⟨3969526898144576123922505, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5292702530859434831896673 3969526898144576123922505)
                      ·
                        rfl

theorem cell23_7730626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 1, 1, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 1, 1, 1, 1, 3, 3, 2].length) (baseStart_7730626 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7730626 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7730626 prefixEnd_7730626 := by exact prefixLift 7730626
  have htrace : WordTrace (prefixWord ++ tailWord_7730626) baseStart_7730626 baseEnd_7730626 := by
    simpa [prefixWord, tailWord_7730626, baseEnd_7730626] using wordTrace_append hprefix tailTrace_7730626
  have hstable : (prefixWord ++ tailWord_7730626).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7730626).length < 2 ^ (prefixWord ++ tailWord_7730626).sum := by decide
  have hdescent : baseEnd_7730626 < baseStart_7730626 := by decide
  rcases family_descends (prefixWord ++ tailWord_7730626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7730681 : List Nat := [1, 2, 1, 3, 1, 2, 1, 4, 1, 4, 3]
def baseStart_7730681 : Nat := 118140960795 + 7730681 * 2 ^ 59
def prefixEnd_7730681 : Nat := 4983230072969 + 3 ^ 40 * 7730681 * 2
def baseEnd_7730681 : Nat := 3969555139580573408734751

theorem tailTrace_7730681 : CollatzResearch.WordTrace tailWord_7730681 prefixEnd_7730681 3969555139580573408734751 := by
  unfold tailWord_7730681
  simp only [CollatzResearch.WordTrace]
  refine ⟨281961100106070507045839897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187974066737380338030559931 281961100106070507045839897)
  ·
    refine ⟨211470825079552880284379923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 281961100106070507045839897 211470825079552880284379923)
    ·
      refine ⟨317206237619329320426569885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 211470825079552880284379923 317206237619329320426569885)
      ·
        refine ⟨118952339107248495159963707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 317206237619329320426569885 118952339107248495159963707)
        ·
          refine ⟨178428508660872742739945561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 118952339107248495159963707 178428508660872742739945561)
          ·
            refine ⟨133821381495654557054959171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 178428508660872742739945561 133821381495654557054959171)
            ·
              refine ⟨200732072243481835582438757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 133821381495654557054959171 200732072243481835582438757)
              ·
                refine ⟨37637263545652844171707267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 200732072243481835582438757 37637263545652844171707267)
                ·
                  refine ⟨56455895318479266257560901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37637263545652844171707267 56455895318479266257560901)
                  ·
                    refine ⟨10585480372214862423292669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 56455895318479266257560901 10585480372214862423292669)
                    ·
                      refine ⟨3969555139580573408734751, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10585480372214862423292669 3969555139580573408734751)
                      ·
                        rfl

theorem cell23_7730681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 1, 4, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 1, 4, 1, 4, 3].length) (baseStart_7730681 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7730681 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7730681 prefixEnd_7730681 := by exact prefixLift 7730681
  have htrace : WordTrace (prefixWord ++ tailWord_7730681) baseStart_7730681 baseEnd_7730681 := by
    simpa [prefixWord, tailWord_7730681, baseEnd_7730681] using wordTrace_append hprefix tailTrace_7730681
  have hstable : (prefixWord ++ tailWord_7730681).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7730681).length < 2 ^ (prefixWord ++ tailWord_7730681).sum := by decide
  have hdescent : baseEnd_7730681 < baseStart_7730681 := by decide
  rcases family_descends (prefixWord ++ tailWord_7730681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7730692 : List Nat := [2, 3, 2, 3, 3, 1, 1, 1, 2, 5]
def baseStart_7730692 : Nat := 118140960795 + 7730692 * 2 ^ 59
def prefixEnd_7730692 : Nat := 4983230072969 + 3 ^ 40 * 7730692 * 2
def baseEnd_7730692 : Nat := 1323186929289257621899067

theorem tailTrace_7730692 : CollatzResearch.WordTrace tailWord_7730692 prefixEnd_7730692 1323186929289257621899067 := by
  unfold tailWord_7730692
  simp only [CollatzResearch.WordTrace]
  refine ⟨140980750654515327962245165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 187974334206020437282993553 140980750654515327962245165)
  ·
    refine ⟨52867781495443247985841937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 140980750654515327962245165 52867781495443247985841937)
    ·
      refine ⟨39650836121582435989381453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52867781495443247985841937 39650836121582435989381453)
      ·
        refine ⟨14869063545593413496018045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39650836121582435989381453 14869063545593413496018045)
        ·
          refine ⟨5575898829597530061006767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14869063545593413496018045 5575898829597530061006767)
          ·
            refine ⟨8363848244396295091510151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5575898829597530061006767 8363848244396295091510151)
            ·
              refine ⟨12545772366594442637265227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8363848244396295091510151 12545772366594442637265227)
              ·
                refine ⟨18818658549891663955897841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12545772366594442637265227 18818658549891663955897841)
                ·
                  refine ⟨14113993912418747966923381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18818658549891663955897841 14113993912418747966923381)
                  ·
                    refine ⟨1323186929289257621899067, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14113993912418747966923381 1323186929289257621899067)
                    ·
                      rfl

theorem cell23_7730692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 3, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 3, 1, 1, 1, 2, 5].length) (baseStart_7730692 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7730692 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7730692 prefixEnd_7730692 := by exact prefixLift 7730692
  have htrace : WordTrace (prefixWord ++ tailWord_7730692) baseStart_7730692 baseEnd_7730692 := by
    simpa [prefixWord, tailWord_7730692, baseEnd_7730692] using wordTrace_append hprefix tailTrace_7730692
  have hstable : (prefixWord ++ tailWord_7730692).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7730692).length < 2 ^ (prefixWord ++ tailWord_7730692).sum := by decide
  have hdescent : baseEnd_7730692 < baseStart_7730692 := by decide
  rcases family_descends (prefixWord ++ tailWord_7730692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7730695 : List Nat := [1, 1, 4, 3, 2, 3, 1, 1, 2, 1, 4]
def baseStart_7730695 : Nat := 118140960795 + 7730695 * 2 ^ 59
def prefixEnd_7730695 : Nat := 4983230072969 + 3 ^ 40 * 7730695 * 2
def baseEnd_7730695 : Nat := 3969562328309736353959687

theorem tailTrace_7730695 : CollatzResearch.WordTrace tailWord_7730695 prefixEnd_7730695 3969562328309736353959687 := by
  unfold tailWord_7730695
  simp only [CollatzResearch.WordTrace]
  refine ⟨281961610728019787436849539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187974407152013191624566359 281961610728019787436849539)
  ·
    refine ⟨422942416092029681155274309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 281961610728019787436849539 422942416092029681155274309)
    ·
      refine ⟨79301703017255565216613933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 422942416092029681155274309 79301703017255565216613933)
      ·
        refine ⟨29738138631470836956230225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 79301703017255565216613933 29738138631470836956230225)
        ·
          refine ⟨22303603973603127717172669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29738138631470836956230225 22303603973603127717172669)
          ·
            refine ⟨8363851490101172893939751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22303603973603127717172669 8363851490101172893939751)
            ·
              refine ⟨12545777235151759340909627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8363851490101172893939751 12545777235151759340909627)
              ·
                refine ⟨18818665852727639011364441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12545777235151759340909627 18818665852727639011364441)
                ·
                  refine ⟨14113999389545729258523331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18818665852727639011364441 14113999389545729258523331)
                  ·
                    refine ⟨21170999084318593887784997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14113999389545729258523331 21170999084318593887784997)
                    ·
                      refine ⟨3969562328309736353959687, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21170999084318593887784997 3969562328309736353959687)
                      ·
                        rfl

theorem cell23_7730695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 3, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 3, 1, 1, 2, 1, 4].length) (baseStart_7730695 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7730695 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7730695 prefixEnd_7730695 := by exact prefixLift 7730695
  have htrace : WordTrace (prefixWord ++ tailWord_7730695) baseStart_7730695 baseEnd_7730695 := by
    simpa [prefixWord, tailWord_7730695, baseEnd_7730695] using wordTrace_append hprefix tailTrace_7730695
  have hstable : (prefixWord ++ tailWord_7730695).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7730695).length < 2 ^ (prefixWord ++ tailWord_7730695).sum := by decide
  have hdescent : baseEnd_7730695 < baseStart_7730695 := by decide
  rcases family_descends (prefixWord ++ tailWord_7730695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7730698 : List Nat := [3, 1, 2, 2, 2, 3, 1, 1, 1, 4, 3]
def baseStart_7730698 : Nat := 118140960795 + 7730698 * 2 ^ 59
def prefixEnd_7730698 : Nat := 4983230072969 + 3 ^ 40 * 7730698 * 2
def baseEnd_7730698 : Nat := 3969563868751699842222173

theorem tailTrace_7730698 : CollatzResearch.WordTrace tailWord_7730698 prefixEnd_7730698 3969563868751699842222173 := by
  unfold tailWord_7730698
  simp only [CollatzResearch.WordTrace]
  refine ⟨70490430036752229737302187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 187974480098005945966139165 70490430036752229737302187)
  ·
    refine ⟨105735645055128344605953281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70490430036752229737302187 105735645055128344605953281)
    ·
      refine ⟨79301733791346258454464961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 105735645055128344605953281 79301733791346258454464961)
      ·
        refine ⟨59476300343509693840848721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79301733791346258454464961 59476300343509693840848721)
        ·
          refine ⟨44607225257632270380636541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59476300343509693840848721 44607225257632270380636541)
          ·
            refine ⟨16727709471612101392738703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44607225257632270380636541 16727709471612101392738703)
            ·
              refine ⟨25091564207418152089108055, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16727709471612101392738703 25091564207418152089108055)
              ·
                refine ⟨37637346311127228133662083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25091564207418152089108055 37637346311127228133662083)
                ·
                  refine ⟨56456019466690842200493125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37637346311127228133662083 56456019466690842200493125)
                  ·
                    refine ⟨10585503650004532912592461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 56456019466690842200493125 10585503650004532912592461)
                    ·
                      refine ⟨3969563868751699842222173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10585503650004532912592461 3969563868751699842222173)
                      ·
                        rfl

theorem cell23_7730698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 3, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 3, 1, 1, 1, 4, 3].length) (baseStart_7730698 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7730698 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7730698 prefixEnd_7730698 := by exact prefixLift 7730698
  have htrace : WordTrace (prefixWord ++ tailWord_7730698) baseStart_7730698 baseEnd_7730698 := by
    simpa [prefixWord, tailWord_7730698, baseEnd_7730698] using wordTrace_append hprefix tailTrace_7730698
  have hstable : (prefixWord ++ tailWord_7730698).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7730698).length < 2 ^ (prefixWord ++ tailWord_7730698).sum := by decide
  have hdescent : baseEnd_7730698 < baseStart_7730698 := by decide
  rcases family_descends (prefixWord ++ tailWord_7730698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7730705 : List Nat := [1, 2, 2, 1, 1, 2, 6, 3, 1, 4]
def baseStart_7730705 : Nat := 118140960795 + 7730705 * 2 ^ 59
def prefixEnd_7730705 : Nat := 4983230072969 + 3 ^ 40 * 7730705 * 2
def baseEnd_7730705 : Nat := 1323189154372093771611547

theorem tailTrace_7730705 : CollatzResearch.WordTrace tailWord_7730705 prefixEnd_7730705 1323189154372093771611547 := by
  unfold tailWord_7730705
  simp only [CollatzResearch.WordTrace]
  refine ⟨281961975457983559144713569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187974650305322372763142379 281961975457983559144713569)
  ·
    refine ⟨211471481593487669358535177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 281961975457983559144713569 211471481593487669358535177)
    ·
      refine ⟨158603611195115752018901383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 211471481593487669358535177 158603611195115752018901383)
      ·
        refine ⟨237905416792673628028352075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 158603611195115752018901383 237905416792673628028352075)
        ·
          refine ⟨356858125189010442042528113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 237905416792673628028352075 356858125189010442042528113)
          ·
            refine ⟨267643593891757831531896085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 356858125189010442042528113 267643593891757831531896085)
            ·
              refine ⟨12545793463676148353057629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 267643593891757831531896085 12545793463676148353057629)
              ·
                refine ⟨4704672548878555632396611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12545793463676148353057629 4704672548878555632396611)
                ·
                  refine ⟨7057008823317833448594917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4704672548878555632396611 7057008823317833448594917)
                  ·
                    refine ⟨1323189154372093771611547, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7057008823317833448594917 1323189154372093771611547)
                    ·
                      rfl

theorem cell23_7730705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 6, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 6, 3, 1, 4].length) (baseStart_7730705 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7730705 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7730705 prefixEnd_7730705 := by exact prefixLift 7730705
  have htrace : WordTrace (prefixWord ++ tailWord_7730705) baseStart_7730705 baseEnd_7730705 := by
    simpa [prefixWord, tailWord_7730705, baseEnd_7730705] using wordTrace_append hprefix tailTrace_7730705
  have hstable : (prefixWord ++ tailWord_7730705).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7730705).length < 2 ^ (prefixWord ++ tailWord_7730705).sum := by decide
  have hdescent : baseEnd_7730705 < baseStart_7730705 := by decide
  rcases family_descends (prefixWord ++ tailWord_7730705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7730721 : List Nat := [1, 2, 3, 2, 2, 2, 1, 1, 1, 2, 6]
def baseStart_7730721 : Nat := 118140960795 + 7730721 * 2 ^ 59
def prefixEnd_7730721 : Nat := 4983230072969 + 3 ^ 40 * 7730721 * 2
def baseEnd_7730721 : Nat := 3969575678806753252234567

theorem tailTrace_7730721 : CollatzResearch.WordTrace tailWord_7730721 prefixEnd_7730721 3969575678806753252234567 := by
  unfold tailWord_7730721
  simp only [CollatzResearch.WordTrace]
  refine ⟨281962559025925593877296017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187975039350617062584864011 281962559025925593877296017)
  ·
    refine ⟨211471919269444195407972013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 281962559025925593877296017 211471919269444195407972013)
    ·
      refine ⟨79301969726041573277989505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 211471919269444195407972013 79301969726041573277989505)
      ·
        refine ⟨59476477294531179958492129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79301969726041573277989505 59476477294531179958492129)
        ·
          refine ⟨44607357970898384968869097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59476477294531179958492129 44607357970898384968869097)
          ·
            refine ⟨33455518478173788726651823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44607357970898384968869097 33455518478173788726651823)
            ·
              refine ⟨50183277717260683089977735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33455518478173788726651823 50183277717260683089977735)
              ·
                refine ⟨75274916575891024634966603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50183277717260683089977735 75274916575891024634966603)
                ·
                  refine ⟨112912374863836536952449905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 75274916575891024634966603 112912374863836536952449905)
                  ·
                    refine ⟨84684281147877402714337429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 112912374863836536952449905 84684281147877402714337429)
                    ·
                      refine ⟨3969575678806753252234567, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 84684281147877402714337429 3969575678806753252234567)
                      ·
                        rfl

theorem cell23_7730721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 1, 1, 1, 2, 6].length) (baseStart_7730721 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7730721 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7730721 prefixEnd_7730721 := by exact prefixLift 7730721
  have htrace : WordTrace (prefixWord ++ tailWord_7730721) baseStart_7730721 baseEnd_7730721 := by
    simpa [prefixWord, tailWord_7730721, baseEnd_7730721] using wordTrace_append hprefix tailTrace_7730721
  have hstable : (prefixWord ++ tailWord_7730721).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7730721).length < 2 ^ (prefixWord ++ tailWord_7730721).sum := by decide
  have hdescent : baseEnd_7730721 < baseStart_7730721 := by decide
  rcases family_descends (prefixWord ++ tailWord_7730721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7730745 : List Nat := [1, 2, 1, 5, 1, 2, 2, 2, 3, 1, 3]
def baseStart_7730745 : Nat := 118140960795 + 7730745 * 2 ^ 59
def prefixEnd_7730745 : Nat := 4983230072969 + 3 ^ 40 * 7730745 * 2
def baseEnd_7730745 : Nat := 3969588002342461158334457

theorem tailTrace_7730745 : CollatzResearch.WordTrace tailWord_7730745 prefixEnd_7730745 3969588002342461158334457 := by
  unfold tailWord_7730745
  simp only [CollatzResearch.WordTrace]
  refine ⟨281963434377838645976169689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187975622918559097317446459 281963434377838645976169689)
  ·
    refine ⟨211472575783378984482127267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 281963434377838645976169689 211472575783378984482127267)
    ·
      refine ⟨317208863675068476723190901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 211472575783378984482127267 317208863675068476723190901)
      ·
        refine ⟨29738330969537669692799147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 317208863675068476723190901 29738330969537669692799147)
        ·
          refine ⟨44607496454306504539198721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29738330969537669692799147 44607496454306504539198721)
          ·
            refine ⟨33455622340729878404399041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44607496454306504539198721 33455622340729878404399041)
            ·
              refine ⟨25091716755547408803299281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33455622340729878404399041 25091716755547408803299281)
              ·
                refine ⟨18818787566660556602474461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25091716755547408803299281 18818787566660556602474461)
                ·
                  refine ⟨7057045337497708725927923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18818787566660556602474461 7057045337497708725927923)
                  ·
                    refine ⟨10585568006246563088891885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7057045337497708725927923 10585568006246563088891885)
                    ·
                      refine ⟨3969588002342461158334457, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10585568006246563088891885 3969588002342461158334457)
                      ·
                        rfl

theorem cell23_7730745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 2, 2, 3, 1, 3].length) (baseStart_7730745 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7730745 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7730745 prefixEnd_7730745 := by exact prefixLift 7730745
  have htrace : WordTrace (prefixWord ++ tailWord_7730745) baseStart_7730745 baseEnd_7730745 := by
    simpa [prefixWord, tailWord_7730745, baseEnd_7730745] using wordTrace_append hprefix tailTrace_7730745
  have hstable : (prefixWord ++ tailWord_7730745).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7730745).length < 2 ^ (prefixWord ++ tailWord_7730745).sum := by decide
  have hdescent : baseEnd_7730745 < baseStart_7730745 := by decide
  rcases family_descends (prefixWord ++ tailWord_7730745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7730761 : List Nat := [1, 2, 1, 1, 2, 2, 1, 6, 1, 6]
def baseStart_7730761 : Nat := 118140960795 + 7730761 * 2 ^ 59
def prefixEnd_7730761 : Nat := 4983230072969 + 3 ^ 40 * 7730761 * 2
def baseEnd_7730761 : Nat := 1323198739344311031911461

theorem tailTrace_7730761 : CollatzResearch.WordTrace tailWord_7730761 prefixEnd_7730761 1323198739344311031911461 := by
  unfold tailWord_7730761
  simp only [CollatzResearch.WordTrace]
  refine ⟨281964017945780680708752137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187976011963853787139168091 281964017945780680708752137)
  ·
    refine ⟨211473013459335510531564103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 281964017945780680708752137 211473013459335510531564103)
    ·
      refine ⟨317209520189003265797346155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 211473013459335510531564103 317209520189003265797346155)
      ·
        refine ⟨475814280283504898696019233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 317209520189003265797346155 475814280283504898696019233)
        ·
          refine ⟨356860710212628674022014425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 475814280283504898696019233 356860710212628674022014425)
          ·
            refine ⟨267645532659471505516510819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 356860710212628674022014425 267645532659471505516510819)
            ·
              refine ⟨401468298989207258274766229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 267645532659471505516510819 401468298989207258274766229)
              ·
                refine ⟨18818826515119090231629667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 401468298989207258274766229 18818826515119090231629667)
                ·
                  refine ⟨28228239772678635347444501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18818826515119090231629667 28228239772678635347444501)
                  ·
                    refine ⟨1323198739344311031911461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28228239772678635347444501 1323198739344311031911461)
                    ·
                      rfl

theorem cell23_7730761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 6, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 6, 1, 6].length) (baseStart_7730761 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7730761 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7730761 prefixEnd_7730761 := by exact prefixLift 7730761
  have htrace : WordTrace (prefixWord ++ tailWord_7730761) baseStart_7730761 baseEnd_7730761 := by
    simpa [prefixWord, tailWord_7730761, baseEnd_7730761] using wordTrace_append hprefix tailTrace_7730761
  have hstable : (prefixWord ++ tailWord_7730761).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7730761).length < 2 ^ (prefixWord ++ tailWord_7730761).sum := by decide
  have hdescent : baseEnd_7730761 < baseStart_7730761 := by decide
  rcases family_descends (prefixWord ++ tailWord_7730761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7730768 : List Nat := [2, 1, 1, 1, 1, 3, 3, 5, 1, 1, 4]
def baseStart_7730768 : Nat := 118140960795 + 7730768 * 2 ^ 59
def prefixEnd_7730768 : Nat := 4983230072969 + 3 ^ 40 * 7730768 * 2
def baseEnd_7730768 : Nat := 3969599812397514568346851

theorem tailTrace_7730768 : CollatzResearch.WordTrace tailWord_7730768 prefixEnd_7730768 3969599812397514568346851 := by
  unfold tailWord_7730768
  simp only [CollatzResearch.WordTrace]
  refine ⟨140982136628377660452128479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 187976182171170213936171305 140982136628377660452128479)
  ·
    refine ⟨211473204942566490678192719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140982136628377660452128479 211473204942566490678192719)
    ·
      refine ⟨317209807413849736017289079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 211473204942566490678192719 317209807413849736017289079)
      ·
        refine ⟨475814711120774604025933619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 317209807413849736017289079 475814711120774604025933619)
        ·
          refine ⟨713722066681161906038900429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 475814711120774604025933619 713722066681161906038900429)
          ·
            refine ⟨267645775005435714764587661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 713722066681161906038900429 267645775005435714764587661)
            ·
              refine ⟨100367165627038393036720373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 267645775005435714764587661 100367165627038393036720373)
              ·
                refine ⟨9409421777534849347192535, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 100367165627038393036720373 9409421777534849347192535)
                ·
                  refine ⟨14114132666302274020788803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9409421777534849347192535 14114132666302274020788803)
                  ·
                    refine ⟨21171198999453411031183205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14114132666302274020788803 21171198999453411031183205)
                    ·
                      refine ⟨3969599812397514568346851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21171198999453411031183205 3969599812397514568346851)
                      ·
                        rfl

theorem cell23_7730768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 3, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 3, 5, 1, 1, 4].length) (baseStart_7730768 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7730768 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7730768 prefixEnd_7730768 := by exact prefixLift 7730768
  have htrace : WordTrace (prefixWord ++ tailWord_7730768) baseStart_7730768 baseEnd_7730768 := by
    simpa [prefixWord, tailWord_7730768, baseEnd_7730768] using wordTrace_append hprefix tailTrace_7730768
  have hstable : (prefixWord ++ tailWord_7730768).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7730768).length < 2 ^ (prefixWord ++ tailWord_7730768).sum := by decide
  have hdescent : baseEnd_7730768 < baseStart_7730768 := by decide
  rcases family_descends (prefixWord ++ tailWord_7730768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7730788 : List Nat := [2, 3, 1, 1, 2, 3, 2, 2, 1, 1, 5]
def baseStart_7730788 : Nat := 118140960795 + 7730788 * 2 ^ 59
def prefixEnd_7730788 : Nat := 4983230072969 + 3 ^ 40 * 7730788 * 2
def baseEnd_7730788 : Nat := 3969610082010604490096759

theorem tailTrace_7730788 : CollatzResearch.WordTrace tailWord_7730788 prefixEnd_7730788 3969610082010604490096759 := by
  unfold tailWord_7730788
  simp only [CollatzResearch.WordTrace]
  refine ⟨140982501358341432159992509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 187976668477788576213323345 140982501358341432159992509)
  ·
    refine ⟨52868438009378037059997191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 140982501358341432159992509 52868438009378037059997191)
    ·
      refine ⟨79302657014067055589995787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52868438009378037059997191 79302657014067055589995787)
      ·
        refine ⟨118953985521100583384993681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79302657014067055589995787 118953985521100583384993681)
        ·
          refine ⟨89215489140825437538745261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 118953985521100583384993681 89215489140825437538745261)
          ·
            refine ⟨33455808427809539077029473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 89215489140825437538745261 33455808427809539077029473)
            ·
              refine ⟨25091856320857154307772105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33455808427809539077029473 25091856320857154307772105)
              ·
                refine ⟨18818892240642865730829079, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25091856320857154307772105 18818892240642865730829079)
                ·
                  refine ⟨28228338360964298596243619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18818892240642865730829079 28228338360964298596243619)
                  ·
                    refine ⟨42342507541446447894365429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28228338360964298596243619 42342507541446447894365429)
                    ·
                      refine ⟨3969610082010604490096759, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42342507541446447894365429 3969610082010604490096759)
                      ·
                        rfl

theorem cell23_7730788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 2, 2, 1, 1, 5].length) (baseStart_7730788 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7730788 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7730788 prefixEnd_7730788 := by exact prefixLift 7730788
  have htrace : WordTrace (prefixWord ++ tailWord_7730788) baseStart_7730788 baseEnd_7730788 := by
    simpa [prefixWord, tailWord_7730788, baseEnd_7730788] using wordTrace_append hprefix tailTrace_7730788
  have hstable : (prefixWord ++ tailWord_7730788).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7730788).length < 2 ^ (prefixWord ++ tailWord_7730788).sum := by decide
  have hdescent : baseEnd_7730788 < baseStart_7730788 := by decide
  rcases family_descends (prefixWord ++ tailWord_7730788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7730791 : List Nat := [1, 1, 5, 1, 1, 1, 3, 10]
def baseStart_7730791 : Nat := 118140960795 + 7730791 * 2 ^ 59
def prefixEnd_7730791 : Nat := 4983230072969 + 3 ^ 40 * 7730791 * 2
def baseEnd_7730791 : Nat := 147022652683428443642935

theorem tailTrace_7730791 : CollatzResearch.WordTrace tailWord_7730791 prefixEnd_7730791 147022652683428443642935 := by
  unfold tailWord_7730791
  simp only [CollatzResearch.WordTrace]
  refine ⟨281965112135671995832344227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187976741423781330554896151 281965112135671995832344227)
  ·
    refine ⟨422947668203507993748516341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 281965112135671995832344227 422947668203507993748516341)
    ·
      refine ⟨39651343894078874413923407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 422947668203507993748516341 39651343894078874413923407)
      ·
        refine ⟨59477015841118311620885111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39651343894078874413923407 59477015841118311620885111)
        ·
          refine ⟨89215523761677467431327667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59477015841118311620885111 89215523761677467431327667)
          ·
            refine ⟨133823285642516201146991501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89215523761677467431327667 133823285642516201146991501)
            ·
              refine ⟨50183732115943575430121813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 133823285642516201146991501 50183732115943575430121813)
              ·
                refine ⟨147022652683428443642935, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 50183732115943575430121813 147022652683428443642935)
                ·
                  rfl

theorem cell23_7730791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 3, 10].length) (baseStart_7730791 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7730791 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7730791 prefixEnd_7730791 := by exact prefixLift 7730791
  have htrace : WordTrace (prefixWord ++ tailWord_7730791) baseStart_7730791 baseEnd_7730791 := by
    simpa [prefixWord, tailWord_7730791, baseEnd_7730791] using wordTrace_append hprefix tailTrace_7730791
  have hstable : (prefixWord ++ tailWord_7730791).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7730791).length < 2 ^ (prefixWord ++ tailWord_7730791).sum := by decide
  have hdescent : baseEnd_7730791 < baseStart_7730791 := by decide
  rcases family_descends (prefixWord ++ tailWord_7730791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7730802 : List Nat := [3, 2, 1, 2, 3, 3, 1, 2, 1, 1, 4]
def baseStart_7730802 : Nat := 118140960795 + 7730802 * 2 ^ 59
def prefixEnd_7730802 : Nat := 4983230072969 + 3 ^ 40 * 7730802 * 2
def baseEnd_7730802 : Nat := 3969617270739767435321695

theorem tailTrace_7730802 : CollatzResearch.WordTrace tailWord_7730802 prefixEnd_7730802 3969617270739767435321695 := by
  unfold tailWord_7730802
  simp only [CollatzResearch.WordTrace]
  refine ⟨70491378334658036177748665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 187977008892421429807329773 70491378334658036177748665)
  ·
    refine ⟨52868533750993527133311499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70491378334658036177748665 52868533750993527133311499)
    ·
      refine ⟨79302800626490290699967249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52868533750993527133311499 79302800626490290699967249)
      ·
        refine ⟨59477100469867718024975437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79302800626490290699967249 59477100469867718024975437)
        ·
          refine ⟨22303912676200394259365789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 59477100469867718024975437 22303912676200394259365789)
          ·
            refine ⟨8363967253575147847262171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22303912676200394259365789 8363967253575147847262171)
            ·
              refine ⟨12545950880362721770893257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8363967253575147847262171 12545950880362721770893257)
              ·
                refine ⟨9409463160272041328169943, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12545950880362721770893257 9409463160272041328169943)
                ·
                  refine ⟨14114194740408061992254915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9409463160272041328169943 14114194740408061992254915)
                  ·
                    refine ⟨21171292110612092988382373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14114194740408061992254915 21171292110612092988382373)
                    ·
                      refine ⟨3969617270739767435321695, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21171292110612092988382373 3969617270739767435321695)
                      ·
                        rfl

theorem cell23_7730802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 3, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 3, 1, 2, 1, 1, 4].length) (baseStart_7730802 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7730802 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7730802 prefixEnd_7730802 := by exact prefixLift 7730802
  have htrace : WordTrace (prefixWord ++ tailWord_7730802) baseStart_7730802 baseEnd_7730802 := by
    simpa [prefixWord, tailWord_7730802, baseEnd_7730802] using wordTrace_append hprefix tailTrace_7730802
  have hstable : (prefixWord ++ tailWord_7730802).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7730802).length < 2 ^ (prefixWord ++ tailWord_7730802).sum := by decide
  have hdescent : baseEnd_7730802 < baseStart_7730802 := by decide
  rcases family_descends (prefixWord ++ tailWord_7730802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7730852 : List Nat := [2, 3, 1, 2, 2, 2, 2, 3, 2, 1, 3]
def baseStart_7730852 : Nat := 118140960795 + 7730852 * 2 ^ 59
def prefixEnd_7730852 : Nat := 4983230072969 + 3 ^ 40 * 7730852 * 2
def baseEnd_7730852 : Nat := 3969642944772492239696465

theorem tailTrace_7730852 : CollatzResearch.WordTrace tailWord_7730852 prefixEnd_7730852 3969642944772492239696465 := by
  unfold tailWord_7730852
  simp only [CollatzResearch.WordTrace]
  refine ⟨140983668494225501625157405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 187978224658967335500209873 140983668494225501625157405)
  ·
    refine ⟨52868875685334563109434027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 140983668494225501625157405 52868875685334563109434027)
    ·
      refine ⟨79303313528001844664151041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52868875685334563109434027 79303313528001844664151041)
      ·
        refine ⟨59477485146001383498113281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79303313528001844664151041 59477485146001383498113281)
        ·
          refine ⟨44608113859501037623584961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59477485146001383498113281 44608113859501037623584961)
          ·
            refine ⟨33456085394625778217688721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44608113859501037623584961 33456085394625778217688721)
            ·
              refine ⟨25092064045969333663266541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33456085394625778217688721 25092064045969333663266541)
              ·
                refine ⟨9409524017238500123724953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25092064045969333663266541 9409524017238500123724953)
                ·
                  refine ⟨7057143012928875092793715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9409524017238500123724953 7057143012928875092793715)
                  ·
                    refine ⟨10585714519393312639190573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7057143012928875092793715 10585714519393312639190573)
                    ·
                      refine ⟨3969642944772492239696465, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10585714519393312639190573 3969642944772492239696465)
                      ·
                        rfl

theorem cell23_7730852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 2, 3, 2, 1, 3].length) (baseStart_7730852 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7730852 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7730852 prefixEnd_7730852 := by exact prefixLift 7730852
  have htrace : WordTrace (prefixWord ++ tailWord_7730852) baseStart_7730852 baseEnd_7730852 := by
    simpa [prefixWord, tailWord_7730852, baseEnd_7730852] using wordTrace_append hprefix tailTrace_7730852
  have hstable : (prefixWord ++ tailWord_7730852).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7730852).length < 2 ^ (prefixWord ++ tailWord_7730852).sum := by decide
  have hdescent : baseEnd_7730852 < baseStart_7730852 := by decide
  rcases family_descends (prefixWord ++ tailWord_7730852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7730886 : List Nat := [6, 1, 2, 1, 1, 2, 1, 1, 4, 1, 3]
def baseStart_7730886 : Nat := 118140960795 + 7730886 * 2 ^ 59
def prefixEnd_7730886 : Nat := 4983230072969 + 3 ^ 40 * 7730886 * 2
def baseEnd_7730886 : Nat := 3969660403114745106671309

theorem tailTrace_7730886 : CollatzResearch.WordTrace tailWord_7730886 prefixEnd_7730886 3969660403114745106671309 := by
  unfold tailWord_7730886
  simp only [CollatzResearch.WordTrace]
  refine ⟨8811518033447744595532891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 187979051380218551371368341 8811518033447744595532891)
  ·
    refine ⟨13217277050171616893299337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8811518033447744595532891 13217277050171616893299337)
    ·
      refine ⟨9912957787628712669974503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13217277050171616893299337 9912957787628712669974503)
      ·
        refine ⟨14869436681443069004961755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9912957787628712669974503 14869436681443069004961755)
        ·
          refine ⟨22304155022164603507442633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14869436681443069004961755 22304155022164603507442633)
          ·
            refine ⟨16728116266623452630581975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22304155022164603507442633 16728116266623452630581975)
            ·
              refine ⟨25092174399935178945872963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16728116266623452630581975 25092174399935178945872963)
              ·
                refine ⟨37638261599902768418809445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25092174399935178945872963 37638261599902768418809445)
                ·
                  refine ⟨7057174049981769078526771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 37638261599902768418809445 7057174049981769078526771)
                  ·
                    refine ⟨10585761074972653617790157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7057174049981769078526771 10585761074972653617790157)
                    ·
                      refine ⟨3969660403114745106671309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10585761074972653617790157 3969660403114745106671309)
                      ·
                        rfl

theorem cell23_7730886_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 2, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 2, 1, 1, 4, 1, 3].length) (baseStart_7730886 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7730886 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7730886 prefixEnd_7730886 := by exact prefixLift 7730886
  have htrace : WordTrace (prefixWord ++ tailWord_7730886) baseStart_7730886 baseEnd_7730886 := by
    simpa [prefixWord, tailWord_7730886, baseEnd_7730886] using wordTrace_append hprefix tailTrace_7730886
  have hstable : (prefixWord ++ tailWord_7730886).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7730886).length < 2 ^ (prefixWord ++ tailWord_7730886).sum := by decide
  have hdescent : baseEnd_7730886 < baseStart_7730886 := by decide
  rcases family_descends (prefixWord ++ tailWord_7730886) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7730888 : List Nat := [2, 1, 3, 1, 2, 2, 1, 1, 4, 2, 4]
def baseStart_7730888 : Nat := 118140960795 + 7730888 * 2 ^ 59
def prefixEnd_7730888 : Nat := 4983230072969 + 3 ^ 40 * 7730888 * 2
def baseEnd_7730888 : Nat := 3969661430076054098846299

theorem tailTrace_7730888 : CollatzResearch.WordTrace tailWord_7730888 prefixEnd_7730888 3969661430076054098846299 := by
  unfold tailWord_7730888
  simp only [CollatzResearch.WordTrace]
  refine ⟨140984325008160290699312659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 187979100010880387599083545 140984325008160290699312659)
  ·
    refine ⟨211476487512240436048968989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140984325008160290699312659 211476487512240436048968989)
    ·
      refine ⟨79303682817090163518363371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 211476487512240436048968989 79303682817090163518363371)
      ·
        refine ⟨118955524225635245277545057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79303682817090163518363371 118955524225635245277545057)
        ·
          refine ⟨89216643169226433958158793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 118955524225635245277545057 89216643169226433958158793)
          ·
            refine ⟨66912482376919825468619095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 89216643169226433958158793 66912482376919825468619095)
            ·
              refine ⟨100368723565379738202928643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66912482376919825468619095 100368723565379738202928643)
              ·
                refine ⟨150553085348069607304392965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 100368723565379738202928643 150553085348069607304392965)
                ·
                  refine ⟨28228703502763051369573681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 150553085348069607304392965 28228703502763051369573681)
                  ·
                    refine ⟨21171527627072288527180261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28228703502763051369573681 21171527627072288527180261)
                    ·
                      refine ⟨3969661430076054098846299, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21171527627072288527180261 3969661430076054098846299)
                      ·
                        rfl

theorem cell23_7730888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 1, 1, 4, 2, 4].length) (baseStart_7730888 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7730888 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7730888 prefixEnd_7730888 := by exact prefixLift 7730888
  have htrace : WordTrace (prefixWord ++ tailWord_7730888) baseStart_7730888 baseEnd_7730888 := by
    simpa [prefixWord, tailWord_7730888, baseEnd_7730888] using wordTrace_append hprefix tailTrace_7730888
  have hstable : (prefixWord ++ tailWord_7730888).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7730888).length < 2 ^ (prefixWord ++ tailWord_7730888).sum := by decide
  have hdescent : baseEnd_7730888 < baseStart_7730888 := by decide
  rcases family_descends (prefixWord ++ tailWord_7730888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7730938 : List Nat := [3, 1, 1, 1, 1, 3, 1, 4, 1, 2, 5]
def baseStart_7730938 : Nat := 118140960795 + 7730938 * 2 ^ 59
def prefixEnd_7730938 : Nat := 4983230072969 + 3 ^ 40 * 7730938 * 2
def baseEnd_7730938 : Nat := 3969687104108778903221069

theorem tailTrace_7730938 : CollatzResearch.WordTrace tailWord_7730938 prefixEnd_7730938 3969687104108778903221069 := by
  unfold tailWord_7730938
  simp only [CollatzResearch.WordTrace]
  refine ⟨70492618416534859984486367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 187980315777426293291963645 70492618416534859984486367)
  ·
    refine ⟨105738927624802289976729551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70492618416534859984486367 105738927624802289976729551)
    ·
      refine ⟨158608391437203434965094327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105738927624802289976729551 158608391437203434965094327)
      ·
        refine ⟨237912587155805152447641491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 158608391437203434965094327 237912587155805152447641491)
        ·
          refine ⟨356868880733707728671462237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 237912587155805152447641491 356868880733707728671462237)
          ·
            refine ⟨133825830275140398251798339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 356868880733707728671462237 133825830275140398251798339)
            ·
              refine ⟨200738745412710597377697509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 133825830275140398251798339 200738745412710597377697509)
              ·
                refine ⟨37638514764883237008318283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 200738745412710597377697509 37638514764883237008318283)
                ·
                  refine ⟨56457772147324855512477425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37638514764883237008318283 56457772147324855512477425)
                  ·
                    refine ⟨42343329110493641634358069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 56457772147324855512477425 42343329110493641634358069)
                    ·
                      refine ⟨3969687104108778903221069, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42343329110493641634358069 3969687104108778903221069)
                      ·
                        rfl

theorem cell23_7730938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 1, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 1, 4, 1, 2, 5].length) (baseStart_7730938 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7730938 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7730938 prefixEnd_7730938 := by exact prefixLift 7730938
  have htrace : WordTrace (prefixWord ++ tailWord_7730938) baseStart_7730938 baseEnd_7730938 := by
    simpa [prefixWord, tailWord_7730938, baseEnd_7730938] using wordTrace_append hprefix tailTrace_7730938
  have hstable : (prefixWord ++ tailWord_7730938).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7730938).length < 2 ^ (prefixWord ++ tailWord_7730938).sum := by decide
  have hdescent : baseEnd_7730938 < baseStart_7730938 := by decide
  rcases family_descends (prefixWord ++ tailWord_7730938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7730975 : List Nat := [1, 1, 2, 4, 2, 1, 2, 1, 5, 4]
def baseStart_7730975 : Nat := 118140960795 + 7730975 * 2 ^ 59
def prefixEnd_7730975 : Nat := 4983230072969 + 3 ^ 40 * 7730975 * 2
def baseEnd_7730975 : Nat := 1323235367630998419486133

theorem tailTrace_7730975 : CollatzResearch.WordTrace tailWord_7730975 prefixEnd_7730975 1323235367630998419486133 := by
  unfold tailWord_7730975
  simp only [CollatzResearch.WordTrace]
  refine ⟨281971823167005395257042379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187981215444670263504694919 281971823167005395257042379)
  ·
    refine ⟨422957734750508092885563569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 281971823167005395257042379 422957734750508092885563569)
    ·
      refine ⟨317218301062881069664172677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 422957734750508092885563569 317218301062881069664172677)
      ·
        refine ⟨59478431449290200562032377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 317218301062881069664172677 59478431449290200562032377)
        ·
          refine ⟨44608823586967650421524283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59478431449290200562032377 44608823586967650421524283)
          ·
            refine ⟨66913235380451475632286425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44608823586967650421524283 66913235380451475632286425)
            ·
              refine ⟨50184926535338606724214819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66913235380451475632286425 50184926535338606724214819)
              ·
                refine ⟨75277389803007910086322229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50184926535338606724214819 75277389803007910086322229)
                ·
                  refine ⟨7057255294031991570592709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 75277389803007910086322229 7057255294031991570592709)
                  ·
                    refine ⟨1323235367630998419486133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7057255294031991570592709 1323235367630998419486133)
                    ·
                      rfl

theorem cell23_7730975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 2, 1, 5, 4].length) (baseStart_7730975 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7730975 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7730975 prefixEnd_7730975 := by exact prefixLift 7730975
  have htrace : WordTrace (prefixWord ++ tailWord_7730975) baseStart_7730975 baseEnd_7730975 := by
    simpa [prefixWord, tailWord_7730975, baseEnd_7730975] using wordTrace_append hprefix tailTrace_7730975
  have hstable : (prefixWord ++ tailWord_7730975).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7730975).length < 2 ^ (prefixWord ++ tailWord_7730975).sum := by decide
  have hdescent : baseEnd_7730975 < baseStart_7730975 := by decide
  rcases family_descends (prefixWord ++ tailWord_7730975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7731002 : List Nat := [3, 1, 1, 1, 5, 1, 2, 2, 2, 2, 3]
def baseStart_7731002 : Nat := 118140960795 + 7731002 * 2 ^ 59
def prefixEnd_7731002 : Nat := 4983230072969 + 3 ^ 40 * 7731002 * 2
def baseEnd_7731002 : Nat := 3969719966870666652820775

theorem tailTrace_7731002 : CollatzResearch.WordTrace tailWord_7731002 prefixEnd_7731002 3969719966870666652820775 := by
  unfold tailWord_7731002
  simp only [CollatzResearch.WordTrace]
  refine ⟨70493201984476894717068815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 187981871958605052578850173 70493201984476894717068815)
  ·
    refine ⟨105739802976715342075603223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70493201984476894717068815 105739802976715342075603223)
    ·
      refine ⟨158609704465073013113404835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105739802976715342075603223 158609704465073013113404835)
      ·
        refine ⟨237914556697609519670107253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 158609704465073013113404835 237914556697609519670107253)
        ·
          refine ⟨22304489690400892469072555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 237914556697609519670107253 22304489690400892469072555)
          ·
            refine ⟨33456734535601338703608833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22304489690400892469072555 33456734535601338703608833)
            ·
              refine ⟨25092550901701004027706625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33456734535601338703608833 25092550901701004027706625)
              ·
                refine ⟨18819413176275753020779969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25092550901701004027706625 18819413176275753020779969)
                ·
                  refine ⟨14114559882206814765584977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18819413176275753020779969 14114559882206814765584977)
                  ·
                    refine ⟨10585919911655111074188733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14114559882206814765584977 10585919911655111074188733)
                    ·
                      refine ⟨3969719966870666652820775, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10585919911655111074188733 3969719966870666652820775)
                      ·
                        rfl

theorem cell23_7731002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 2, 2, 2, 2, 3].length) (baseStart_7731002 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7731002 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7731002 prefixEnd_7731002 := by exact prefixLift 7731002
  have htrace : WordTrace (prefixWord ++ tailWord_7731002) baseStart_7731002 baseEnd_7731002 := by
    simpa [prefixWord, tailWord_7731002, baseEnd_7731002] using wordTrace_append hprefix tailTrace_7731002
  have hstable : (prefixWord ++ tailWord_7731002).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7731002).length < 2 ^ (prefixWord ++ tailWord_7731002).sum := by decide
  have hdescent : baseEnd_7731002 < baseStart_7731002 := by decide
  rcases family_descends (prefixWord ++ tailWord_7731002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7731036 : List Nat := [2, 2, 4, 2, 2, 2, 1, 1, 2, 2, 3]
def baseStart_7731036 : Nat := 118140960795 + 7731036 * 2 ^ 59
def prefixEnd_7731036 : Nat := 4983230072969 + 3 ^ 40 * 7731036 * 2
def baseEnd_7731036 : Nat := 3969737425212919519795619

theorem tailTrace_7731036 : CollatzResearch.WordTrace tailWord_7731036 prefixEnd_7731036 3969737425212919519795619 := by
  unfold tailWord_7731036
  simp only [CollatzResearch.WordTrace]
  refine ⟨140987024009892201337506481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 187982698679856268450008641 140987024009892201337506481)
  ·
    refine ⟨105740268007419151003129861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 140987024009892201337506481 105740268007419151003129861)
    ·
      refine ⟨19826300251391090813086849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 105740268007419151003129861 19826300251391090813086849)
      ·
        refine ⟨14869725188543318109815137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19826300251391090813086849 14869725188543318109815137)
        ·
          refine ⟨11152293891407488582361353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14869725188543318109815137 11152293891407488582361353)
          ·
            refine ⟨8364220418555616436771015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11152293891407488582361353 8364220418555616436771015)
            ·
              refine ⟨12546330627833424655156523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8364220418555616436771015 12546330627833424655156523)
              ·
                refine ⟨18819495941750136982734785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12546330627833424655156523 18819495941750136982734785)
                ·
                  refine ⟨14114621956312602737051089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18819495941750136982734785 14114621956312602737051089)
                  ·
                    refine ⟨10585966467234452052788317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14114621956312602737051089 10585966467234452052788317)
                    ·
                      refine ⟨3969737425212919519795619, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10585966467234452052788317 3969737425212919519795619)
                      ·
                        rfl

theorem cell23_7731036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 2, 2, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 2, 2, 1, 1, 2, 2, 3].length) (baseStart_7731036 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7731036 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7731036 prefixEnd_7731036 := by exact prefixLift 7731036
  have htrace : WordTrace (prefixWord ++ tailWord_7731036) baseStart_7731036 baseEnd_7731036 := by
    simpa [prefixWord, tailWord_7731036, baseEnd_7731036] using wordTrace_append hprefix tailTrace_7731036
  have hstable : (prefixWord ++ tailWord_7731036).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7731036).length < 2 ^ (prefixWord ++ tailWord_7731036).sum := by decide
  have hdescent : baseEnd_7731036 < baseStart_7731036 := by decide
  rcases family_descends (prefixWord ++ tailWord_7731036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7731052 : List Nat := [2, 2, 1, 1, 4, 3, 1, 3, 1, 5]
def baseStart_7731052 : Nat := 118140960795 + 7731052 * 2 ^ 59
def prefixEnd_7731052 : Nat := 4983230072969 + 3 ^ 40 * 7731052 * 2
def baseEnd_7731052 : Nat := 1323248546967797152398515

theorem tailTrace_7731052 : CollatzResearch.WordTrace tailWord_7731052 prefixEnd_7731052 1323248546967797152398515 := by
  unfold tailWord_7731052
  simp only [CollatzResearch.WordTrace]
  refine ⟨140987315793863218703797705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 187983087725150958271730273 140987315793863218703797705)
  ·
    refine ⟨105740486845397414027848279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 140987315793863218703797705 105740486845397414027848279)
    ·
      refine ⟨158610730268096121041772419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105740486845397414027848279 158610730268096121041772419)
      ·
        refine ⟨237916095402144181562658629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 158610730268096121041772419 237916095402144181562658629)
        ·
          refine ⟨44609267887902034042998493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 237916095402144181562658629 44609267887902034042998493)
          ·
            refine ⟨16728475457963262766124435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44609267887902034042998493 16728475457963262766124435)
            ·
              refine ⟨25092713186944894149186653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16728475457963262766124435 25092713186944894149186653)
              ·
                refine ⟨9409767445104335305944995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25092713186944894149186653 9409767445104335305944995)
                ·
                  refine ⟨14114651167656502958917493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9409767445104335305944995 14114651167656502958917493)
                  ·
                    refine ⟨1323248546967797152398515, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14114651167656502958917493 1323248546967797152398515)
                    ·
                      rfl

theorem cell23_7731052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 1, 5].length) (baseStart_7731052 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7731052 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7731052 prefixEnd_7731052 := by exact prefixLift 7731052
  have htrace : WordTrace (prefixWord ++ tailWord_7731052) baseStart_7731052 baseEnd_7731052 := by
    simpa [prefixWord, tailWord_7731052, baseEnd_7731052] using wordTrace_append hprefix tailTrace_7731052
  have hstable : (prefixWord ++ tailWord_7731052).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7731052).length < 2 ^ (prefixWord ++ tailWord_7731052).sum := by decide
  have hdescent : baseEnd_7731052 < baseStart_7731052 := by decide
  rcases family_descends (prefixWord ++ tailWord_7731052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7731075 : List Nat := [1, 1, 1, 3, 4, 2, 1, 1, 3, 1, 5]
def baseStart_7731075 : Nat := 118140960795 + 7731075 * 2 ^ 59
def prefixEnd_7731075 : Nat := 4983230072969 + 3 ^ 40 * 7731075 * 2
def baseEnd_7731075 : Nat := 3969757450958444867207939

theorem tailTrace_7731075 : CollatzResearch.WordTrace tailWord_7731075 prefixEnd_7731075 3969757450958444867207939 := by
  unfold tailWord_7731075
  simp only [CollatzResearch.WordTrace]
  refine ⟨281975470466643112335682679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187983646977762074890455119 281975470466643112335682679)
  ·
    refine ⟨422963205699964668503524019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 281975470466643112335682679 422963205699964668503524019)
    ·
      refine ⟨634444808549947002755286029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 422963205699964668503524019 634444808549947002755286029)
      ·
        refine ⟨237916803206230126033232261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 634444808549947002755286029 237916803206230126033232261)
        ·
          refine ⟨44609400601168148631231049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 237916803206230126033232261 44609400601168148631231049)
          ·
            refine ⟨33457050450876111473423287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44609400601168148631231049 33457050450876111473423287)
            ·
              refine ⟨50185575676314167210134931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33457050450876111473423287 50185575676314167210134931)
              ·
                refine ⟨75278363514471250815202397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50185575676314167210134931 75278363514471250815202397)
                ·
                  refine ⟨28229386317926719055700899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 75278363514471250815202397 28229386317926719055700899)
                  ·
                    refine ⟨42344079476890078583551349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28229386317926719055700899 42344079476890078583551349)
                    ·
                      refine ⟨3969757450958444867207939, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42344079476890078583551349 3969757450958444867207939)
                      ·
                        rfl

theorem cell23_7731075_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 1, 1, 3, 1, 5].length) (baseStart_7731075 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7731075 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7731075 prefixEnd_7731075 := by exact prefixLift 7731075
  have htrace : WordTrace (prefixWord ++ tailWord_7731075) baseStart_7731075 baseEnd_7731075 := by
    simpa [prefixWord, tailWord_7731075, baseEnd_7731075] using wordTrace_append hprefix tailTrace_7731075
  have hstable : (prefixWord ++ tailWord_7731075).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7731075).length < 2 ^ (prefixWord ++ tailWord_7731075).sum := by decide
  have hdescent : baseEnd_7731075 < baseStart_7731075 := by decide
  rcases family_descends (prefixWord ++ tailWord_7731075) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7731086 : List Nat := [4, 1, 1, 5, 1, 1, 2, 2, 1, 5]
def baseStart_7731086 : Nat := 118140960795 + 7731086 * 2 ^ 59
def prefixEnd_7731086 : Nat := 4983230072969 + 3 ^ 40 * 7731086 * 2
def baseEnd_7731086 : Nat := 1323254366415214774723463

theorem tailTrace_7731086 : CollatzResearch.WordTrace tailWord_7731086 prefixEnd_7731086 1323254366415214774723463 := by
  unfold tailWord_7731086
  simp only [CollatzResearch.WordTrace]
  refine ⟨35246983958700407651791639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 187983914446402174142888741 35246983958700407651791639)
  ·
    refine ⟨52870475938050611477687459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35246983958700407651791639 52870475938050611477687459)
    ·
      refine ⟨79305713907075917216531189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52870475938050611477687459 79305713907075917216531189)
      ·
        refine ⟨7434910678788367239049799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 79305713907075917216531189 7434910678788367239049799)
        ·
          refine ⟨11152366018182550858574699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7434910678788367239049799 11152366018182550858574699)
          ·
            refine ⟨16728549027273826287862049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11152366018182550858574699 16728549027273826287862049)
            ·
              refine ⟨12546411770455369715896537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16728549027273826287862049 12546411770455369715896537)
              ·
                refine ⟨9409808827841527286922403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12546411770455369715896537 9409808827841527286922403)
                ·
                  refine ⟨14114713241762290930383605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9409808827841527286922403 14114713241762290930383605)
                  ·
                    refine ⟨1323254366415214774723463, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14114713241762290930383605 1323254366415214774723463)
                    ·
                      rfl

theorem cell23_7731086_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 1, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 1, 1, 2, 2, 1, 5].length) (baseStart_7731086 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7731086 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7731086 prefixEnd_7731086 := by exact prefixLift 7731086
  have htrace : WordTrace (prefixWord ++ tailWord_7731086) baseStart_7731086 baseEnd_7731086 := by
    simpa [prefixWord, tailWord_7731086, baseEnd_7731086] using wordTrace_append hprefix tailTrace_7731086
  have hstable : (prefixWord ++ tailWord_7731086).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7731086).length < 2 ^ (prefixWord ++ tailWord_7731086).sum := by decide
  have hdescent : baseEnd_7731086 < baseStart_7731086 := by decide
  rcases family_descends (prefixWord ++ tailWord_7731086) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7731089 : List Nat := [1, 2, 2, 1, 1, 1, 6, 2, 3, 2, 2]
def baseStart_7731089 : Nat := 118140960795 + 7731089 * 2 ^ 59
def prefixEnd_7731089 : Nat := 4983230072969 + 3 ^ 40 * 7731089 * 2
def baseEnd_7731089 : Nat := 3969764639687607812432875

theorem tailTrace_7731089 : CollatzResearch.WordTrace tailWord_7731089 prefixEnd_7731089 3969764639687607812432875 := by
  unfold tailWord_7731089
  simp only [CollatzResearch.WordTrace]
  refine ⟨281975981088592392726692321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187983987392394928484461547 281975981088592392726692321)
  ·
    refine ⟨211481985816444294545019241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 281975981088592392726692321 211481985816444294545019241)
    ·
      refine ⟨158611489362333220908764431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 211481985816444294545019241 158611489362333220908764431)
      ·
        refine ⟨237917234043499831363146647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 158611489362333220908764431 237917234043499831363146647)
        ·
          refine ⟨356875851065249747044719971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 237917234043499831363146647 356875851065249747044719971)
          ·
            refine ⟨535313776597874620567079957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 356875851065249747044719971 535313776597874620567079957)
            ·
              refine ⟨25092833278025372839081873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 535313776597874620567079957 25092833278025372839081873)
              ·
                refine ⟨18819624958519029629311405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25092833278025372839081873 18819624958519029629311405)
                ·
                  refine ⟨7057359359444636110991777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18819624958519029629311405 7057359359444636110991777)
                  ·
                    refine ⟨5293019519583477083243833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7057359359444636110991777 5293019519583477083243833)
                    ·
                      refine ⟨3969764639687607812432875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5293019519583477083243833 3969764639687607812432875)
                      ·
                        rfl

theorem cell23_7731089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 6, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 6, 2, 3, 2, 2].length) (baseStart_7731089 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7731089 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7731089 prefixEnd_7731089 := by exact prefixLift 7731089
  have htrace : WordTrace (prefixWord ++ tailWord_7731089) baseStart_7731089 baseEnd_7731089 := by
    simpa [prefixWord, tailWord_7731089, baseEnd_7731089] using wordTrace_append hprefix tailTrace_7731089
  have hstable : (prefixWord ++ tailWord_7731089).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7731089).length < 2 ^ (prefixWord ++ tailWord_7731089).sum := by decide
  have hdescent : baseEnd_7731089 < baseStart_7731089 := by decide
  rcases family_descends (prefixWord ++ tailWord_7731089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7731095 : List Nat := [1, 1, 3, 3, 1, 4, 1, 9]
def baseStart_7731095 : Nat := 118140960795 + 7731095 * 2 ^ 59
def prefixEnd_7731095 : Nat := 4983230072969 + 3 ^ 40 * 7731095 * 2
def baseEnd_7731095 : Nat := 147028434095242029220661

theorem tailTrace_7731095 : CollatzResearch.WordTrace tailWord_7731095 prefixEnd_7731095 147028434095242029220661 := by
  unfold tailWord_7731095
  simp only [CollatzResearch.WordTrace]
  refine ⟨281976199926570655751410739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187984133284380437167607159 281976199926570655751410739)
  ·
    refine ⟨422964299889855983627116109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 281976199926570655751410739 422964299889855983627116109)
    ·
      refine ⟨158611612458695993860168541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 422964299889855983627116109 158611612458695993860168541)
      ·
        refine ⟨59479354672010997697563203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 158611612458695993860168541 59479354672010997697563203)
        ·
          refine ⟨89219032008016496546344805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59479354672010997697563203 89219032008016496546344805)
          ·
            refine ⟨16728568501503093102439651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 89219032008016496546344805 16728568501503093102439651)
            ·
              refine ⟨25092852752254639653659477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16728568501503093102439651 25092852752254639653659477)
              ·
                refine ⟨147028434095242029220661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 25092852752254639653659477 147028434095242029220661)
                ·
                  rfl

theorem cell23_7731095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 4, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 4, 1, 9].length) (baseStart_7731095 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7731095 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7731095 prefixEnd_7731095 := by exact prefixLift 7731095
  have htrace : WordTrace (prefixWord ++ tailWord_7731095) baseStart_7731095 baseEnd_7731095 := by
    simpa [prefixWord, tailWord_7731095, baseEnd_7731095] using wordTrace_append hprefix tailTrace_7731095
  have hstable : (prefixWord ++ tailWord_7731095).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7731095).length < 2 ^ (prefixWord ++ tailWord_7731095).sum := by decide
  have hdescent : baseEnd_7731095 < baseStart_7731095 := by decide
  rcases family_descends (prefixWord ++ tailWord_7731095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7731123 : List Nat := [1, 1, 1, 2, 3, 1, 7, 2, 1, 2, 2]
def baseStart_7731123 : Nat := 118140960795 + 7731123 * 2 ^ 59
def prefixEnd_7731123 : Nat := 4983230072969 + 3 ^ 40 * 7731123 * 2
def baseEnd_7731123 : Nat := 3969782098029860679407719

theorem tailTrace_7731123 : CollatzResearch.WordTrace tailWord_7731123 prefixEnd_7731123 3969782098029860679407719 := by
  unfold tailWord_7731123
  simp only [CollatzResearch.WordTrace]
  refine ⟨281977221170469216533430023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187984814113646144355620015 281977221170469216533430023)
  ·
    refine ⟨422965831755703824800145035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 281977221170469216533430023 422965831755703824800145035)
    ·
      refine ⟨634448747633555737200217553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 422965831755703824800145035 634448747633555737200217553)
      ·
        refine ⟨475836560725166802900163165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 634448747633555737200217553 475836560725166802900163165)
        ·
          refine ⟨178438710271937551087561187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 475836560725166802900163165 178438710271937551087561187)
          ·
            refine ⟨267658065407906326631341781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 178438710271937551087561187 267658065407906326631341781)
            ·
              refine ⟨6273235907997804530422073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 267658065407906326631341781 6273235907997804530422073)
              ·
                refine ⟨4704926930998353397816555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6273235907997804530422073 4704926930998353397816555)
                ·
                  refine ⟨7057390396497530096724833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4704926930998353397816555 7057390396497530096724833)
                  ·
                    refine ⟨5293042797373147572543625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7057390396497530096724833 5293042797373147572543625)
                    ·
                      refine ⟨3969782098029860679407719, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5293042797373147572543625 3969782098029860679407719)
                      ·
                        rfl

theorem cell23_7731123_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 7, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 7, 2, 1, 2, 2].length) (baseStart_7731123 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7731123 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7731123 prefixEnd_7731123 := by exact prefixLift 7731123
  have htrace : WordTrace (prefixWord ++ tailWord_7731123) baseStart_7731123 baseEnd_7731123 := by
    simpa [prefixWord, tailWord_7731123, baseEnd_7731123] using wordTrace_append hprefix tailTrace_7731123
  have hstable : (prefixWord ++ tailWord_7731123).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7731123).length < 2 ^ (prefixWord ++ tailWord_7731123).sum := by decide
  have hdescent : baseEnd_7731123 < baseStart_7731123 := by decide
  rcases family_descends (prefixWord ++ tailWord_7731123) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7731145 : List Nat := [1, 2, 1, 1, 2, 1, 2, 4, 2, 3, 4]
def baseStart_7731145 : Nat := 118140960795 + 7731145 * 2 ^ 59
def prefixEnd_7731145 : Nat := 4983230072969 + 3 ^ 40 * 7731145 * 2
def baseEnd_7731145 : Nat := 3969793394604259593332617

theorem tailTrace_7731145 : CollatzResearch.WordTrace tailWord_7731145 prefixEnd_7731145 3969793394604259593332617 := by
  unfold tailWord_7731145
  simp only [CollatzResearch.WordTrace]
  refine ⟨281978023576389514290730889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187985349050926342860487259 281978023576389514290730889)
  ·
    refine ⟨211483517682292135718048167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 281978023576389514290730889 211483517682292135718048167)
    ·
      refine ⟨317225276523438203577072251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 211483517682292135718048167 317225276523438203577072251)
      ·
        refine ⟨475837914785157305365608377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 317225276523438203577072251 475837914785157305365608377)
        ·
          refine ⟨356878436088867979024206283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 475837914785157305365608377 356878436088867979024206283)
          ·
            refine ⟨535317654133301968536309425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 356878436088867979024206283 535317654133301968536309425)
            ·
              refine ⟨401488240599976476402232069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 535317654133301968536309425 401488240599976476402232069)
              ·
                refine ⟨75279045112495589325418513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 401488240599976476402232069 75279045112495589325418513)
                ·
                  refine ⟨56459283834371691994063885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 75279045112495589325418513 56459283834371691994063885)
                  ·
                    refine ⟨21172231437889384497773957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 56459283834371691994063885 21172231437889384497773957)
                    ·
                      refine ⟨3969793394604259593332617, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21172231437889384497773957 3969793394604259593332617)
                      ·
                        rfl

theorem cell23_7731145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 4, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 4, 2, 3, 4].length) (baseStart_7731145 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7731145 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7731145 prefixEnd_7731145 := by exact prefixLift 7731145
  have htrace : WordTrace (prefixWord ++ tailWord_7731145) baseStart_7731145 baseEnd_7731145 := by
    simpa [prefixWord, tailWord_7731145, baseEnd_7731145] using wordTrace_append hprefix tailTrace_7731145
  have hstable : (prefixWord ++ tailWord_7731145).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7731145).length < 2 ^ (prefixWord ++ tailWord_7731145).sum := by decide
  have hdescent : baseEnd_7731145 < baseStart_7731145 := by decide
  rcases family_descends (prefixWord ++ tailWord_7731145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7731179 : List Nat := [1, 1, 1, 1, 2, 3, 1, 5, 4, 2, 2]
def baseStart_7731179 : Nat := 118140960795 + 7731179 * 2 ^ 59
def prefixEnd_7731179 : Nat := 4983230072969 + 3 ^ 40 * 7731179 * 2
def baseEnd_7731179 : Nat := 3969810852946512460307461

theorem tailTrace_7731179 : CollatzResearch.WordTrace tailWord_7731179 prefixEnd_7731179 3969810852946512460307461 := by
  unfold tailWord_7731179
  simp only [CollatzResearch.WordTrace]
  refine ⟨281979263658266338097468591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187986175772177558731645727 281979263658266338097468591)
  ·
    refine ⟨422968895487399507146202887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 281979263658266338097468591 422968895487399507146202887)
    ·
      refine ⟨634453343231099260719304331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 422968895487399507146202887 634453343231099260719304331)
      ·
        refine ⟨951680014846648891078956497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 634453343231099260719304331 951680014846648891078956497)
        ·
          refine ⟨713760011134986668309217373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 951680014846648891078956497 713760011134986668309217373)
          ·
            refine ⟨267660004175620000615956515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 713760011134986668309217373 267660004175620000615956515)
            ·
              refine ⟨401490006263430000923934773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 267660004175620000615956515 401490006263430000923934773)
              ·
                refine ⟨37639688087196562586618885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 401490006263430000923934773 37639688087196562586618885)
                ·
                  refine ⟨7057441516349355484991041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 37639688087196562586618885 7057441516349355484991041)
                  ·
                    refine ⟨5293081137262016613743281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7057441516349355484991041 5293081137262016613743281)
                    ·
                      refine ⟨3969810852946512460307461, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5293081137262016613743281 3969810852946512460307461)
                      ·
                        rfl

theorem cell23_7731179_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 5, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 5, 4, 2, 2].length) (baseStart_7731179 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7731179 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7731179 prefixEnd_7731179 := by exact prefixLift 7731179
  have htrace : WordTrace (prefixWord ++ tailWord_7731179) baseStart_7731179 baseEnd_7731179 := by
    simpa [prefixWord, tailWord_7731179, baseEnd_7731179] using wordTrace_append hprefix tailTrace_7731179
  have hstable : (prefixWord ++ tailWord_7731179).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7731179).length < 2 ^ (prefixWord ++ tailWord_7731179).sum := by decide
  have hdescent : baseEnd_7731179 < baseStart_7731179 := by decide
  rcases family_descends (prefixWord ++ tailWord_7731179) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7731196 : List Nat := [2, 2, 2, 1, 2, 2, 1, 5, 2, 2, 2]
def baseStart_7731196 : Nat := 118140960795 + 7731196 * 2 ^ 59
def prefixEnd_7731196 : Nat := 4983230072969 + 3 ^ 40 * 7731196 * 2
def baseEnd_7731196 : Nat := 3969819582117638893794883

theorem tailTrace_7731196 : CollatzResearch.WordTrace tailWord_7731196 prefixEnd_7731196 3969819582117638893794883 := by
  unfold tailWord_7731196
  simp only [CollatzResearch.WordTrace]
  refine ⟨140989941849602375000418721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 187986589132803166667224961 140989941849602375000418721)
  ·
    refine ⟨105742456387201781250314041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 140989941849602375000418721 105742456387201781250314041)
    ·
      refine ⟨79306842290401335937735531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 105742456387201781250314041 79306842290401335937735531)
      ·
        refine ⟨118960263435602003906603297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79306842290401335937735531 118960263435602003906603297)
        ·
          refine ⟨89220197576701502929952473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 118960263435602003906603297 89220197576701502929952473)
          ·
            refine ⟨66915148182526127197464355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 89220197576701502929952473 66915148182526127197464355)
            ·
              refine ⟨100372722273789190796196533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66915148182526127197464355 100372722273789190796196533)
              ·
                refine ⟨9409942713167736637143425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 100372722273789190796196533 9409942713167736637143425)
                ·
                  refine ⟨7057457034875802477857569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9409942713167736637143425 7057457034875802477857569)
                  ·
                    refine ⟨5293092776156851858393177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7057457034875802477857569 5293092776156851858393177)
                    ·
                      refine ⟨3969819582117638893794883, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5293092776156851858393177 3969819582117638893794883)
                      ·
                        rfl

theorem cell23_7731196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 1, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 1, 5, 2, 2, 2].length) (baseStart_7731196 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7731196 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7731196 prefixEnd_7731196 := by exact prefixLift 7731196
  have htrace : WordTrace (prefixWord ++ tailWord_7731196) baseStart_7731196 baseEnd_7731196 := by
    simpa [prefixWord, tailWord_7731196, baseEnd_7731196] using wordTrace_append hprefix tailTrace_7731196
  have hstable : (prefixWord ++ tailWord_7731196).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7731196).length < 2 ^ (prefixWord ++ tailWord_7731196).sum := by decide
  have hdescent : baseEnd_7731196 < baseStart_7731196 := by decide
  rcases family_descends (prefixWord ++ tailWord_7731196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7731212 : List Nat := [2, 2, 1, 2, 3, 1, 1, 2, 1, 5, 3]
def baseStart_7731212 : Nat := 118140960795 + 7731212 * 2 ^ 59
def prefixEnd_7731212 : Nat := 4983230072969 + 3 ^ 40 * 7731212 * 2
def baseEnd_7731212 : Nat := 3969827797808110831194809

theorem tailTrace_7731212 : CollatzResearch.WordTrace tailWord_7731212 prefixEnd_7731212 3969827797808110831194809 := by
  unfold tailWord_7731212
  simp only [CollatzResearch.WordTrace]
  refine ⟨140990233633573392366709945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 187986978178097856488946593 140990233633573392366709945)
  ·
    refine ⟨105742675225180044275032459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 140990233633573392366709945 105742675225180044275032459)
    ·
      refine ⟨158614012837770066412548689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105742675225180044275032459 158614012837770066412548689)
      ·
        refine ⟨118960509628327549809411517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 158614012837770066412548689 118960509628327549809411517)
        ·
          refine ⟨44610191110622831178529319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 118960509628327549809411517 44610191110622831178529319)
          ·
            refine ⟨66915286665934246767793979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44610191110622831178529319 66915286665934246767793979)
            ·
              refine ⟨100372929998901370151690969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66915286665934246767793979 100372929998901370151690969)
              ·
                refine ⟨75279697499176027613768227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 100372929998901370151690969 75279697499176027613768227)
                ·
                  refine ⟨112919546248764041420652341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 75279697499176027613768227 112919546248764041420652341)
                  ·
                    refine ⟨10586207460821628883186157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 112919546248764041420652341 10586207460821628883186157)
                    ·
                      refine ⟨3969827797808110831194809, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10586207460821628883186157 3969827797808110831194809)
                      ·
                        rfl

theorem cell23_7731212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 1, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 1, 2, 1, 5, 3].length) (baseStart_7731212 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7731212 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7731212 prefixEnd_7731212 := by exact prefixLift 7731212
  have htrace : WordTrace (prefixWord ++ tailWord_7731212) baseStart_7731212 baseEnd_7731212 := by
    simpa [prefixWord, tailWord_7731212, baseEnd_7731212] using wordTrace_append hprefix tailTrace_7731212
  have hstable : (prefixWord ++ tailWord_7731212).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7731212).length < 2 ^ (prefixWord ++ tailWord_7731212).sum := by decide
  have hdescent : baseEnd_7731212 < baseStart_7731212 := by decide
  rcases family_descends (prefixWord ++ tailWord_7731212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7731229 : List Nat := [1, 4, 2, 2, 2, 1, 1, 2, 2, 3, 3]
def baseStart_7731229 : Nat := 118140960795 + 7731229 * 2 ^ 59
def prefixEnd_7731229 : Nat := 4983230072969 + 3 ^ 40 * 7731229 * 2
def baseEnd_7731229 : Nat := 3969836526979237264682231

theorem tailTrace_7731229 : CollatzResearch.WordTrace tailWord_7731229 prefixEnd_7731229 3969836526979237264682231 := by
  unfold tailWord_7731229
  simp only [CollatzResearch.WordTrace]
  refine ⟨281981087308085196636788741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187987391538723464424525827 281981087308085196636788741)
  ·
    refine ⟨52871453870265974369397889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 281981087308085196636788741 52871453870265974369397889)
    ·
      refine ⟨39653590402699480777048417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52871453870265974369397889 39653590402699480777048417)
      ·
        refine ⟨29740192802024610582786313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39653590402699480777048417 29740192802024610582786313)
        ·
          refine ⟨22305144601518457937089735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29740192802024610582786313 22305144601518457937089735)
          ·
            refine ⟨33457716902277686905634603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22305144601518457937089735 33457716902277686905634603)
            ·
              refine ⟨50186575353416530358451905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33457716902277686905634603 50186575353416530358451905)
              ·
                refine ⟨37639931515062397768838929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50186575353416530358451905 37639931515062397768838929)
                ·
                  refine ⟨28229948636296798326629197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37639931515062397768838929 28229948636296798326629197)
                  ·
                    refine ⟨10586230738611299372485949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28229948636296798326629197 10586230738611299372485949)
                    ·
                      refine ⟨3969836526979237264682231, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10586230738611299372485949 3969836526979237264682231)
                      ·
                        rfl

theorem cell23_7731229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 1, 2, 2, 3, 3].length) (baseStart_7731229 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7731229 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7731229 prefixEnd_7731229 := by exact prefixLift 7731229
  have htrace : WordTrace (prefixWord ++ tailWord_7731229) baseStart_7731229 baseEnd_7731229 := by
    simpa [prefixWord, tailWord_7731229, baseEnd_7731229] using wordTrace_append hprefix tailTrace_7731229
  have hstable : (prefixWord ++ tailWord_7731229).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7731229).length < 2 ^ (prefixWord ++ tailWord_7731229).sum := by decide
  have hdescent : baseEnd_7731229 < baseStart_7731229 := by decide
  rcases family_descends (prefixWord ++ tailWord_7731229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7731289 : List Nat := [1, 2, 1, 2, 2, 1, 5, 2, 2, 2, 3]
def baseStart_7731289 : Nat := 118140960795 + 7731289 * 2 ^ 59
def prefixEnd_7731289 : Nat := 4983230072969 + 3 ^ 40 * 7731289 * 2
def baseEnd_7731289 : Nat := 3969867335818507029931955

theorem tailTrace_7731289 : CollatzResearch.WordTrace tailWord_7731289 prefixEnd_7731289 3969867335818507029931955 := by
  unfold tailWord_7731289
  simp only [CollatzResearch.WordTrace]
  refine ⟨281983275687867826883972921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187988850458578551255981947 281983275687867826883972921)
  ·
    refine ⟨211487456765900870162979691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 281983275687867826883972921 211487456765900870162979691)
    ·
      refine ⟨317231185148851305244469537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 211487456765900870162979691 317231185148851305244469537)
      ·
        refine ⟨237923388861638478933352153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 317231185148851305244469537 237923388861638478933352153)
        ·
          refine ⟨178442541646228859200014115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 237923388861638478933352153 178442541646228859200014115)
          ·
            refine ⟨267663812469343288800021173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 178442541646228859200014115 267663812469343288800021173)
            ·
              refine ⟨25093482419000933325001985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 267663812469343288800021173 25093482419000933325001985)
              ·
                refine ⟨18820111814250699993751489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25093482419000933325001985 18820111814250699993751489)
                ·
                  refine ⟨14115083860688024995313617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18820111814250699993751489 14115083860688024995313617)
                  ·
                    refine ⟨10586312895516018746485213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14115083860688024995313617 10586312895516018746485213)
                    ·
                      refine ⟨3969867335818507029931955, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10586312895516018746485213 3969867335818507029931955)
                      ·
                        rfl

theorem cell23_7731289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 5, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 5, 2, 2, 2, 3].length) (baseStart_7731289 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7731289 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7731289 prefixEnd_7731289 := by exact prefixLift 7731289
  have htrace : WordTrace (prefixWord ++ tailWord_7731289) baseStart_7731289 baseEnd_7731289 := by
    simpa [prefixWord, tailWord_7731289, baseEnd_7731289] using wordTrace_append hprefix tailTrace_7731289
  have hstable : (prefixWord ++ tailWord_7731289).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7731289).length < 2 ^ (prefixWord ++ tailWord_7731289).sum := by decide
  have hdescent : baseEnd_7731289 < baseStart_7731289 := by decide
  rcases family_descends (prefixWord ++ tailWord_7731289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7731296 : List Nat := [2, 1, 1, 3, 2, 5, 1, 1, 3, 4]
def baseStart_7731296 : Nat := 118140960795 + 7731296 * 2 ^ 59
def prefixEnd_7731296 : Nat := 4983230072969 + 3 ^ 40 * 7731296 * 2
def baseEnd_7731296 : Nat := 1323290310061029500848141

theorem tailTrace_7731296 : CollatzResearch.WordTrace tailWord_7731296 prefixEnd_7731296 1323290310061029500848141 := by
  unfold tailWord_7731296
  simp only [CollatzResearch.WordTrace]
  refine ⟨140991765499421233539738871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 187989020665894978052985161 140991765499421233539738871)
  ·
    refine ⟨211487648249131850309608307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140991765499421233539738871 211487648249131850309608307)
    ·
      refine ⟨317231472373697775464412461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 211487648249131850309608307 317231472373697775464412461)
      ·
        refine ⟨118961802140136665799154673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 317231472373697775464412461 118961802140136665799154673)
        ·
          refine ⟨89221351605102499349366005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 118961802140136665799154673 89221351605102499349366005)
          ·
            refine ⟨8364501712978359314003063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 89221351605102499349366005 8364501712978359314003063)
            ·
              refine ⟨12546752569467538971004595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8364501712978359314003063 12546752569467538971004595)
              ·
                refine ⟨18820128854201308456506893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12546752569467538971004595 18820128854201308456506893)
                ·
                  refine ⟨7057548320325490671190085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18820128854201308456506893 7057548320325490671190085)
                  ·
                    refine ⟨1323290310061029500848141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7057548320325490671190085 1323290310061029500848141)
                    ·
                      rfl

theorem cell23_7731296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 5, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 5, 1, 1, 3, 4].length) (baseStart_7731296 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7731296 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7731296 prefixEnd_7731296 := by exact prefixLift 7731296
  have htrace : WordTrace (prefixWord ++ tailWord_7731296) baseStart_7731296 baseEnd_7731296 := by
    simpa [prefixWord, tailWord_7731296, baseEnd_7731296] using wordTrace_append hprefix tailTrace_7731296
  have hstable : (prefixWord ++ tailWord_7731296).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7731296).length < 2 ^ (prefixWord ++ tailWord_7731296).sum := by decide
  have hdescent : baseEnd_7731296 < baseStart_7731296 := by decide
  rcases family_descends (prefixWord ++ tailWord_7731296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7731309 : List Nat := [1, 5, 1, 1, 2, 1, 3, 3, 6]
def baseStart_7731309 : Nat := 118140960795 + 7731309 * 2 ^ 59
def prefixEnd_7731309 : Nat := 4983230072969 + 3 ^ 40 * 7731309 * 2
def baseEnd_7731309 : Nat := 441097511714621883520207

theorem tailTrace_7731309 : CollatzResearch.WordTrace tailWord_7731309 prefixEnd_7731309 441097511714621883520207 := by
  unfold tailWord_7731309
  simp only [CollatzResearch.WordTrace]
  refine ⟨281984005147795370299700981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187989336765196913533133987 281984005147795370299700981)
  ·
    refine ⟨26436000482605815965596967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 281984005147795370299700981 26436000482605815965596967)
    ·
      refine ⟨39654000723908723948395451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26436000482605815965596967 39654000723908723948395451)
      ·
        refine ⟨59481001085863085922593177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39654000723908723948395451 59481001085863085922593177)
        ·
          refine ⟨44610750814397314441944883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59481001085863085922593177 44610750814397314441944883)
          ·
            refine ⟨66916126221595971662917325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44610750814397314441944883 66916126221595971662917325)
            ·
              refine ⟨25093547333098489373593997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 66916126221595971662917325 25093547333098489373593997)
              ·
                refine ⟨9410080249911933515097749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25093547333098489373593997 9410080249911933515097749)
                ·
                  refine ⟨441097511714621883520207, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9410080249911933515097749 441097511714621883520207)
                  ·
                    rfl

theorem cell23_7731309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 3, 3, 6].length) (baseStart_7731309 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7731309 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7731309 prefixEnd_7731309 := by exact prefixLift 7731309
  have htrace : WordTrace (prefixWord ++ tailWord_7731309) baseStart_7731309 baseEnd_7731309 := by
    simpa [prefixWord, tailWord_7731309, baseEnd_7731309] using wordTrace_append hprefix tailTrace_7731309
  have hstable : (prefixWord ++ tailWord_7731309).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7731309).length < 2 ^ (prefixWord ++ tailWord_7731309).sum := by decide
  have hdescent : baseEnd_7731309 < baseStart_7731309 := by decide
  rcases family_descends (prefixWord ++ tailWord_7731309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7731370 : List Nat := [3, 1, 5, 1, 2, 1, 1, 2, 3, 1, 3]
def baseStart_7731370 : Nat := 118140960795 + 7731370 * 2 ^ 59
def prefixEnd_7731370 : Nat := 4983230072969 + 3 ^ 40 * 7731370 * 2
def baseEnd_7731370 : Nat := 3969908927751521213019083

theorem tailTrace_7731370 : CollatzResearch.WordTrace tailWord_7731370 prefixEnd_7731370 3969908927751521213019083 := by
  unfold tailWord_7731370
  simp only [CollatzResearch.WordTrace]
  refine ⟨70496557500143594429417891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 187990820000382918478447709 70496557500143594429417891)
  ·
    refine ⟨105744836250215391644126837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70496557500143594429417891 105744836250215391644126837)
    ·
      refine ⟨9913578398457692966636891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 105744836250215391644126837 9913578398457692966636891)
      ·
        refine ⟨14870367597686539449955337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9913578398457692966636891 14870367597686539449955337)
        ·
          refine ⟨11152775698264904587466503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14870367597686539449955337 11152775698264904587466503)
          ·
            refine ⟨16729163547397356881199755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11152775698264904587466503 16729163547397356881199755)
            ·
              refine ⟨25093745321096035321799633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16729163547397356881199755 25093745321096035321799633)
              ·
                refine ⟨18820308990822026491349725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25093745321096035321799633 18820308990822026491349725)
                ·
                  refine ⟨7057615871558259934256147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18820308990822026491349725 7057615871558259934256147)
                  ·
                    refine ⟨10586423807337389901384221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7057615871558259934256147 10586423807337389901384221)
                    ·
                      refine ⟨3969908927751521213019083, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10586423807337389901384221 3969908927751521213019083)
                      ·
                        rfl

theorem cell23_7731370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 2, 1, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 2, 1, 1, 2, 3, 1, 3].length) (baseStart_7731370 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7731370 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7731370 prefixEnd_7731370 := by exact prefixLift 7731370
  have htrace : WordTrace (prefixWord ++ tailWord_7731370) baseStart_7731370 baseEnd_7731370 := by
    simpa [prefixWord, tailWord_7731370, baseEnd_7731370] using wordTrace_append hprefix tailTrace_7731370
  have hstable : (prefixWord ++ tailWord_7731370).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7731370).length < 2 ^ (prefixWord ++ tailWord_7731370).sum := by decide
  have hdescent : baseEnd_7731370 < baseStart_7731370 := by decide
  rcases family_descends (prefixWord ++ tailWord_7731370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7731372 : List Nat := [2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 6]
def baseStart_7731372 : Nat := 118140960795 + 7731372 * 2 ^ 59
def prefixEnd_7731372 : Nat := 4983230072969 + 3 ^ 40 * 7731372 * 2
def baseEnd_7731372 : Nat := 3969909954712830205194073

theorem tailTrace_7731372 : CollatzResearch.WordTrace tailWord_7731372 prefixEnd_7731372 3969909954712830205194073 := by
  unfold tailWord_7731372
  simp only [CollatzResearch.WordTrace]
  refine ⟨140993151473283566029622185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 187990868631044754706162913 140993151473283566029622185)
  ·
    refine ⟨105744863604962674522216639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 140993151473283566029622185 105744863604962674522216639)
    ·
      refine ⟨158617295407444011783324959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105744863604962674522216639 158617295407444011783324959)
      ·
        refine ⟨237925943111166017674987439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 158617295407444011783324959 237925943111166017674987439)
        ·
          refine ⟨356888914666749026512481159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 237925943111166017674987439 356888914666749026512481159)
          ·
            refine ⟨535333372000123539768721739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 356888914666749026512481159 535333372000123539768721739)
            ·
              refine ⟨803000058000185309653082609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 535333372000123539768721739 803000058000185309653082609)
              ·
                refine ⟨602250043500138982239811957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 803000058000185309653082609 602250043500138982239811957)
                ·
                  refine ⟨56460941578138029584982371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 602250043500138982239811957 56460941578138029584982371)
                  ·
                    refine ⟨84691412367207044377473557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 56460941578138029584982371 84691412367207044377473557)
                    ·
                      refine ⟨3969909954712830205194073, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 84691412367207044377473557 3969909954712830205194073)
                      ·
                        rfl

theorem cell23_7731372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 6].length) (baseStart_7731372 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7731372 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7731372 prefixEnd_7731372 := by exact prefixLift 7731372
  have htrace : WordTrace (prefixWord ++ tailWord_7731372) baseStart_7731372 baseEnd_7731372 := by
    simpa [prefixWord, tailWord_7731372, baseEnd_7731372] using wordTrace_append hprefix tailTrace_7731372
  have hstable : (prefixWord ++ tailWord_7731372).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7731372).length < 2 ^ (prefixWord ++ tailWord_7731372).sum := by decide
  have hdescent : baseEnd_7731372 < baseStart_7731372 := by decide
  rcases family_descends (prefixWord ++ tailWord_7731372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7731390 : List Nat := [4, 2, 1, 1, 4, 2, 2, 1, 1, 5]
def baseStart_7731390 : Nat := 118140960795 + 7731390 * 2 ^ 59
def prefixEnd_7731390 : Nat := 4983230072969 + 3 ^ 40 * 7731390 * 2
def baseEnd_7731390 : Nat := 1323306399121537044922997

theorem tailTrace_7731390 : CollatzResearch.WordTrace tailWord_7731390 prefixEnd_7731390 1323306399121537044922997 := by
  unfold tailWord_7731390
  simp only [CollatzResearch.WordTrace]
  refine ⟨35248369932562740141674953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 187991306307001280755599749 35248369932562740141674953)
  ·
    refine ⟨26436277449422055106256215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35248369932562740141674953 26436277449422055106256215)
    ·
      refine ⟨39654416174133082659384323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26436277449422055106256215 39654416174133082659384323)
      ·
        refine ⟨59481624261199623989076485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39654416174133082659384323 59481624261199623989076485)
        ·
          refine ⟨11152804548974929497951841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 59481624261199623989076485 11152804548974929497951841)
          ·
            refine ⟨8364603411731197123463881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11152804548974929497951841 8364603411731197123463881)
            ·
              refine ⟨6273452558798397842597911, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8364603411731197123463881 6273452558798397842597911)
              ·
                refine ⟨9410178838197596763896867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6273452558798397842597911 9410178838197596763896867)
                ·
                  refine ⟨14115268257296395145845301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9410178838197596763896867 14115268257296395145845301)
                  ·
                    refine ⟨1323306399121537044922997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14115268257296395145845301 1323306399121537044922997)
                    ·
                      rfl

theorem cell23_7731390_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 4, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 4, 2, 2, 1, 1, 5].length) (baseStart_7731390 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7731390 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7731390 prefixEnd_7731390 := by exact prefixLift 7731390
  have htrace : WordTrace (prefixWord ++ tailWord_7731390) baseStart_7731390 baseEnd_7731390 := by
    simpa [prefixWord, tailWord_7731390, baseEnd_7731390] using wordTrace_append hprefix tailTrace_7731390
  have hstable : (prefixWord ++ tailWord_7731390).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7731390).length < 2 ^ (prefixWord ++ tailWord_7731390).sum := by decide
  have hdescent : baseEnd_7731390 < baseStart_7731390 := by decide
  rcases family_descends (prefixWord ++ tailWord_7731390) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7731409 : List Nat := [1, 2, 2, 1, 2, 2, 2, 2, 3, 3, 3]
def baseStart_7731409 : Nat := 118140960795 + 7731409 * 2 ^ 59
def prefixEnd_7731409 : Nat := 4983230072969 + 3 ^ 40 * 7731409 * 2
def baseEnd_7731409 : Nat := 3969928953497046560431403

theorem tailTrace_7731409 : CollatzResearch.WordTrace tailWord_7731409 prefixEnd_7731409 3969928953497046560431403 := by
  unfold tailWord_7731409
  simp only [CollatzResearch.WordTrace]
  refine ⟨281987652447433087378341281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187991768298288724918894187 281987652447433087378341281)
  ·
    refine ⟨211490739335574815533755961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 281987652447433087378341281 211490739335574815533755961)
    ·
      refine ⟨158618054501681111650316971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 211490739335574815533755961 158618054501681111650316971)
      ·
        refine ⟨237927081752521667475475457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 158618054501681111650316971 237927081752521667475475457)
        ·
          refine ⟨178445311314391250606606593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 237927081752521667475475457 178445311314391250606606593)
          ·
            refine ⟨133833983485793437954954945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 178445311314391250606606593 133833983485793437954954945)
            ·
              refine ⟨100375487614345078466216209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 133833983485793437954954945 100375487614345078466216209)
              ·
                refine ⟨75281615710758808849662157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 100375487614345078466216209 75281615710758808849662157)
                ·
                  refine ⟨28230605891534553318623309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 75281615710758808849662157 28230605891534553318623309)
                  ·
                    refine ⟨10586477209325457494483741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28230605891534553318623309 10586477209325457494483741)
                    ·
                      refine ⟨3969928953497046560431403, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10586477209325457494483741 3969928953497046560431403)
                      ·
                        rfl

theorem cell23_7731409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 2, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 2, 2, 3, 3, 3].length) (baseStart_7731409 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7731409 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7731409 prefixEnd_7731409 := by exact prefixLift 7731409
  have htrace : WordTrace (prefixWord ++ tailWord_7731409) baseStart_7731409 baseEnd_7731409 := by
    simpa [prefixWord, tailWord_7731409, baseEnd_7731409] using wordTrace_append hprefix tailTrace_7731409
  have hstable : (prefixWord ++ tailWord_7731409).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7731409).length < 2 ^ (prefixWord ++ tailWord_7731409).sum := by decide
  have hdescent : baseEnd_7731409 < baseStart_7731409 := by decide
  rcases family_descends (prefixWord ++ tailWord_7731409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7731410 : List Nat := [3, 2, 2, 2, 1, 3, 2, 1, 3, 2, 2]
def baseStart_7731410 : Nat := 118140960795 + 7731410 * 2 ^ 59
def prefixEnd_7731410 : Nat := 4983230072969 + 3 ^ 40 * 7731410 * 2
def baseEnd_7731410 : Nat := 3969929466977701056518899

theorem tailTrace_7731410 : CollatzResearch.WordTrace tailWord_7731410 prefixEnd_7731410 3969929466977701056518899 := by
  unfold tailWord_7731410
  simp only [CollatzResearch.WordTrace]
  refine ⟨70496922230107366137281921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 187991792613619643032751789 70496922230107366137281921)
  ·
    refine ⟨52872691672580524602961441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70496922230107366137281921 52872691672580524602961441)
    ·
      refine ⟨39654518754435393452221081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52872691672580524602961441 39654518754435393452221081)
      ·
        refine ⟨29740889065826545089165811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39654518754435393452221081 29740889065826545089165811)
        ·
          refine ⟨44611333598739817633748717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29740889065826545089165811 44611333598739817633748717)
          ·
            refine ⟨16729250099527431612655769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44611333598739817633748717 16729250099527431612655769)
            ·
              refine ⟨12546937574645573709491827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16729250099527431612655769 12546937574645573709491827)
              ·
                refine ⟨18820406361968360564237741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12546937574645573709491827 18820406361968360564237741)
                ·
                  refine ⟨7057652385738135211589153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18820406361968360564237741 7057652385738135211589153)
                  ·
                    refine ⟨5293239289303601408691865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7057652385738135211589153 5293239289303601408691865)
                    ·
                      refine ⟨3969929466977701056518899, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5293239289303601408691865 3969929466977701056518899)
                      ·
                        rfl

theorem cell23_7731410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 3, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 3, 2, 1, 3, 2, 2].length) (baseStart_7731410 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7731410 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7731410 prefixEnd_7731410 := by exact prefixLift 7731410
  have htrace : WordTrace (prefixWord ++ tailWord_7731410) baseStart_7731410 baseEnd_7731410 := by
    simpa [prefixWord, tailWord_7731410, baseEnd_7731410] using wordTrace_append hprefix tailTrace_7731410
  have hstable : (prefixWord ++ tailWord_7731410).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7731410).length < 2 ^ (prefixWord ++ tailWord_7731410).sum := by decide
  have hdescent : baseEnd_7731410 < baseStart_7731410 := by decide
  rcases family_descends (prefixWord ++ tailWord_7731410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7731420 : List Nat := [2, 2, 5, 2, 1, 2, 1, 1, 1, 6]
def baseStart_7731420 : Nat := 118140960795 + 7731420 * 2 ^ 59
def prefixEnd_7731420 : Nat := 4983230072969 + 3 ^ 40 * 7731420 * 2
def baseEnd_7731420 : Nat := 1323311533928082005797951

theorem tailTrace_7731420 : CollatzResearch.WordTrace tailWord_7731420 prefixEnd_7731420 1323311533928082005797951 := by
  unfold tailWord_7731420
  simp only [CollatzResearch.WordTrace]
  refine ⟨140994026825196618128495857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 187992035766928824171327809 140994026825196618128495857)
  ·
    refine ⟨105745520118897463596371893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 140994026825196618128495857 105745520118897463596371893)
    ·
      refine ⟨9913642511146637212159865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 105745520118897463596371893 9913642511146637212159865)
      ·
        refine ⟨7435231883359977909119899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9913642511146637212159865 7435231883359977909119899)
        ·
          refine ⟨11152847825039966863679849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7435231883359977909119899 11152847825039966863679849)
          ·
            refine ⟨8364635868779975147759887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11152847825039966863679849 8364635868779975147759887)
            ·
              refine ⟨12546953803169962721639831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8364635868779975147759887 12546953803169962721639831)
              ·
                refine ⟨18820430704754944082459747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12546953803169962721639831 18820430704754944082459747)
                ·
                  refine ⟨28230646057132416123689621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18820430704754944082459747 28230646057132416123689621)
                  ·
                    refine ⟨1323311533928082005797951, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28230646057132416123689621 1323311533928082005797951)
                    ·
                      rfl

theorem cell23_7731420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 1, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 1, 2, 1, 1, 1, 6].length) (baseStart_7731420 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7731420 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7731420 prefixEnd_7731420 := by exact prefixLift 7731420
  have htrace : WordTrace (prefixWord ++ tailWord_7731420) baseStart_7731420 baseEnd_7731420 := by
    simpa [prefixWord, tailWord_7731420, baseEnd_7731420] using wordTrace_append hprefix tailTrace_7731420
  have hstable : (prefixWord ++ tailWord_7731420).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7731420).length < 2 ^ (prefixWord ++ tailWord_7731420).sum := by decide
  have hdescent : baseEnd_7731420 < baseStart_7731420 := by decide
  rcases family_descends (prefixWord ++ tailWord_7731420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7731439 : List Nat := [1, 1, 2, 1, 6, 1, 1, 1, 2, 2, 5]
def baseStart_7731439 : Nat := 118140960795 + 7731439 * 2 ^ 59
def prefixEnd_7731439 : Nat := 4983230072969 + 3 ^ 40 * 7731439 * 2
def baseEnd_7731439 : Nat := 3969944357916681443056265

theorem tailTrace_7731439 : CollatzResearch.WordTrace tailWord_7731439 prefixEnd_7731439 3969944357916681443056265 := by
  unfold tailWord_7731439
  simp only [CollatzResearch.WordTrace]
  refine ⟨281988746637324402501933371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187992497758216268334622247 281988746637324402501933371)
  ·
    refine ⟨422983119955986603752900057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 281988746637324402501933371 422983119955986603752900057)
    ·
      refine ⟨317237339966989952814675043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 422983119955986603752900057 317237339966989952814675043)
      ·
        refine ⟨475856009950484929222012565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 317237339966989952814675043 475856009950484929222012565)
        ·
          refine ⟨22305750466428981057281839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 475856009950484929222012565 22305750466428981057281839)
          ·
            refine ⟨33458625699643471585922759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22305750466428981057281839 33458625699643471585922759)
            ·
              refine ⟨50187938549465207378884139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33458625699643471585922759 50187938549465207378884139)
              ·
                refine ⟨75281907824197811068326209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50187938549465207378884139 75281907824197811068326209)
                ·
                  refine ⟨56461430868148358301244657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 75281907824197811068326209 56461430868148358301244657)
                  ·
                    refine ⟨42346073151111268725933493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 56461430868148358301244657 42346073151111268725933493)
                    ·
                      refine ⟨3969944357916681443056265, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42346073151111268725933493 3969944357916681443056265)
                      ·
                        rfl

theorem cell23_7731439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 1, 1, 2, 2, 5].length) (baseStart_7731439 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7731439 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7731439 prefixEnd_7731439 := by exact prefixLift 7731439
  have htrace : WordTrace (prefixWord ++ tailWord_7731439) baseStart_7731439 baseEnd_7731439 := by
    simpa [prefixWord, tailWord_7731439, baseEnd_7731439] using wordTrace_append hprefix tailTrace_7731439
  have hstable : (prefixWord ++ tailWord_7731439).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7731439).length < 2 ^ (prefixWord ++ tailWord_7731439).sum := by decide
  have hdescent : baseEnd_7731439 < baseStart_7731439 := by decide
  rcases family_descends (prefixWord ++ tailWord_7731439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7731489 : List Nat := [1, 2, 3, 2, 1, 1, 2, 4, 7]
def baseStart_7731489 : Nat := 118140960795 + 7731489 * 2 ^ 59
def prefixEnd_7731489 : Nat := 4983230072969 + 3 ^ 40 * 7731489 * 2
def baseEnd_7731489 : Nat := 441107781327711805270115

theorem tailTrace_7731489 : CollatzResearch.WordTrace tailWord_7731489 prefixEnd_7731489 441107781327711805270115 := by
  unfold tailWord_7731489
  simp only [CollatzResearch.WordTrace]
  refine ⟨281990570287143261041253521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187993713524762174027502347 281990570287143261041253521)
  ·
    refine ⟨211492927715357445780940141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 281990570287143261041253521 211492927715357445780940141)
    ·
      refine ⟨79309847893259042167852553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 211492927715357445780940141 79309847893259042167852553)
      ·
        refine ⟨59482385919944281625889415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79309847893259042167852553 59482385919944281625889415)
        ·
          refine ⟨89223578879916422438834123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59482385919944281625889415 89223578879916422438834123)
          ·
            refine ⟨133835368319874633658251185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89223578879916422438834123 133835368319874633658251185)
            ·
              refine ⟨100376526239905975243688389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 133835368319874633658251185 100376526239905975243688389)
              ·
                refine ⟨18820598669982370358191573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 100376526239905975243688389 18820598669982370358191573)
                ·
                  refine ⟨441107781327711805270115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18820598669982370358191573 441107781327711805270115)
                  ·
                    rfl

theorem cell23_7731489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 2, 4, 7].length) (baseStart_7731489 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7731489 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7731489 prefixEnd_7731489 := by exact prefixLift 7731489
  have htrace : WordTrace (prefixWord ++ tailWord_7731489) baseStart_7731489 baseEnd_7731489 := by
    simpa [prefixWord, tailWord_7731489, baseEnd_7731489] using wordTrace_append hprefix tailTrace_7731489
  have hstable : (prefixWord ++ tailWord_7731489).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7731489).length < 2 ^ (prefixWord ++ tailWord_7731489).sum := by decide
  have hdescent : baseEnd_7731489 < baseStart_7731489 := by decide
  rcases family_descends (prefixWord ++ tailWord_7731489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7731516 : List Nat := [2, 2, 2, 2, 1, 2, 2, 2, 2, 3, 3]
def baseStart_7731516 : Nat := 118140960795 + 7731516 * 2 ^ 59
def prefixEnd_7731516 : Nat := 4983230072969 + 3 ^ 40 * 7731516 * 2
def baseEnd_7731516 : Nat := 3969983895927077641793411

theorem tailTrace_7731516 : CollatzResearch.WordTrace tailWord_7731516 prefixEnd_7731516 3969983895927077641793411 := by
  unfold tailWord_7731516
  simp only [CollatzResearch.WordTrace]
  refine ⟨140995777529022722326243201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 187994370038696963101657601 140995777529022722326243201)
  ·
    refine ⟨105746833146767041744682401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 140995777529022722326243201 105746833146767041744682401)
    ·
      refine ⟨79310124860075281308511801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 105746833146767041744682401 79310124860075281308511801)
      ·
        refine ⟨59482593645056460981383851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79310124860075281308511801 59482593645056460981383851)
        ·
          refine ⟨89223890467584691472075777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59482593645056460981383851 89223890467584691472075777)
          ·
            refine ⟨66917917850688518604056833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 89223890467584691472075777 66917917850688518604056833)
            ·
              refine ⟨50188438388016388953042625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66917917850688518604056833 50188438388016388953042625)
              ·
                refine ⟨37641328791012291714781969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50188438388016388953042625 37641328791012291714781969)
                ·
                  refine ⟨28230996593259218786086477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37641328791012291714781969 28230996593259218786086477)
                  ·
                    refine ⟨10586623722472207044782429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28230996593259218786086477 10586623722472207044782429)
                    ·
                      refine ⟨3969983895927077641793411, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10586623722472207044782429 3969983895927077641793411)
                      ·
                        rfl

theorem cell23_7731516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 2, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 2, 2, 2, 3, 3].length) (baseStart_7731516 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7731516 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7731516 prefixEnd_7731516 := by exact prefixLift 7731516
  have htrace : WordTrace (prefixWord ++ tailWord_7731516) baseStart_7731516 baseEnd_7731516 := by
    simpa [prefixWord, tailWord_7731516, baseEnd_7731516] using wordTrace_append hprefix tailTrace_7731516
  have hstable : (prefixWord ++ tailWord_7731516).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7731516).length < 2 ^ (prefixWord ++ tailWord_7731516).sum := by decide
  have hdescent : baseEnd_7731516 < baseStart_7731516 := by decide
  rcases family_descends (prefixWord ++ tailWord_7731516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7731523 : List Nat := [1, 1, 1, 3, 1, 3, 6, 2, 5]
def baseStart_7731523 : Nat := 118140960795 + 7731523 * 2 ^ 59
def prefixEnd_7731523 : Nat := 4983230072969 + 3 ^ 40 * 7731523 * 2
def baseEnd_7731523 : Nat := 441109721143517679378431

theorem tailTrace_7731523 : CollatzResearch.WordTrace tailWord_7731523 prefixEnd_7731523 441109721143517679378431 := by
  unfold tailWord_7731523
  simp only [CollatzResearch.WordTrace]
  refine ⟨281991810369020084847991223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187994540246013389898660815 281991810369020084847991223)
  ·
    refine ⟨422987715553530127271986835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 281991810369020084847991223 422987715553530127271986835)
    ·
      refine ⟨634481573330295190907980253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 422987715553530127271986835 634481573330295190907980253)
      ·
        refine ⟨237930589998860696590492595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 634481573330295190907980253 237930589998860696590492595)
        ·
          refine ⟨356895884998291044885738893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 237930589998860696590492595 356895884998291044885738893)
          ·
            refine ⟨133835956874359141832152085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 356895884998291044885738893 133835956874359141832152085)
            ·
              refine ⟨6273560478485584773382129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 133835956874359141832152085 6273560478485584773382129)
              ·
                refine ⟨4705170358864188580036597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6273560478485584773382129 4705170358864188580036597)
                ·
                  refine ⟨441109721143517679378431, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4705170358864188580036597 441109721143517679378431)
                  ·
                    rfl

theorem cell23_7731523_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 6, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 6, 2, 5].length) (baseStart_7731523 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7731523 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7731523 prefixEnd_7731523 := by exact prefixLift 7731523
  have htrace : WordTrace (prefixWord ++ tailWord_7731523) baseStart_7731523 baseEnd_7731523 := by
    simpa [prefixWord, tailWord_7731523, baseEnd_7731523] using wordTrace_append hprefix tailTrace_7731523
  have hstable : (prefixWord ++ tailWord_7731523).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7731523).length < 2 ^ (prefixWord ++ tailWord_7731523).sum := by decide
  have hdescent : baseEnd_7731523 < baseStart_7731523 := by decide
  rcases family_descends (prefixWord ++ tailWord_7731523) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7731556 : List Nat := [2, 3, 1, 1, 3, 1, 3, 1, 1, 3, 4]
def baseStart_7731556 : Nat := 118140960795 + 7731556 * 2 ^ 59
def prefixEnd_7731556 : Nat := 4983230072969 + 3 ^ 40 * 7731556 * 2
def baseEnd_7731556 : Nat := 3970004435153257485293227

theorem tailTrace_7731556 : CollatzResearch.WordTrace tailWord_7731556 prefixEnd_7731556 3970004435153257485293227 := by
  unfold tailWord_7731556
  simp only [CollatzResearch.WordTrace]
  refine ⟨140996506988950265741971261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 187995342651933687655961681 140996506988950265741971261)
  ·
    refine ⟨52873690120856349653239223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 140996506988950265741971261 52873690120856349653239223)
    ·
      refine ⟨79310535181284524479858835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52873690120856349653239223 79310535181284524479858835)
      ·
        refine ⟨118965802771926786719788253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79310535181284524479858835 118965802771926786719788253)
        ·
          refine ⟨44612176039472545019920595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 118965802771926786719788253 44612176039472545019920595)
          ·
            refine ⟨66918264059208817529880893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44612176039472545019920595 66918264059208817529880893)
            ·
              refine ⟨25094349022203306573705335, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 66918264059208817529880893 25094349022203306573705335)
              ·
                refine ⟨37641523533304959860558003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25094349022203306573705335 37641523533304959860558003)
                ·
                  refine ⟨56462285299957439790837005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37641523533304959860558003 56462285299957439790837005)
                  ·
                    refine ⟨21173356987484039921563877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 56462285299957439790837005 21173356987484039921563877)
                    ·
                      refine ⟨3970004435153257485293227, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21173356987484039921563877 3970004435153257485293227)
                      ·
                        rfl

theorem cell23_7731556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 3, 1, 1, 3, 4].length) (baseStart_7731556 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7731556 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7731556 prefixEnd_7731556 := by exact prefixLift 7731556
  have htrace : WordTrace (prefixWord ++ tailWord_7731556) baseStart_7731556 baseEnd_7731556 := by
    simpa [prefixWord, tailWord_7731556, baseEnd_7731556] using wordTrace_append hprefix tailTrace_7731556
  have hstable : (prefixWord ++ tailWord_7731556).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7731556).length < 2 ^ (prefixWord ++ tailWord_7731556).sum := by decide
  have hdescent : baseEnd_7731556 < baseStart_7731556 := by decide
  rcases family_descends (prefixWord ++ tailWord_7731556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7731680 : List Nat := [2, 1, 1, 3, 1, 1, 7, 1, 1, 1, 4]
def baseStart_7731680 : Nat := 118140960795 + 7731680 * 2 ^ 59
def prefixEnd_7731680 : Nat := 4983230072969 + 3 ^ 40 * 7731680 * 2
def baseEnd_7731680 : Nat := 3970068106754415000142657

theorem tailTrace_7731680 : CollatzResearch.WordTrace tailWord_7731680 prefixEnd_7731680 3970068106754415000142657 := by
  unfold tailWord_7731680
  simp only [CollatzResearch.WordTrace]
  refine ⟨140998768314725650330728247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 187998357752967533774304329 140998768314725650330728247)
  ·
    refine ⟨211498152472088475496092371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140998768314725650330728247 211498152472088475496092371)
    ·
      refine ⟨317247228708132713244138557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 211498152472088475496092371 317247228708132713244138557)
      ·
        refine ⟨118967710765549767466551959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 317247228708132713244138557 118967710765549767466551959)
        ·
          refine ⟨178451566148324651199827939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 118967710765549767466551959 178451566148324651199827939)
          ·
            refine ⟨267677349222486976799741909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 178451566148324651199827939 267677349222486976799741909)
            ·
              refine ⟨6273687872402038518743951, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 267677349222486976799741909 6273687872402038518743951)
              ·
                refine ⟨9410531808603057778115927, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6273687872402038518743951 9410531808603057778115927)
                ·
                  refine ⟨14115797712904586667173891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9410531808603057778115927 14115797712904586667173891)
                  ·
                    refine ⟨21173696569356880000760837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14115797712904586667173891 21173696569356880000760837)
                    ·
                      refine ⟨3970068106754415000142657, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21173696569356880000760837 3970068106754415000142657)
                      ·
                        rfl

theorem cell23_7731680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 7, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 7, 1, 1, 1, 4].length) (baseStart_7731680 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7731680 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7731680 prefixEnd_7731680 := by exact prefixLift 7731680
  have htrace : WordTrace (prefixWord ++ tailWord_7731680) baseStart_7731680 baseEnd_7731680 := by
    simpa [prefixWord, tailWord_7731680, baseEnd_7731680] using wordTrace_append hprefix tailTrace_7731680
  have hstable : (prefixWord ++ tailWord_7731680).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7731680).length < 2 ^ (prefixWord ++ tailWord_7731680).sum := by decide
  have hdescent : baseEnd_7731680 < baseStart_7731680 := by decide
  rcases family_descends (prefixWord ++ tailWord_7731680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7731690 : List Nat := [3, 1, 3, 1, 3, 1, 1, 4, 2, 4]
def baseStart_7731690 : Nat := 118140960795 + 7731690 * 2 ^ 59
def prefixEnd_7731690 : Nat := 4983230072969 + 3 ^ 40 * 7731690 * 2
def baseEnd_7731690 : Nat := 1323357747186986653672537

theorem tailTrace_7731690 : CollatzResearch.WordTrace tailWord_7731690 prefixEnd_7731690 1323357747186986653672537 := by
  unfold tailWord_7731690
  simp only [CollatzResearch.WordTrace]
  refine ⟨70499475339853768092330131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 187998600906276714912880349 70499475339853768092330131)
  ·
    refine ⟨105749213009780652138495197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70499475339853768092330131 105749213009780652138495197)
    ·
      refine ⟨39655954878667744551935699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 105749213009780652138495197 39655954878667744551935699)
      ·
        refine ⟨59483932318001616827903549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39655954878667744551935699 59483932318001616827903549)
        ·
          refine ⟨22306474619250606310463831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 59483932318001616827903549 22306474619250606310463831)
          ·
            refine ⟨33459711928875909465695747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22306474619250606310463831 33459711928875909465695747)
            ·
              refine ⟨50189567893313864198543621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33459711928875909465695747 50189567893313864198543621)
              ·
                refine ⟨9410543979996349537226929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 50189567893313864198543621 9410543979996349537226929)
                ·
                  refine ⟨7057907984997262152920197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9410543979996349537226929 7057907984997262152920197)
                  ·
                    refine ⟨1323357747186986653672537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7057907984997262152920197 1323357747186986653672537)
                    ·
                      rfl

theorem cell23_7731690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 1, 4, 2, 4].length) (baseStart_7731690 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7731690 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7731690 prefixEnd_7731690 := by exact prefixLift 7731690
  have htrace : WordTrace (prefixWord ++ tailWord_7731690) baseStart_7731690 baseEnd_7731690 := by
    simpa [prefixWord, tailWord_7731690, baseEnd_7731690] using wordTrace_append hprefix tailTrace_7731690
  have hstable : (prefixWord ++ tailWord_7731690).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7731690).length < 2 ^ (prefixWord ++ tailWord_7731690).sum := by decide
  have hdescent : baseEnd_7731690 < baseStart_7731690 := by decide
  rcases family_descends (prefixWord ++ tailWord_7731690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7731718 : List Nat := [6, 2, 1, 1, 1, 3, 1, 1, 2, 3, 2]
def baseStart_7731718 : Nat := 118140960795 + 7731718 * 2 ^ 59
def prefixEnd_7731718 : Nat := 4983230072969 + 3 ^ 40 * 7731718 * 2
def baseEnd_7731718 : Nat := 3970087619019285851467483

theorem tailTrace_7731718 : CollatzResearch.WordTrace tailWord_7731718 prefixEnd_7731718 3970087619019285851467483 := by
  unfold tailWord_7731718
  simp only [CollatzResearch.WordTrace]
  refine ⟨8812466331353551035979369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 187999281735542422100893205 8812466331353551035979369)
  ·
    refine ⟨6609349748515163276984527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8812466331353551035979369 6609349748515163276984527)
    ·
      refine ⟨9914024622772744915476791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6609349748515163276984527 9914024622772744915476791)
      ·
        refine ⟨14871036934159117373215187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9914024622772744915476791 14871036934159117373215187)
        ·
          refine ⟨22306555401238676059822781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14871036934159117373215187 22306555401238676059822781)
          ·
            refine ⟨8364958275464503522433543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22306555401238676059822781 8364958275464503522433543)
            ·
              refine ⟨12547437413196755283650315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8364958275464503522433543 12547437413196755283650315)
              ·
                refine ⟨18821156119795132925475473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12547437413196755283650315 18821156119795132925475473)
                ·
                  refine ⟨14115867089846349694106605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18821156119795132925475473 14115867089846349694106605)
                  ·
                    refine ⟨5293450158692381135289977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14115867089846349694106605 5293450158692381135289977)
                    ·
                      refine ⟨3970087619019285851467483, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5293450158692381135289977 3970087619019285851467483)
                      ·
                        rfl

theorem cell23_7731718_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 3, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 3, 1, 1, 2, 3, 2].length) (baseStart_7731718 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7731718 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7731718 prefixEnd_7731718 := by exact prefixLift 7731718
  have htrace : WordTrace (prefixWord ++ tailWord_7731718) baseStart_7731718 baseEnd_7731718 := by
    simpa [prefixWord, tailWord_7731718, baseEnd_7731718] using wordTrace_append hprefix tailTrace_7731718
  have hstable : (prefixWord ++ tailWord_7731718).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7731718).length < 2 ^ (prefixWord ++ tailWord_7731718).sum := by decide
  have hdescent : baseEnd_7731718 < baseStart_7731718 := by decide
  rcases family_descends (prefixWord ++ tailWord_7731718) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7731747 : List Nat := [1, 1, 1, 4, 4, 1, 3, 2, 2, 1, 3]
def baseStart_7731747 : Nat := 118140960795 + 7731747 * 2 ^ 59
def prefixEnd_7731747 : Nat := 4983230072969 + 3 ^ 40 * 7731747 * 2
def baseEnd_7731747 : Nat := 3970102509958266238004849

theorem tailTrace_7731747 : CollatzResearch.WordTrace tailWord_7731747 prefixEnd_7731747 3970102509958266238004849 := by
  unfold tailWord_7731747
  simp only [CollatzResearch.WordTrace]
  refine ⟨281999980320208571104145495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187999986880139047402763663 281999980320208571104145495)
  ·
    refine ⟨422999970480312856656218243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 281999980320208571104145495 422999970480312856656218243)
    ·
      refine ⟨634499955720469284984327365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 422999970480312856656218243 634499955720469284984327365)
      ·
        refine ⟨118968741697587990934561381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 634499955720469284984327365 118968741697587990934561381)
        ·
          refine ⟨22306639068297748300230259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 118968741697587990934561381 22306639068297748300230259)
          ·
            refine ⟨33459958602446622450345389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22306639068297748300230259 33459958602446622450345389)
            ·
              refine ⟨12547484475917483418879521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33459958602446622450345389 12547484475917483418879521)
              ·
                refine ⟨9410613356938112564159641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12547484475917483418879521 9410613356938112564159641)
                ·
                  refine ⟨7057960017703584423119731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9410613356938112564159641 7057960017703584423119731)
                  ·
                    refine ⟨10586940026555376634679597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7057960017703584423119731 10586940026555376634679597)
                    ·
                      refine ⟨3970102509958266238004849, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10586940026555376634679597 3970102509958266238004849)
                      ·
                        rfl

theorem cell23_7731747_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 3, 2, 2, 1, 3].length) (baseStart_7731747 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7731747 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7731747 prefixEnd_7731747 := by exact prefixLift 7731747
  have htrace : WordTrace (prefixWord ++ tailWord_7731747) baseStart_7731747 baseEnd_7731747 := by
    simpa [prefixWord, tailWord_7731747, baseEnd_7731747] using wordTrace_append hprefix tailTrace_7731747
  have hstable : (prefixWord ++ tailWord_7731747).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7731747).length < 2 ^ (prefixWord ++ tailWord_7731747).sum := by decide
  have hdescent : baseEnd_7731747 < baseStart_7731747 := by decide
  rcases family_descends (prefixWord ++ tailWord_7731747) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7731821 : List Nat := [1, 5, 1, 1, 3, 1, 4, 1, 2, 2, 2]
def baseStart_7731821 : Nat := 118140960795 + 7731821 * 2 ^ 59
def prefixEnd_7731821 : Nat := 4983230072969 + 3 ^ 40 * 7731821 * 2
def baseEnd_7731821 : Nat := 3970140507526698948479509

theorem tailTrace_7731821 : CollatzResearch.WordTrace tailWord_7731821 prefixEnd_7731821 3970140507526698948479509 := by
  unfold tailWord_7731821
  simp only [CollatzResearch.WordTrace]
  refine ⟨282002679321940481742339317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188001786214626987828226211 282002679321940481742339317)
  ·
    refine ⟨26437751186431920163344311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 282002679321940481742339317 26437751186431920163344311)
    ·
      refine ⟨39656626779647880245016467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26437751186431920163344311 39656626779647880245016467)
      ·
        refine ⟨59484940169471820367524701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39656626779647880245016467 59484940169471820367524701)
        ·
          refine ⟨22306852563551932637821763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 59484940169471820367524701 22306852563551932637821763)
          ·
            refine ⟨33460278845327898956732645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22306852563551932637821763 33460278845327898956732645)
            ·
              refine ⟨6273802283498981054387371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 33460278845327898956732645 6273802283498981054387371)
              ·
                refine ⟨9410703425248471581581057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6273802283498981054387371 9410703425248471581581057)
                ·
                  refine ⟨7058027568936353686185793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9410703425248471581581057 7058027568936353686185793)
                  ·
                    refine ⟨5293520676702265264639345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7058027568936353686185793 5293520676702265264639345)
                    ·
                      refine ⟨3970140507526698948479509, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5293520676702265264639345 3970140507526698948479509)
                      ·
                        rfl

theorem cell23_7731821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 4, 1, 2, 2, 2].length) (baseStart_7731821 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7731821 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7731821 prefixEnd_7731821 := by exact prefixLift 7731821
  have htrace : WordTrace (prefixWord ++ tailWord_7731821) baseStart_7731821 baseEnd_7731821 := by
    simpa [prefixWord, tailWord_7731821, baseEnd_7731821] using wordTrace_append hprefix tailTrace_7731821
  have hstable : (prefixWord ++ tailWord_7731821).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7731821).length < 2 ^ (prefixWord ++ tailWord_7731821).sum := by decide
  have hdescent : baseEnd_7731821 < baseStart_7731821 := by decide
  rcases family_descends (prefixWord ++ tailWord_7731821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7731840 : List Nat := [2, 1, 1, 2, 1, 6, 2, 1, 2, 5]
def baseStart_7731840 : Nat := 118140960795 + 7731840 * 2 ^ 59
def prefixEnd_7731840 : Nat := 4983230072969 + 3 ^ 40 * 7731840 * 2
def baseEnd_7731840 : Nat := 1323383421219711458047307

theorem tailTrace_7731840 : CollatzResearch.WordTrace tailWord_7731840 prefixEnd_7731840 1323383421219711458047307 := by
  unfold tailWord_7731840
  simp only [CollatzResearch.WordTrace]
  refine ⟨141001686154435823993640487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 188002248205914431991520649 141001686154435823993640487)
  ·
    refine ⟨211502529231653735990460731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141001686154435823993640487 211502529231653735990460731)
    ·
      refine ⟨317253793847480603985691097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 211502529231653735990460731 317253793847480603985691097)
      ·
        refine ⟨237940345385610452989268323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 317253793847480603985691097 237940345385610452989268323)
        ·
          refine ⟨356910518078415679483902485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 237940345385610452989268323 356910518078415679483902485)
          ·
            refine ⟨16730180534925734975807929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 356910518078415679483902485 16730180534925734975807929)
            ·
              refine ⟨12547635401194301231855947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16730180534925734975807929 12547635401194301231855947)
              ·
                refine ⟨18821453101791451847783921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12547635401194301231855947 18821453101791451847783921)
                ·
                  refine ⟨14116089826343588885837941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18821453101791451847783921 14116089826343588885837941)
                  ·
                    refine ⟨1323383421219711458047307, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14116089826343588885837941 1323383421219711458047307)
                    ·
                      rfl

theorem cell23_7731840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 6, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 6, 2, 1, 2, 5].length) (baseStart_7731840 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7731840 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7731840 prefixEnd_7731840 := by exact prefixLift 7731840
  have htrace : WordTrace (prefixWord ++ tailWord_7731840) baseStart_7731840 baseEnd_7731840 := by
    simpa [prefixWord, tailWord_7731840, baseEnd_7731840] using wordTrace_append hprefix tailTrace_7731840
  have hstable : (prefixWord ++ tailWord_7731840).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7731840).length < 2 ^ (prefixWord ++ tailWord_7731840).sum := by decide
  have hdescent : baseEnd_7731840 < baseStart_7731840 := by decide
  rcases family_descends (prefixWord ++ tailWord_7731840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7731843 : List Nat := [1, 1, 1, 3, 3, 1, 2, 3, 1, 3, 4]
def baseStart_7731843 : Nat := 118140960795 + 7731843 * 2 ^ 59
def prefixEnd_7731843 : Nat := 4983230072969 + 3 ^ 40 * 7731843 * 2
def baseEnd_7731843 : Nat := 3970151804101097862404407

theorem tailTrace_7731843 : CollatzResearch.WordTrace tailWord_7731843 prefixEnd_7731843 3970151804101097862404407 := by
  unfold tailWord_7731843
  simp only [CollatzResearch.WordTrace]
  refine ⟨282003481727860779499640183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188002321151907186333093455 282003481727860779499640183)
  ·
    refine ⟨423005222591791169249460275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 282003481727860779499640183 423005222591791169249460275)
    ·
      refine ⟨634507833887686753874190413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 423005222591791169249460275 634507833887686753874190413)
      ·
        refine ⟨237940437707882532702821405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 634507833887686753874190413 237940437707882532702821405)
        ·
          refine ⟨89227664140455949763558027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 237940437707882532702821405 89227664140455949763558027)
          ·
            refine ⟨133841496210683924645337041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89227664140455949763558027 133841496210683924645337041)
            ·
              refine ⟨100381122158012943484002781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 133841496210683924645337041 100381122158012943484002781)
              ·
                refine ⟨37642920809254853806501043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 100381122158012943484002781 37642920809254853806501043)
                ·
                  refine ⟨56464381213882280709751565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37642920809254853806501043 56464381213882280709751565)
                  ·
                    refine ⟨21174142955205855266156837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 56464381213882280709751565 21174142955205855266156837)
                    ·
                      refine ⟨3970151804101097862404407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21174142955205855266156837 3970151804101097862404407)
                      ·
                        rfl

theorem cell23_7731843_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 2, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 2, 3, 1, 3, 4].length) (baseStart_7731843 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7731843 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7731843 prefixEnd_7731843 := by exact prefixLift 7731843
  have htrace : WordTrace (prefixWord ++ tailWord_7731843) baseStart_7731843 baseEnd_7731843 := by
    simpa [prefixWord, tailWord_7731843, baseEnd_7731843] using wordTrace_append hprefix tailTrace_7731843
  have hstable : (prefixWord ++ tailWord_7731843).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7731843).length < 2 ^ (prefixWord ++ tailWord_7731843).sum := by decide
  have hdescent : baseEnd_7731843 < baseStart_7731843 := by decide
  rcases family_descends (prefixWord ++ tailWord_7731843) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7731863 : List Nat := [1, 1, 3, 3, 2, 1, 1, 1, 2, 3, 5]
def baseStart_7731863 : Nat := 118140960795 + 7731863 * 2 ^ 59
def prefixEnd_7731863 : Nat := 4983230072969 + 3 ^ 40 * 7731863 * 2
def baseEnd_7731863 : Nat := 3970162073714187784154315

theorem tailTrace_7731863 : CollatzResearch.WordTrace tailWord_7731863 prefixEnd_7731863 3970162073714187784154315 := by
  unfold tailWord_7731863
  simp only [CollatzResearch.WordTrace]
  refine ⟨282004211187788322915368243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188002807458525548610245495 282004211187788322915368243)
  ·
    refine ⟨423006316781682484373052365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 282004211187788322915368243 423006316781682484373052365)
    ·
      refine ⟨158627368793130931639894637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 423006316781682484373052365 158627368793130931639894637)
      ·
        refine ⟨59485263297424099364960489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 158627368793130931639894637 59485263297424099364960489)
        ·
          refine ⟨44613947473068074523720367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59485263297424099364960489 44613947473068074523720367)
          ·
            refine ⟨66920921209602111785580551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44613947473068074523720367 66920921209602111785580551)
            ·
              refine ⟨100381381814403167678370827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66920921209602111785580551 100381381814403167678370827)
              ·
                refine ⟨150572072721604751517556241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 100381381814403167678370827 150572072721604751517556241)
                ·
                  refine ⟨112929054541203563638167181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 150572072721604751517556241 112929054541203563638167181)
                  ·
                    refine ⟨42348395452951336364312693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 112929054541203563638167181 42348395452951336364312693)
                    ·
                      refine ⟨3970162073714187784154315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42348395452951336364312693 3970162073714187784154315)
                      ·
                        rfl

theorem cell23_7731863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 1, 1, 2, 3, 5].length) (baseStart_7731863 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7731863 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7731863 prefixEnd_7731863 := by exact prefixLift 7731863
  have htrace : WordTrace (prefixWord ++ tailWord_7731863) baseStart_7731863 baseEnd_7731863 := by
    simpa [prefixWord, tailWord_7731863, baseEnd_7731863] using wordTrace_append hprefix tailTrace_7731863
  have hstable : (prefixWord ++ tailWord_7731863).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7731863).length < 2 ^ (prefixWord ++ tailWord_7731863).sum := by decide
  have hdescent : baseEnd_7731863 < baseStart_7731863 := by decide
  rcases family_descends (prefixWord ++ tailWord_7731863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7731894 : List Nat := [5, 1, 3, 1, 2, 1, 1, 1, 1, 3, 4]
def baseStart_7731894 : Nat := 118140960795 + 7731894 * 2 ^ 59
def prefixEnd_7731894 : Nat := 4983230072969 + 3 ^ 40 * 7731894 * 2
def baseEnd_7731894 : Nat := 3970177991614477162866673

theorem tailTrace_7731894 : CollatzResearch.WordTrace tailWord_7731894 prefixEnd_7731894 3970177991614477162866673 := by
  unfold tailWord_7731894
  simp only [CollatzResearch.WordTrace]
  refine ⟨17625333865667250950609171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 188003561233784010139831157 17625333865667250950609171)
  ·
    refine ⟨26438000798500876425913757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17625333865667250950609171 26438000798500876425913757)
    ·
      refine ⟨9914250299437828659717659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26438000798500876425913757 9914250299437828659717659)
      ·
        refine ⟨14871375449156742989576489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9914250299437828659717659 14871375449156742989576489)
        ·
          refine ⟨11153531586867557242182367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14871375449156742989576489 11153531586867557242182367)
          ·
            refine ⟨16730297380301335863273551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11153531586867557242182367 16730297380301335863273551)
            ·
              refine ⟨25095446070452003794910327, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16730297380301335863273551 25095446070452003794910327)
              ·
                refine ⟨37643169105678005692365491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25095446070452003794910327 37643169105678005692365491)
                ·
                  refine ⟨56464753658517008538548237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37643169105678005692365491 56464753658517008538548237)
                  ·
                    refine ⟨21174282621943878201955589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 56464753658517008538548237 21174282621943878201955589)
                    ·
                      refine ⟨3970177991614477162866673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21174282621943878201955589 3970177991614477162866673)
                      ·
                        rfl

theorem cell23_7731894_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 2, 1, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 2, 1, 1, 1, 1, 3, 4].length) (baseStart_7731894 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7731894 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7731894 prefixEnd_7731894 := by exact prefixLift 7731894
  have htrace : WordTrace (prefixWord ++ tailWord_7731894) baseStart_7731894 baseEnd_7731894 := by
    simpa [prefixWord, tailWord_7731894, baseEnd_7731894] using wordTrace_append hprefix tailTrace_7731894
  have hstable : (prefixWord ++ tailWord_7731894).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7731894).length < 2 ^ (prefixWord ++ tailWord_7731894).sum := by decide
  have hdescent : baseEnd_7731894 < baseStart_7731894 := by decide
  rcases family_descends (prefixWord ++ tailWord_7731894) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7731904 : List Nat := [2, 1, 1, 2, 4, 3, 2, 3, 1, 4]
def baseStart_7731904 : Nat := 118140960795 + 7731904 * 2 ^ 59
def prefixEnd_7731904 : Nat := 4983230072969 + 3 ^ 40 * 7731904 * 2
def baseEnd_7731904 : Nat := 1323394375473674041247209

theorem tailTrace_7731904 : CollatzResearch.WordTrace tailWord_7731904 prefixEnd_7731904 1323394375473674041247209 := by
  unfold tailWord_7731904
  simp only [CollatzResearch.WordTrace]
  refine ⟨141002853290319893458805383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 188003804387093191278407177 141002853290319893458805383)
  ·
    refine ⟨211504279935479840188208075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141002853290319893458805383 211504279935479840188208075)
    ·
      refine ⟨317256419903219760282312113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 211504279935479840188208075 317256419903219760282312113)
      ·
        refine ⟨237942314927414820211734085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 317256419903219760282312113 237942314927414820211734085)
        ·
          refine ⟨44614184048890278789700141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 237942314927414820211734085 44614184048890278789700141)
          ·
            refine ⟨16730319018333854546137553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44614184048890278789700141 16730319018333854546137553)
            ·
              refine ⟨12547739263750390909603165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16730319018333854546137553 12547739263750390909603165)
              ·
                refine ⟨4705402223906396591101187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12547739263750390909603165 4705402223906396591101187)
                ·
                  refine ⟨7058103335859594886651781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4705402223906396591101187 7058103335859594886651781)
                  ·
                    refine ⟨1323394375473674041247209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7058103335859594886651781 1323394375473674041247209)
                    ·
                      rfl

theorem cell23_7731904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 3, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 3, 2, 3, 1, 4].length) (baseStart_7731904 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7731904 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7731904 prefixEnd_7731904 := by exact prefixLift 7731904
  have htrace : WordTrace (prefixWord ++ tailWord_7731904) baseStart_7731904 baseEnd_7731904 := by
    simpa [prefixWord, tailWord_7731904, baseEnd_7731904] using wordTrace_append hprefix tailTrace_7731904
  have hstable : (prefixWord ++ tailWord_7731904).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7731904).length < 2 ^ (prefixWord ++ tailWord_7731904).sum := by decide
  have hdescent : baseEnd_7731904 < baseStart_7731904 := by decide
  rcases family_descends (prefixWord ++ tailWord_7731904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7731927 : List Nat := [1, 1, 3, 2, 1, 4, 1, 3, 3, 1, 3]
def baseStart_7731927 : Nat := 118140960795 + 7731927 * 2 ^ 59
def prefixEnd_7731927 : Nat := 4983230072969 + 3 ^ 40 * 7731927 * 2
def baseEnd_7731927 : Nat := 3970194936476075533754021

theorem tailTrace_7731927 : CollatzResearch.WordTrace tailWord_7731927 prefixEnd_7731927 3970194936476075533754021 := by
  unfold tailWord_7731927
  simp only [CollatzResearch.WordTrace]
  refine ⟨282006545459556461845698035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188004363639704307897132023 282006545459556461845698035)
  ·
    refine ⟨423009818189334692768547053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 282006545459556461845698035 423009818189334692768547053)
    ·
      refine ⟨158628681821000509788205145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 423009818189334692768547053 158628681821000509788205145)
      ·
        refine ⟨118971511365750382341153859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 158628681821000509788205145 118971511365750382341153859)
        ·
          refine ⟨178457267048625573511730789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 118971511365750382341153859 178457267048625573511730789)
          ·
            refine ⟨33460737571617295033449523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 178457267048625573511730789 33460737571617295033449523)
            ·
              refine ⟨50191106357425942550174285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33460737571617295033449523 50191106357425942550174285)
              ·
                refine ⟨18821664884034728456315357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 50191106357425942550174285 18821664884034728456315357)
                ·
                  refine ⟨7058124331513023171118259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18821664884034728456315357 7058124331513023171118259)
                  ·
                    refine ⟨10587186497269534756677389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7058124331513023171118259 10587186497269534756677389)
                    ·
                      refine ⟨3970194936476075533754021, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10587186497269534756677389 3970194936476075533754021)
                      ·
                        rfl

theorem cell23_7731927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 1, 3, 3, 1, 3].length) (baseStart_7731927 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7731927 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7731927 prefixEnd_7731927 := by exact prefixLift 7731927
  have htrace : WordTrace (prefixWord ++ tailWord_7731927) baseStart_7731927 baseEnd_7731927 := by
    simpa [prefixWord, tailWord_7731927, baseEnd_7731927] using wordTrace_append hprefix tailTrace_7731927
  have hstable : (prefixWord ++ tailWord_7731927).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7731927).length < 2 ^ (prefixWord ++ tailWord_7731927).sum := by decide
  have hdescent : baseEnd_7731927 < baseStart_7731927 := by decide
  rcases family_descends (prefixWord ++ tailWord_7731927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7731937 : List Nat := [1, 2, 3, 1, 4, 1, 1, 2, 1, 5, 2]
def baseStart_7731937 : Nat := 118140960795 + 7731937 * 2 ^ 59
def prefixEnd_7731937 : Nat := 4983230072969 + 3 ^ 40 * 7731937 * 2
def baseEnd_7731937 : Nat := 3970200071282620494628975

theorem tailTrace_7731937 : CollatzResearch.WordTrace tailWord_7731937 prefixEnd_7731937 3970200071282620494628975 := by
  unfold tailWord_7731937
  simp only [CollatzResearch.WordTrace]
  refine ⟨282006910189520233553562065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188004606793013489035708043 282006910189520233553562065)
  ·
    refine ⟨211505182642140175165171549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 282006910189520233553562065 211505182642140175165171549)
    ·
      refine ⟨79314443490802565686939331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 211505182642140175165171549 79314443490802565686939331)
      ·
        refine ⟨118971665236203848530408997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79314443490802565686939331 118971665236203848530408997)
        ·
          refine ⟨22307187231788221599451687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 118971665236203848530408997 22307187231788221599451687)
          ·
            refine ⟨33460780847682332399177531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22307187231788221599451687 33460780847682332399177531)
            ·
              refine ⟨50191171271523498598766297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33460780847682332399177531 50191171271523498598766297)
              ·
                refine ⟨37643378453642623949074723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50191171271523498598766297 37643378453642623949074723)
                ·
                  refine ⟨56465067680463935923612085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37643378453642623949074723 56465067680463935923612085)
                  ·
                    refine ⟨5293600095043493992838633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 56465067680463935923612085 5293600095043493992838633)
                    ·
                      refine ⟨3970200071282620494628975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5293600095043493992838633 3970200071282620494628975)
                      ·
                        rfl

theorem cell23_7731937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 1, 2, 1, 5, 2].length) (baseStart_7731937 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7731937 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7731937 prefixEnd_7731937 := by exact prefixLift 7731937
  have htrace : WordTrace (prefixWord ++ tailWord_7731937) baseStart_7731937 baseEnd_7731937 := by
    simpa [prefixWord, tailWord_7731937, baseEnd_7731937] using wordTrace_append hprefix tailTrace_7731937
  have hstable : (prefixWord ++ tailWord_7731937).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7731937).length < 2 ^ (prefixWord ++ tailWord_7731937).sum := by decide
  have hdescent : baseEnd_7731937 < baseStart_7731937 := by decide
  rcases family_descends (prefixWord ++ tailWord_7731937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7731960 : List Nat := [2, 1, 2, 1, 1, 2, 3, 1, 6, 4]
def baseStart_7731960 : Nat := 118140960795 + 7731960 * 2 ^ 59
def prefixEnd_7731960 : Nat := 4983230072969 + 3 ^ 40 * 7731960 * 2
def baseEnd_7731960 : Nat := 1323403960445891301547123

theorem tailTrace_7731960 : CollatzResearch.WordTrace tailWord_7731960 prefixEnd_7731960 1323403960445891301547123 := by
  unfold tailWord_7731960
  simp only [CollatzResearch.WordTrace]
  refine ⟨141003874534218454240824667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 188005166045624605654432889 141003874534218454240824667)
  ·
    refine ⟨211505811801327681361237001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141003874534218454240824667 211505811801327681361237001)
    ·
      refine ⟨158629358850995761020927751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 211505811801327681361237001 158629358850995761020927751)
      ·
        refine ⟨237944038276493641531391627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 158629358850995761020927751 237944038276493641531391627)
        ·
          refine ⟨356916057414740462297087441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 237944038276493641531391627 356916057414740462297087441)
          ·
            refine ⟨267687043061055346722815581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 356916057414740462297087441 267687043061055346722815581)
            ·
              refine ⟨100382641147895755021055843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 267687043061055346722815581 100382641147895755021055843)
              ·
                refine ⟨150573961721843632531583765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 100382641147895755021055843 150573961721843632531583765)
                ·
                  refine ⟨7058154455711420274917989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 150573961721843632531583765 7058154455711420274917989)
                  ·
                    refine ⟨1323403960445891301547123, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7058154455711420274917989 1323403960445891301547123)
                    ·
                      rfl

theorem cell23_7731960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 3, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 3, 1, 6, 4].length) (baseStart_7731960 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7731960 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7731960 prefixEnd_7731960 := by exact prefixLift 7731960
  have htrace : WordTrace (prefixWord ++ tailWord_7731960) baseStart_7731960 baseEnd_7731960 := by
    simpa [prefixWord, tailWord_7731960, baseEnd_7731960] using wordTrace_append hprefix tailTrace_7731960
  have hstable : (prefixWord ++ tailWord_7731960).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7731960).length < 2 ^ (prefixWord ++ tailWord_7731960).sum := by decide
  have hdescent : baseEnd_7731960 < baseStart_7731960 := by decide
  rcases family_descends (prefixWord ++ tailWord_7731960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7732004 : List Nat := [2, 3, 1, 3, 3, 1, 1, 1, 3, 2, 3]
def baseStart_7732004 : Nat := 118140960795 + 7732004 * 2 ^ 59
def prefixEnd_7732004 : Nat := 4983230072969 + 3 ^ 40 * 7732004 * 2
def baseEnd_7732004 : Nat := 3970234474486471732491167

theorem tailTrace_7732004 : CollatzResearch.WordTrace tailWord_7732004 prefixEnd_7732004 3970234474486471732491167 := by
  unfold tailWord_7732004
  simp only [CollatzResearch.WordTrace]
  refine ⟨141004676940138751998125533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 188006235920185002664167377 141004676940138751998125533)
  ·
    refine ⟨52876753852552031999297075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 141004676940138751998125533 52876753852552031999297075)
    ·
      refine ⟨79315130778828047998945613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52876753852552031999297075 79315130778828047998945613)
      ·
        refine ⟨29743174042060517999604605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 79315130778828047998945613 29743174042060517999604605)
        ·
          refine ⟨11153690265772694249851727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29743174042060517999604605 11153690265772694249851727)
          ·
            refine ⟨16730535398659041374777591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11153690265772694249851727 16730535398659041374777591)
            ·
              refine ⟨25095803097988562062166387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16730535398659041374777591 25095803097988562062166387)
              ·
                refine ⟨37643704646982843093249581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25095803097988562062166387 37643704646982843093249581)
                ·
                  refine ⟨14116389242618566159968593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37643704646982843093249581 14116389242618566159968593)
                  ·
                    refine ⟨10587291931963924619976445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14116389242618566159968593 10587291931963924619976445)
                    ·
                      refine ⟨3970234474486471732491167, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10587291931963924619976445 3970234474486471732491167)
                      ·
                        rfl

theorem cell23_7732004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 3, 1, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 3, 1, 1, 1, 3, 2, 3].length) (baseStart_7732004 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7732004 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7732004 prefixEnd_7732004 := by exact prefixLift 7732004
  have htrace : WordTrace (prefixWord ++ tailWord_7732004) baseStart_7732004 baseEnd_7732004 := by
    simpa [prefixWord, tailWord_7732004, baseEnd_7732004] using wordTrace_append hprefix tailTrace_7732004
  have hstable : (prefixWord ++ tailWord_7732004).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7732004).length < 2 ^ (prefixWord ++ tailWord_7732004).sum := by decide
  have hdescent : baseEnd_7732004 < baseStart_7732004 := by decide
  rcases family_descends (prefixWord ++ tailWord_7732004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7732014 : List Nat := [4, 1, 3, 2, 1, 2, 1, 2, 1, 2, 4]
def baseStart_7732014 : Nat := 118140960795 + 7732014 * 2 ^ 59
def prefixEnd_7732014 : Nat := 4983230072969 + 3 ^ 40 * 7732014 * 2
def baseEnd_7732014 : Nat := 3970239609293016693366121

theorem tailTrace_7732014 : CollatzResearch.WordTrace tailWord_7732014 prefixEnd_7732014 3970239609293016693366121 := by
  unfold tailWord_7732014
  simp only [CollatzResearch.WordTrace]
  refine ⟨35251214826280159463014387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 188006479073494183802743397 35251214826280159463014387)
  ·
    refine ⟨52876822239420239194521581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35251214826280159463014387 52876822239420239194521581)
    ·
      refine ⟨19828808339782589697945593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 52876822239420239194521581 19828808339782589697945593)
      ·
        refine ⟨14871606254836942273459195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19828808339782589697945593 14871606254836942273459195)
        ·
          refine ⟨22307409382255413410188793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14871606254836942273459195 22307409382255413410188793)
          ·
            refine ⟨16730557036691560057641595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22307409382255413410188793 16730557036691560057641595)
            ·
              refine ⟨25095835555037340086462393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16730557036691560057641595 25095835555037340086462393)
              ·
                refine ⟨18821876666278005064846795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25095835555037340086462393 18821876666278005064846795)
                ·
                  refine ⟨28232814999417007597270193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18821876666278005064846795 28232814999417007597270193)
                  ·
                    refine ⟨21174611249562755697952645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28232814999417007597270193 21174611249562755697952645)
                    ·
                      refine ⟨3970239609293016693366121, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21174611249562755697952645 3970239609293016693366121)
                      ·
                        rfl

theorem cell23_7732014_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 2, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 2, 1, 2, 1, 2, 4].length) (baseStart_7732014 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7732014 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7732014 prefixEnd_7732014 := by exact prefixLift 7732014
  have htrace : WordTrace (prefixWord ++ tailWord_7732014) baseStart_7732014 baseEnd_7732014 := by
    simpa [prefixWord, tailWord_7732014, baseEnd_7732014] using wordTrace_append hprefix tailTrace_7732014
  have hstable : (prefixWord ++ tailWord_7732014).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7732014).length < 2 ^ (prefixWord ++ tailWord_7732014).sum := by decide
  have hdescent : baseEnd_7732014 < baseStart_7732014 := by decide
  rcases family_descends (prefixWord ++ tailWord_7732014) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7732017 : List Nat := [1, 2, 2, 3, 2, 1, 3, 2, 1, 3, 3]
def baseStart_7732017 : Nat := 118140960795 + 7732017 * 2 ^ 59
def prefixEnd_7732017 : Nat := 4983230072969 + 3 ^ 40 * 7732017 * 2
def baseEnd_7732017 : Nat := 3970241149734980181628607

theorem tailTrace_7732017 : CollatzResearch.WordTrace tailWord_7732017 prefixEnd_7732017 3970241149734980181628607 := by
  unfold tailWord_7732017
  simp only [CollatzResearch.WordTrace]
  refine ⟨282009828029230407216474305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188006552019486938144316203 282009828029230407216474305)
  ·
    refine ⟨211507371021922805412355729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 282009828029230407216474305 211507371021922805412355729)
    ·
      refine ⟨158630528266442104059266797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 211507371021922805412355729 158630528266442104059266797)
      ·
        refine ⟨59486448099915789022225049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 158630528266442104059266797 59486448099915789022225049)
        ·
          refine ⟨44614836074936841766668787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59486448099915789022225049 44614836074936841766668787)
          ·
            refine ⟨66922254112405262650003181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44614836074936841766668787 66922254112405262650003181)
            ·
              refine ⟨25095845292151973493751193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 66922254112405262650003181 25095845292151973493751193)
              ·
                refine ⟨18821883969113980120313395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25095845292151973493751193 18821883969113980120313395)
                ·
                  refine ⟨28232825953670970180470093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18821883969113980120313395 28232825953670970180470093)
                  ·
                    refine ⟨10587309732626613817676285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28232825953670970180470093 10587309732626613817676285)
                    ·
                      refine ⟨3970241149734980181628607, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10587309732626613817676285 3970241149734980181628607)
                      ·
                        rfl

theorem cell23_7732017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 3, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 3, 2, 1, 3, 3].length) (baseStart_7732017 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7732017 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7732017 prefixEnd_7732017 := by exact prefixLift 7732017
  have htrace : WordTrace (prefixWord ++ tailWord_7732017) baseStart_7732017 baseEnd_7732017 := by
    simpa [prefixWord, tailWord_7732017, baseEnd_7732017] using wordTrace_append hprefix tailTrace_7732017
  have hstable : (prefixWord ++ tailWord_7732017).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7732017).length < 2 ^ (prefixWord ++ tailWord_7732017).sum := by decide
  have hdescent : baseEnd_7732017 < baseStart_7732017 := by decide
  rcases family_descends (prefixWord ++ tailWord_7732017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7732021 : List Nat := [1, 3, 3, 1, 3, 2, 3, 1, 1, 2, 3]
def baseStart_7732021 : Nat := 118140960795 + 7732021 * 2 ^ 59
def prefixEnd_7732021 : Nat := 4983230072969 + 3 ^ 40 * 7732021 * 2
def baseEnd_7732021 : Nat := 3970243203657598165978589

theorem tailTrace_7732021 : CollatzResearch.WordTrace tailWord_7732021 prefixEnd_7732021 3970243203657598165978589 := by
  unfold tailWord_7732021
  simp only [CollatzResearch.WordTrace]
  refine ⟨282009973921215915899619917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188006649280810610599746611 282009973921215915899619917)
  ·
    refine ⟨105753740220455968462357469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 282009973921215915899619917 105753740220455968462357469)
    ·
      refine ⟨39657652582670988173384051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 105753740220455968462357469 39657652582670988173384051)
      ·
        refine ⟨59486478874006482260076077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39657652582670988173384051 59486478874006482260076077)
        ·
          refine ⟨22307429577752430847528529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 59486478874006482260076077 22307429577752430847528529)
          ·
            refine ⟨16730572183314323135646397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22307429577752430847528529 16730572183314323135646397)
            ·
              refine ⟨6273964568742871175867399, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16730572183314323135646397 6273964568742871175867399)
              ·
                refine ⟨9410946853114306763801099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6273964568742871175867399 9410946853114306763801099)
                ·
                  refine ⟨14116420279671460145701649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9410946853114306763801099 14116420279671460145701649)
                  ·
                    refine ⟨10587315209753595109276237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14116420279671460145701649 10587315209753595109276237)
                    ·
                      refine ⟨3970243203657598165978589, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10587315209753595109276237 3970243203657598165978589)
                      ·
                        rfl

theorem cell23_7732021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 2, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 2, 3, 1, 1, 2, 3].length) (baseStart_7732021 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7732021 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7732021 prefixEnd_7732021 := by exact prefixLift 7732021
  have htrace : WordTrace (prefixWord ++ tailWord_7732021) baseStart_7732021 baseEnd_7732021 := by
    simpa [prefixWord, tailWord_7732021, baseEnd_7732021] using wordTrace_append hprefix tailTrace_7732021
  have hstable : (prefixWord ++ tailWord_7732021).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7732021).length < 2 ^ (prefixWord ++ tailWord_7732021).sum := by decide
  have hdescent : baseEnd_7732021 < baseStart_7732021 := by decide
  rcases family_descends (prefixWord ++ tailWord_7732021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7732040 : List Nat := [2, 1, 3, 1, 1, 3, 1, 1, 1, 5, 4]
def baseStart_7732040 : Nat := 118140960795 + 7732040 * 2 ^ 59
def prefixEnd_7732040 : Nat := 4983230072969 + 3 ^ 40 * 7732040 * 2
def baseEnd_7732040 : Nat := 3970252959790033591641001

theorem tailTrace_7732040 : CollatzResearch.WordTrace tailWord_7732040 prefixEnd_7732040 3970252959790033591641001 := by
  unfold tailWord_7732040
  simp only [CollatzResearch.WordTrace]
  refine ⟨141005333454073541072280787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 188007111272098054763041049 141005333454073541072280787)
  ·
    refine ⟨211508000181110311608421181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141005333454073541072280787 211508000181110311608421181)
    ·
      refine ⟨79315500067916366853157943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 211508000181110311608421181 79315500067916366853157943)
      ·
        refine ⟨118973250101874550279736915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79315500067916366853157943 118973250101874550279736915)
        ·
          refine ⟨178459875152811825419605373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 118973250101874550279736915 178459875152811825419605373)
          ·
            refine ⟨66922453182304434532352015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 178459875152811825419605373 66922453182304434532352015)
            ·
              refine ⟨100383679773456651798528023, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66922453182304434532352015 100383679773456651798528023)
              ·
                refine ⟨150575519660184977697792035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 100383679773456651798528023 150575519660184977697792035)
                ·
                  refine ⟨225863279490277466546688053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 150575519660184977697792035 225863279490277466546688053)
                  ·
                    refine ⟨21174682452213512488752005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 225863279490277466546688053 21174682452213512488752005)
                    ·
                      refine ⟨3970252959790033591641001, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21174682452213512488752005 3970252959790033591641001)
                      ·
                        rfl

theorem cell23_7732040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 1, 1, 1, 5, 4].length) (baseStart_7732040 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7732040 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7732040 prefixEnd_7732040 := by exact prefixLift 7732040
  have htrace : WordTrace (prefixWord ++ tailWord_7732040) baseStart_7732040 baseEnd_7732040 := by
    simpa [prefixWord, tailWord_7732040, baseEnd_7732040] using wordTrace_append hprefix tailTrace_7732040
  have hstable : (prefixWord ++ tailWord_7732040).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7732040).length < 2 ^ (prefixWord ++ tailWord_7732040).sum := by decide
  have hdescent : baseEnd_7732040 < baseStart_7732040 := by decide
  rcases family_descends (prefixWord ++ tailWord_7732040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7732044 : List Nat := [2, 2, 1, 3, 3, 1, 1, 2, 3, 3, 2]
def baseStart_7732044 : Nat := 118140960795 + 7732044 * 2 ^ 59
def prefixEnd_7732044 : Nat := 4983230072969 + 3 ^ 40 * 7732044 * 2
def baseEnd_7732044 : Nat := 3970255013712651575990983

theorem tailTrace_7732044 : CollatzResearch.WordTrace tailWord_7732044 prefixEnd_7732044 3970255013712651575990983 := by
  unfold tailWord_7732044
  simp only [CollatzResearch.WordTrace]
  refine ⟨141005406400066295413853593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 188007208533421727218471457 141005406400066295413853593)
  ·
    refine ⟨105754054800049721560390195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 141005406400066295413853593 105754054800049721560390195)
    ·
      refine ⟨158631082200074582340585293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105754054800049721560390195 158631082200074582340585293)
      ·
        refine ⟨59486655825027968377719485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 158631082200074582340585293 59486655825027968377719485)
        ·
          refine ⟨22307495934385488141644807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 59486655825027968377719485 22307495934385488141644807)
          ·
            refine ⟨33461243901578232212467211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22307495934385488141644807 33461243901578232212467211)
            ·
              refine ⟨50191865852367348318700817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33461243901578232212467211 50191865852367348318700817)
              ·
                refine ⟨37643899389275511239025613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50191865852367348318700817 37643899389275511239025613)
                ·
                  refine ⟨14116462270978316714634605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37643899389275511239025613 14116462270978316714634605)
                  ·
                    refine ⟨5293673351616868767987977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14116462270978316714634605 5293673351616868767987977)
                    ·
                      refine ⟨3970255013712651575990983, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5293673351616868767987977 3970255013712651575990983)
                      ·
                        rfl

theorem cell23_7732044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 1, 2, 3, 3, 2].length) (baseStart_7732044 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7732044 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7732044 prefixEnd_7732044 := by exact prefixLift 7732044
  have htrace : WordTrace (prefixWord ++ tailWord_7732044) baseStart_7732044 baseEnd_7732044 := by
    simpa [prefixWord, tailWord_7732044, baseEnd_7732044] using wordTrace_append hprefix tailTrace_7732044
  have hstable : (prefixWord ++ tailWord_7732044).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7732044).length < 2 ^ (prefixWord ++ tailWord_7732044).sum := by decide
  have hdescent : baseEnd_7732044 < baseStart_7732044 := by decide
  rcases family_descends (prefixWord ++ tailWord_7732044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7732078 : List Nat := [4, 1, 2, 3, 2, 1, 1, 3, 1, 3, 2]
def baseStart_7732078 : Nat := 118140960795 + 7732078 * 2 ^ 59
def prefixEnd_7732078 : Nat := 4983230072969 + 3 ^ 40 * 7732078 * 2
def baseEnd_7732078 : Nat := 3970272472054904442965827

theorem tailTrace_7732078 : CollatzResearch.WordTrace tailWord_7732078 prefixEnd_7732078 3970272472054904442965827 := by
  unfold tailWord_7732078
  simp only [CollatzResearch.WordTrace]
  refine ⟨35251506610251176829305611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 188008035254672943089629925 35251506610251176829305611)
  ·
    refine ⟨52877259915376765243958417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35251506610251176829305611 52877259915376765243958417)
    ·
      refine ⟨39657944936532573932968813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52877259915376765243958417 39657944936532573932968813)
      ·
        refine ⟨14871729351199715224863305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39657944936532573932968813 14871729351199715224863305)
        ·
          refine ⟨11153797013399786418647479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14871729351199715224863305 11153797013399786418647479)
          ·
            refine ⟨16730695520099679627971219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11153797013399786418647479 16730695520099679627971219)
            ·
              refine ⟨25096043280149519441956829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16730695520099679627971219 25096043280149519441956829)
              ·
                refine ⟨9411016230056069790733811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25096043280149519441956829 9411016230056069790733811)
                ·
                  refine ⟨14116524345084104686100717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9411016230056069790733811 14116524345084104686100717)
                  ·
                    refine ⟨5293696629406539257287769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14116524345084104686100717 5293696629406539257287769)
                    ·
                      refine ⟨3970272472054904442965827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5293696629406539257287769 3970272472054904442965827)
                      ·
                        rfl

theorem cell23_7732078_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 2, 1, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 2, 1, 1, 3, 1, 3, 2].length) (baseStart_7732078 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7732078 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7732078 prefixEnd_7732078 := by exact prefixLift 7732078
  have htrace : WordTrace (prefixWord ++ tailWord_7732078) baseStart_7732078 baseEnd_7732078 := by
    simpa [prefixWord, tailWord_7732078, baseEnd_7732078] using wordTrace_append hprefix tailTrace_7732078
  have hstable : (prefixWord ++ tailWord_7732078).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7732078).length < 2 ^ (prefixWord ++ tailWord_7732078).sum := by decide
  have hdescent : baseEnd_7732078 < baseStart_7732078 := by decide
  rcases family_descends (prefixWord ++ tailWord_7732078) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7732091 : List Nat := [1, 1, 1, 1, 1, 5, 5, 2, 2, 2, 2]
def baseStart_7732091 : Nat := 118140960795 + 7732091 * 2 ^ 59
def prefixEnd_7732091 : Nat := 4983230072969 + 3 ^ 40 * 7732091 * 2
def baseEnd_7732091 : Nat := 3970279147303412892103267

theorem tailTrace_7732091 : CollatzResearch.WordTrace tailWord_7732091 prefixEnd_7732091 3970279147303412892103267 := by
  unfold tailWord_7732091
  simp only [CollatzResearch.WordTrace]
  refine ⟨282012527030962317854668127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188008351353974878569778751 282012527030962317854668127)
  ·
    refine ⟨423018790546443476782002191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 282012527030962317854668127 423018790546443476782002191)
    ·
      refine ⟨634528185819665215173003287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 423018790546443476782002191 634528185819665215173003287)
      ·
        refine ⟨951792278729497822759504931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 634528185819665215173003287 951792278729497822759504931)
        ·
          refine ⟨1427688418094246734139257397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 951792278729497822759504931 1427688418094246734139257397)
          ·
            refine ⟨133845789196335631325555381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 1427688418094246734139257397 133845789196335631325555381)
            ·
              refine ⟨12548042737156465436770817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 133845789196335631325555381 12548042737156465436770817)
              ·
                refine ⟨9411032052867349077578113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12548042737156465436770817 9411032052867349077578113)
                ·
                  refine ⟨7058274039650511808183585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9411032052867349077578113 7058274039650511808183585)
                  ·
                    refine ⟨5293705529737883856137689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7058274039650511808183585 5293705529737883856137689)
                    ·
                      refine ⟨3970279147303412892103267, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5293705529737883856137689 3970279147303412892103267)
                      ·
                        rfl

theorem cell23_7732091_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 5, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 5, 2, 2, 2, 2].length) (baseStart_7732091 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7732091 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7732091 prefixEnd_7732091 := by exact prefixLift 7732091
  have htrace : WordTrace (prefixWord ++ tailWord_7732091) baseStart_7732091 baseEnd_7732091 := by
    simpa [prefixWord, tailWord_7732091, baseEnd_7732091] using wordTrace_append hprefix tailTrace_7732091
  have hstable : (prefixWord ++ tailWord_7732091).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7732091).length < 2 ^ (prefixWord ++ tailWord_7732091).sum := by decide
  have hdescent : baseEnd_7732091 < baseStart_7732091 := by decide
  rcases family_descends (prefixWord ++ tailWord_7732091) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7732107 : List Nat := [1, 1, 1, 1, 4, 2, 4, 1, 2, 3, 3]
def baseStart_7732107 : Nat := 118140960795 + 7732107 * 2 ^ 59
def prefixEnd_7732107 : Nat := 4983230072969 + 3 ^ 40 * 7732107 * 2
def baseEnd_7732107 : Nat := 3970287362993884829503193

theorem tailTrace_7732107 : CollatzResearch.WordTrace tailWord_7732107 prefixEnd_7732107 3970287362993884829503193 := by
  unfold tailWord_7732107
  simp only [CollatzResearch.WordTrace]
  refine ⟨282013110598904352587250575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188008740399269568391500383 282013110598904352587250575)
  ·
    refine ⟨423019665898356528880875863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 282013110598904352587250575 423019665898356528880875863)
    ·
      refine ⟨634529498847534793321313795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 423019665898356528880875863 634529498847534793321313795)
      ·
        refine ⟨951794248271302189981970693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 634529498847534793321313795 951794248271302189981970693)
        ·
          refine ⟨178461421550869160621619505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 951794248271302189981970693 178461421550869160621619505)
          ·
            refine ⟨133846066163151870466214629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 178461421550869160621619505 133846066163151870466214629)
            ·
              refine ⟨25096137405590975712415243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 133846066163151870466214629 25096137405590975712415243)
              ·
                refine ⟨37644206108386463568622865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25096137405590975712415243 37644206108386463568622865)
                ·
                  refine ⟨28233154581289847676467149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37644206108386463568622865 28233154581289847676467149)
                  ·
                    refine ⟨10587432967983692878675181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28233154581289847676467149 10587432967983692878675181)
                    ·
                      refine ⟨3970287362993884829503193, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10587432967983692878675181 3970287362993884829503193)
                      ·
                        rfl

theorem cell23_7732107_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 4, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 4, 1, 2, 3, 3].length) (baseStart_7732107 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7732107 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7732107 prefixEnd_7732107 := by exact prefixLift 7732107
  have htrace : WordTrace (prefixWord ++ tailWord_7732107) baseStart_7732107 baseEnd_7732107 := by
    simpa [prefixWord, tailWord_7732107, baseEnd_7732107] using wordTrace_append hprefix tailTrace_7732107
  have hstable : (prefixWord ++ tailWord_7732107).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7732107).length < 2 ^ (prefixWord ++ tailWord_7732107).sum := by decide
  have hdescent : baseEnd_7732107 < baseStart_7732107 := by decide
  rcases family_descends (prefixWord ++ tailWord_7732107) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7732127 : List Nat := [1, 1, 2, 5, 2, 1, 2, 1, 1, 7]
def baseStart_7732127 : Nat := 118140960795 + 7732127 * 2 ^ 59
def prefixEnd_7732127 : Nat := 4983230072969 + 3 ^ 40 * 7732127 * 2
def baseEnd_7732127 : Nat := 1323432544202324917084367

theorem tailTrace_7732127 : CollatzResearch.WordTrace tailWord_7732127 prefixEnd_7732127 1323432544202324917084367 := by
  unfold tailWord_7732127
  simp only [CollatzResearch.WordTrace]
  refine ⟨282013840058831896002978635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188009226705887930668652423 282013840058831896002978635)
  ·
    refine ⟨423020760088247844004467953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 282013840058831896002978635 423020760088247844004467953)
    ·
      refine ⟨317265570066185883003350965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 423020760088247844004467953 317265570066185883003350965)
      ·
        refine ⟨29743647193704926531564153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 317265570066185883003350965 29743647193704926531564153)
        ·
          refine ⟨22307735395278694898673115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29743647193704926531564153 22307735395278694898673115)
          ·
            refine ⟨33461603092918042348009673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22307735395278694898673115 33461603092918042348009673)
            ·
              refine ⟨25096202319688531761007255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33461603092918042348009673 25096202319688531761007255)
              ·
                refine ⟨37644303479532797641510883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25096202319688531761007255 37644303479532797641510883)
                ·
                  refine ⟨56466455219299196462266325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37644303479532797641510883 56466455219299196462266325)
                  ·
                    refine ⟨1323432544202324917084367, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 56466455219299196462266325 1323432544202324917084367)
                    ·
                      rfl

theorem cell23_7732127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 2, 1, 1, 7].length) (baseStart_7732127 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7732127 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7732127 prefixEnd_7732127 := by exact prefixLift 7732127
  have htrace : WordTrace (prefixWord ++ tailWord_7732127) baseStart_7732127 baseEnd_7732127 := by
    simpa [prefixWord, tailWord_7732127, baseEnd_7732127] using wordTrace_append hprefix tailTrace_7732127
  have hstable : (prefixWord ++ tailWord_7732127).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7732127).length < 2 ^ (prefixWord ++ tailWord_7732127).sum := by decide
  have hdescent : baseEnd_7732127 < baseStart_7732127 := by decide
  rcases family_descends (prefixWord ++ tailWord_7732127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7732140 : List Nat := [2, 2, 1, 1, 1, 1, 2, 2, 1, 10]
def baseStart_7732140 : Nat := 118140960795 + 7732140 * 2 ^ 59
def prefixEnd_7732140 : Nat := 4983230072969 + 3 ^ 40 * 7732140 * 2
def baseEnd_7732140 : Nat := 1323434769285161066796847

theorem tailTrace_7732140 : CollatzResearch.WordTrace tailWord_7732140 prefixEnd_7732140 1323434769285161066796847 := by
  unfold tailWord_7732140
  simp only [CollatzResearch.WordTrace]
  refine ⟨141007157103892399611600937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 188009542805189866148801249 141007157103892399611600937)
  ·
    refine ⟨105755367827919299708700703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 141007157103892399611600937 105755367827919299708700703)
    ·
      refine ⟨158633051741878949563051055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105755367827919299708700703 158633051741878949563051055)
      ·
        refine ⟨237949577612818424344576583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 158633051741878949563051055 237949577612818424344576583)
        ·
          refine ⟨356924366419227636516864875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 237949577612818424344576583 356924366419227636516864875)
          ·
            refine ⟨535386549628841454775297313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 356924366419227636516864875 535386549628841454775297313)
            ·
              refine ⟨401539912221631091081472985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 535386549628841454775297313 401539912221631091081472985)
              ·
                refine ⟨301154934166223318311104739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 401539912221631091081472985 301154934166223318311104739)
                ·
                  refine ⟨451732401249334977466657109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 301154934166223318311104739 451732401249334977466657109)
                  ·
                    refine ⟨1323434769285161066796847, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 451732401249334977466657109 1323434769285161066796847)
                    ·
                      rfl

theorem cell23_7732140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 10].length) (baseStart_7732140 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7732140 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7732140 prefixEnd_7732140 := by exact prefixLift 7732140
  have htrace : WordTrace (prefixWord ++ tailWord_7732140) baseStart_7732140 baseEnd_7732140 := by
    simpa [prefixWord, tailWord_7732140, baseEnd_7732140] using wordTrace_append hprefix tailTrace_7732140
  have hstable : (prefixWord ++ tailWord_7732140).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7732140).length < 2 ^ (prefixWord ++ tailWord_7732140).sum := by decide
  have hdescent : baseEnd_7732140 < baseStart_7732140 := by decide
  rcases family_descends (prefixWord ++ tailWord_7732140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7732167 : List Nat := [1, 1, 4, 1, 1, 2, 2, 1, 3, 4, 3]
def baseStart_7732167 : Nat := 118140960795 + 7732167 * 2 ^ 59
def prefixEnd_7732167 : Nat := 4983230072969 + 3 ^ 40 * 7732167 * 2
def baseEnd_7732167 : Nat := 3970318171833154594752917

theorem tailTrace_7732167 : CollatzResearch.WordTrace tailWord_7732167 prefixEnd_7732167 3970318171833154594752917 := by
  unfold tailWord_7732167
  simp only [CollatzResearch.WordTrace]
  refine ⟨282015298978686982834434755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188010199319124655222956503 282015298978686982834434755)
  ·
    refine ⟨423022948468030474251652133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 282015298978686982834434755 423022948468030474251652133)
    ·
      refine ⟨79316802837755713922184775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 423022948468030474251652133 79316802837755713922184775)
      ·
        refine ⟨118975204256633570883277163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79316802837755713922184775 118975204256633570883277163)
        ·
          refine ⟨178462806384950356324915745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 118975204256633570883277163 178462806384950356324915745)
          ·
            refine ⟨133847104788712767243686809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 178462806384950356324915745 133847104788712767243686809)
            ·
              refine ⟨100385328591534575432765107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 133847104788712767243686809 100385328591534575432765107)
              ·
                refine ⟨150577992887301863149147661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 100385328591534575432765107 150577992887301863149147661)
                ·
                  refine ⟨56466747332738198680930373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 150577992887301863149147661 56466747332738198680930373)
                  ·
                    refine ⟨10587515124888412252674445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 56466747332738198680930373 10587515124888412252674445)
                    ·
                      refine ⟨3970318171833154594752917, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10587515124888412252674445 3970318171833154594752917)
                      ·
                        rfl

theorem cell23_7732167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 2, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 2, 1, 3, 4, 3].length) (baseStart_7732167 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7732167 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7732167 prefixEnd_7732167 := by exact prefixLift 7732167
  have htrace : WordTrace (prefixWord ++ tailWord_7732167) baseStart_7732167 baseEnd_7732167 := by
    simpa [prefixWord, tailWord_7732167, baseEnd_7732167] using wordTrace_append hprefix tailTrace_7732167
  have hstable : (prefixWord ++ tailWord_7732167).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7732167).length < 2 ^ (prefixWord ++ tailWord_7732167).sum := by decide
  have hdescent : baseEnd_7732167 < baseStart_7732167 := by decide
  rcases family_descends (prefixWord ++ tailWord_7732167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7732181 : List Nat := [1, 3, 2, 3, 3, 1, 2, 1, 2, 1, 4]
def baseStart_7732181 : Nat := 118140960795 + 7732181 * 2 ^ 59
def prefixEnd_7732181 : Nat := 4983230072969 + 3 ^ 40 * 7732181 * 2
def baseEnd_7732181 : Nat := 3970325360562317539977853

theorem tailTrace_7732181 : CollatzResearch.WordTrace tailWord_7732181 prefixEnd_7732181 3970325360562317539977853 := by
  unfold tailWord_7732181
  simp only [CollatzResearch.WordTrace]
  refine ⟨282015809600636263225444397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188010539733757508816962931 282015809600636263225444397)
  ·
    refine ⟨105755928600238598709541649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 282015809600636263225444397 105755928600238598709541649)
    ·
      refine ⟨79316946450178949032156237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 105755928600238598709541649 79316946450178949032156237)
      ·
        refine ⟨29743854918817105887058589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 79316946450178949032156237 29743854918817105887058589)
        ·
          refine ⟨11153945594556414707646971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29743854918817105887058589 11153945594556414707646971)
          ·
            refine ⟨16730918391834622061470457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11153945594556414707646971 16730918391834622061470457)
            ·
              refine ⟨12548188793875966546102843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16730918391834622061470457 12548188793875966546102843)
              ·
                refine ⟨18822283190813949819154265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12548188793875966546102843 18822283190813949819154265)
                ·
                  refine ⟨14116712393110462364365699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18822283190813949819154265 14116712393110462364365699)
                  ·
                    refine ⟨21175068589665693546548549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14116712393110462364365699 21175068589665693546548549)
                    ·
                      refine ⟨3970325360562317539977853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21175068589665693546548549 3970325360562317539977853)
                      ·
                        rfl

theorem cell23_7732181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 3, 1, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 3, 1, 2, 1, 2, 1, 4].length) (baseStart_7732181 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7732181 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7732181 prefixEnd_7732181 := by exact prefixLift 7732181
  have htrace : WordTrace (prefixWord ++ tailWord_7732181) baseStart_7732181 baseEnd_7732181 := by
    simpa [prefixWord, tailWord_7732181, baseEnd_7732181] using wordTrace_append hprefix tailTrace_7732181
  have hstable : (prefixWord ++ tailWord_7732181).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7732181).length < 2 ^ (prefixWord ++ tailWord_7732181).sum := by decide
  have hdescent : baseEnd_7732181 < baseStart_7732181 := by decide
  rcases family_descends (prefixWord ++ tailWord_7732181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7732184 : List Nat := [2, 1, 2, 2, 2, 3, 1, 3, 2, 2, 3]
def baseStart_7732184 : Nat := 118140960795 + 7732184 * 2 ^ 59
def prefixEnd_7732184 : Nat := 4983230072969 + 3 ^ 40 * 7732184 * 2
def baseEnd_7732184 : Nat := 3970326901004281028240339

theorem tailTrace_7732184 : CollatzResearch.WordTrace tailWord_7732184 prefixEnd_7732184 3970326901004281028240339 := by
  unfold tailWord_7732184
  simp only [CollatzResearch.WordTrace]
  refine ⟨141007959509812697368901803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 188010612679750263158535737 141007959509812697368901803)
  ·
    refine ⟨211511939264719046053352705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141007959509812697368901803 211511939264719046053352705)
    ·
      refine ⟨158633954448539284540014529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 211511939264719046053352705 158633954448539284540014529)
      ·
        refine ⟨118975465836404463405010897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 158633954448539284540014529 118975465836404463405010897)
        ·
          refine ⟨89231599377303347553758173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 118975465836404463405010897 89231599377303347553758173)
          ·
            refine ⟨33461849766488755332659315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 89231599377303347553758173 33461849766488755332659315)
            ·
              refine ⟨50192774649733132998988973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33461849766488755332659315 50192774649733132998988973)
              ·
                refine ⟨18822290493649924874620865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 50192774649733132998988973 18822290493649924874620865)
                ·
                  refine ⟨14116717870237443655965649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18822290493649924874620865 14116717870237443655965649)
                  ·
                    refine ⟨10587538402678082741974237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14116717870237443655965649 10587538402678082741974237)
                    ·
                      refine ⟨3970326901004281028240339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10587538402678082741974237 3970326901004281028240339)
                      ·
                        rfl

theorem cell23_7732184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 1, 3, 2, 2, 3].length) (baseStart_7732184 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7732184 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7732184 prefixEnd_7732184 := by exact prefixLift 7732184
  have htrace : WordTrace (prefixWord ++ tailWord_7732184) baseStart_7732184 baseEnd_7732184 := by
    simpa [prefixWord, tailWord_7732184, baseEnd_7732184] using wordTrace_append hprefix tailTrace_7732184
  have hstable : (prefixWord ++ tailWord_7732184).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7732184).length < 2 ^ (prefixWord ++ tailWord_7732184).sum := by decide
  have hdescent : baseEnd_7732184 < baseStart_7732184 := by decide
  rcases family_descends (prefixWord ++ tailWord_7732184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7732217 : List Nat := [1, 2, 1, 3, 1, 3, 1, 1, 5, 5]
def baseStart_7732217 : Nat := 118140960795 + 7732217 * 2 ^ 59
def prefixEnd_7732217 : Nat := 4983230072969 + 3 ^ 40 * 7732217 * 2
def baseEnd_7732217 : Nat := 1323447948621959799709229

theorem tailTrace_7732217 : CollatzResearch.WordTrace tailWord_7732217 prefixEnd_7732217 1323447948621959799709229 := by
  unfold tailWord_7732217
  simp only [CollatzResearch.WordTrace]
  refine ⟨282017122628505841373754905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188011415085670560915836603 282017122628505841373754905)
  ·
    refine ⟨211512841971379381030316179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 282017122628505841373754905 211512841971379381030316179)
    ·
      refine ⟨317269262957069071545474269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 211512841971379381030316179 317269262957069071545474269)
      ·
        refine ⟨118975973608900901829552851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 317269262957069071545474269 118975973608900901829552851)
        ·
          refine ⟨178463960413351352744329277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 118975973608900901829552851 178463960413351352744329277)
          ·
            refine ⟨66923985155006757279123479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 178463960413351352744329277 66923985155006757279123479)
            ·
              refine ⟨100385977732510135918685219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66923985155006757279123479 100385977732510135918685219)
              ·
                refine ⟨150578966598765203878027829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 100385977732510135918685219 150578966598765203878027829)
                ·
                  refine ⟨14116778118634237863565109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 150578966598765203878027829 14116778118634237863565109)
                  ·
                    refine ⟨1323447948621959799709229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14116778118634237863565109 1323447948621959799709229)
                    ·
                      rfl

theorem cell23_7732217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 1, 1, 5, 5].length) (baseStart_7732217 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7732217 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7732217 prefixEnd_7732217 := by exact prefixLift 7732217
  have htrace : WordTrace (prefixWord ++ tailWord_7732217) baseStart_7732217 baseEnd_7732217 := by
    simpa [prefixWord, tailWord_7732217, baseEnd_7732217] using wordTrace_append hprefix tailTrace_7732217
  have hstable : (prefixWord ++ tailWord_7732217).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7732217).length < 2 ^ (prefixWord ++ tailWord_7732217).sum := by decide
  have hdescent : baseEnd_7732217 < baseStart_7732217 := by decide
  rcases family_descends (prefixWord ++ tailWord_7732217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7732231 : List Nat := [1, 1, 4, 3, 1, 1, 3, 2, 3, 1, 3]
def baseStart_7732231 : Nat := 118140960795 + 7732231 * 2 ^ 59
def prefixEnd_7732231 : Nat := 4983230072969 + 3 ^ 40 * 7732231 * 2
def baseEnd_7732231 : Nat := 3970351034595042344352623

theorem tailTrace_7732231 : CollatzResearch.WordTrace tailWord_7732231 prefixEnd_7732231 3970351034595042344352623 := by
  unfold tailWord_7732231
  simp only [CollatzResearch.WordTrace]
  refine ⟨282017633250455121764764547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188011755500303414509843031 282017633250455121764764547)
  ·
    refine ⟨423026449875682682647146821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 282017633250455121764764547 423026449875682682647146821)
    ·
      refine ⟨79317459351690502996340029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 423026449875682682647146821 79317459351690502996340029)
      ·
        refine ⟨29744047256883938623627511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 79317459351690502996340029 29744047256883938623627511)
        ·
          refine ⟨44616070885325907935441267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29744047256883938623627511 44616070885325907935441267)
          ·
            refine ⟨66924106327988861903161901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44616070885325907935441267 66924106327988861903161901)
            ·
              refine ⟨25096539872995823213685713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 66924106327988861903161901 25096539872995823213685713)
              ·
                refine ⟨18822404904746867410264285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25096539872995823213685713 18822404904746867410264285)
                ·
                  refine ⟨7058401839280075278849107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18822404904746867410264285 7058401839280075278849107)
                  ·
                    refine ⟨10587602758920112918273661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7058401839280075278849107 10587602758920112918273661)
                    ·
                      refine ⟨3970351034595042344352623, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10587602758920112918273661 3970351034595042344352623)
                      ·
                        rfl

theorem cell23_7732231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 3, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 3, 2, 3, 1, 3].length) (baseStart_7732231 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7732231 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7732231 prefixEnd_7732231 := by exact prefixLift 7732231
  have htrace : WordTrace (prefixWord ++ tailWord_7732231) baseStart_7732231 baseEnd_7732231 := by
    simpa [prefixWord, tailWord_7732231, baseEnd_7732231] using wordTrace_append hprefix tailTrace_7732231
  have hstable : (prefixWord ++ tailWord_7732231).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7732231).length < 2 ^ (prefixWord ++ tailWord_7732231).sum := by decide
  have hdescent : baseEnd_7732231 < baseStart_7732231 := by decide
  rcases family_descends (prefixWord ++ tailWord_7732231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7732234 : List Nat := [3, 1, 2, 2, 3, 1, 2, 1, 3, 5]
def baseStart_7732234 : Nat := 118140960795 + 7732234 * 2 ^ 59
def prefixEnd_7732234 : Nat := 4983230072969 + 3 ^ 40 * 7732234 * 2
def baseEnd_7732234 : Nat := 1323450858345668610871703

theorem tailTrace_7732234 : CollatzResearch.WordTrace tailWord_7732234 prefixEnd_7732234 1323450858345668610871703 := by
  unfold tailWord_7732234
  simp only [CollatzResearch.WordTrace]
  refine ⟨70504435667361063319280939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 188011828446296168851415837 70504435667361063319280939)
  ·
    refine ⟨105756653501041594978921409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70504435667361063319280939 105756653501041594978921409)
    ·
      refine ⟨79317490125781196234191057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 105756653501041594978921409 79317490125781196234191057)
      ·
        refine ⟨59488117594335897175643293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79317490125781196234191057 59488117594335897175643293)
        ·
          refine ⟨22308044097875961440866235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 59488117594335897175643293 22308044097875961440866235)
          ·
            refine ⟨33462066146813942161299353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22308044097875961440866235 33462066146813942161299353)
            ·
              refine ⟨25096549610110456620974515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33462066146813942161299353 25096549610110456620974515)
              ·
                refine ⟨37644824415165684931461773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25096549610110456620974515 37644824415165684931461773)
                ·
                  refine ⟨14116809155687131849298165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37644824415165684931461773 14116809155687131849298165)
                  ·
                    refine ⟨1323450858345668610871703, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14116809155687131849298165 1323450858345668610871703)
                    ·
                      rfl

theorem cell23_7732234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 2, 1, 3, 5].length) (baseStart_7732234 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7732234 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7732234 prefixEnd_7732234 := by exact prefixLift 7732234
  have htrace : WordTrace (prefixWord ++ tailWord_7732234) baseStart_7732234 baseEnd_7732234 := by
    simpa [prefixWord, tailWord_7732234, baseEnd_7732234] using wordTrace_append hprefix tailTrace_7732234
  have hstable : (prefixWord ++ tailWord_7732234).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7732234).length < 2 ^ (prefixWord ++ tailWord_7732234).sum := by decide
  have hdescent : baseEnd_7732234 < baseStart_7732234 := by decide
  rcases family_descends (prefixWord ++ tailWord_7732234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7732248 : List Nat := [2, 1, 2, 3, 2, 2, 1, 5, 1, 1, 3]
def baseStart_7732248 : Nat := 118140960795 + 7732248 * 2 ^ 59
def prefixEnd_7732248 : Nat := 4983230072969 + 3 ^ 40 * 7732248 * 2
def baseEnd_7732248 : Nat := 3970359763766168777840045

theorem tailTrace_7732248 : CollatzResearch.WordTrace tailWord_7732248 prefixEnd_7732248 3970359763766168777840045 := by
  unfold tailWord_7732248
  simp only [CollatzResearch.WordTrace]
  refine ⟨141009126645696766834066699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 188012168860929022445422265 141009126645696766834066699)
  ·
    refine ⟨211513689968545150251100049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141009126645696766834066699 211513689968545150251100049)
    ·
      refine ⟨158635267476408862688325037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 211513689968545150251100049 158635267476408862688325037)
      ·
        refine ⟨59488225303653323508121889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 158635267476408862688325037 59488225303653323508121889)
        ·
          refine ⟨44616168977739992631091417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59488225303653323508121889 44616168977739992631091417)
          ·
            refine ⟨33462126733304994473318563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44616168977739992631091417 33462126733304994473318563)
            ·
              refine ⟨50193190099957491709977845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33462126733304994473318563 50193190099957491709977845)
              ·
                refine ⟨4705611571871014847810423, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 50193190099957491709977845 4705611571871014847810423)
                ·
                  refine ⟨7058417357806522271715635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4705611571871014847810423 7058417357806522271715635)
                  ·
                    refine ⟨10587626036709783407573453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7058417357806522271715635 10587626036709783407573453)
                    ·
                      refine ⟨3970359763766168777840045, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10587626036709783407573453 3970359763766168777840045)
                      ·
                        rfl

theorem cell23_7732248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 1, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 1, 5, 1, 1, 3].length) (baseStart_7732248 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7732248 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7732248 prefixEnd_7732248 := by exact prefixLift 7732248
  have htrace : WordTrace (prefixWord ++ tailWord_7732248) baseStart_7732248 baseEnd_7732248 := by
    simpa [prefixWord, tailWord_7732248, baseEnd_7732248] using wordTrace_append hprefix tailTrace_7732248
  have hstable : (prefixWord ++ tailWord_7732248).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7732248).length < 2 ^ (prefixWord ++ tailWord_7732248).sum := by decide
  have hdescent : baseEnd_7732248 < baseStart_7732248 := by decide
  rcases family_descends (prefixWord ++ tailWord_7732248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7732267 : List Nat := [1, 1, 1, 1, 2, 1, 6, 2, 1, 1, 6]
def baseStart_7732267 : Nat := 118140960795 + 7732267 * 2 ^ 59
def prefixEnd_7732267 : Nat := 4983230072969 + 3 ^ 40 * 7732267 * 2
def baseEnd_7732267 : Nat := 3970369519898604203502457

theorem tailTrace_7732267 : CollatzResearch.WordTrace tailWord_7732267 prefixEnd_7732267 3970369519898604203502457 := by
  unfold tailWord_7732267
  simp only [CollatzResearch.WordTrace]
  refine ⟨282018946278324699913075055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188012630852216466608716703 282018946278324699913075055)
  ·
    refine ⟨423028419417487049869612583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 282018946278324699913075055 423028419417487049869612583)
    ·
      refine ⟨634542629126230574804418875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 423028419417487049869612583 634542629126230574804418875)
      ·
        refine ⟨951813943689345862206628313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 634542629126230574804418875 951813943689345862206628313)
        ·
          refine ⟨713860457767009396654971235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 951813943689345862206628313 713860457767009396654971235)
          ·
            refine ⟨1070790686650514094982456853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 713860457767009396654971235 1070790686650514094982456853)
            ·
              refine ⟨50193313436742848202302665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 1070790686650514094982456853 50193313436742848202302665)
              ·
                refine ⟨37644985077557136151726999, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50193313436742848202302665 37644985077557136151726999)
                ·
                  refine ⟨56467477616335704227590499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37644985077557136151726999 56467477616335704227590499)
                  ·
                    refine ⟨84701216424503556341385749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 56467477616335704227590499 84701216424503556341385749)
                    ·
                      refine ⟨3970369519898604203502457, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 84701216424503556341385749 3970369519898604203502457)
                      ·
                        rfl

theorem cell23_7732267_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 6, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 6, 2, 1, 1, 6].length) (baseStart_7732267 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7732267 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7732267 prefixEnd_7732267 := by exact prefixLift 7732267
  have htrace : WordTrace (prefixWord ++ tailWord_7732267) baseStart_7732267 baseEnd_7732267 := by
    simpa [prefixWord, tailWord_7732267, baseEnd_7732267] using wordTrace_append hprefix tailTrace_7732267
  have hstable : (prefixWord ++ tailWord_7732267).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7732267).length < 2 ^ (prefixWord ++ tailWord_7732267).sum := by decide
  have hdescent : baseEnd_7732267 < baseStart_7732267 := by decide
  rcases family_descends (prefixWord ++ tailWord_7732267) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7732274 : List Nat := [3, 2, 1, 1, 2, 2, 3, 2, 1, 1, 5]
def baseStart_7732274 : Nat := 118140960795 + 7732274 * 2 ^ 59
def prefixEnd_7732274 : Nat := 4983230072969 + 3 ^ 40 * 7732274 * 2
def baseEnd_7732274 : Nat := 3970373114263185676114925

theorem tailTrace_7732274 : CollatzResearch.WordTrace tailWord_7732274 prefixEnd_7732274 3970373114263185676114925 := by
  unfold tailWord_7732274
  simp only [CollatzResearch.WordTrace]
  refine ⟨70504800397324835027144969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 188012801059532893405719917 70504800397324835027144969)
  ·
    refine ⟨52878600297993626270358727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70504800397324835027144969 52878600297993626270358727)
    ·
      refine ⟨79317900446990439405538091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52878600297993626270358727 79317900446990439405538091)
      ·
        refine ⟨118976850670485659108307137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79317900446990439405538091 118976850670485659108307137)
        ·
          refine ⟨89232638002864244331230353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 118976850670485659108307137 89232638002864244331230353)
          ·
            refine ⟨66924478502148183248422765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 89232638002864244331230353 66924478502148183248422765)
            ·
              refine ⟨25096679438305568718158537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 66924478502148183248422765 25096679438305568718158537)
              ·
                refine ⟨18822509578729176538618903, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25096679438305568718158537 18822509578729176538618903)
                ·
                  refine ⟨28233764368093764807928355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18822509578729176538618903 28233764368093764807928355)
                  ·
                    refine ⟨42350646552140647211892533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28233764368093764807928355 42350646552140647211892533)
                    ·
                      refine ⟨3970373114263185676114925, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42350646552140647211892533 3970373114263185676114925)
                      ·
                        rfl

theorem cell23_7732274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 3, 2, 1, 1, 5].length) (baseStart_7732274 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7732274 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7732274 prefixEnd_7732274 := by exact prefixLift 7732274
  have htrace : WordTrace (prefixWord ++ tailWord_7732274) baseStart_7732274 baseEnd_7732274 := by
    simpa [prefixWord, tailWord_7732274, baseEnd_7732274] using wordTrace_append hprefix tailTrace_7732274
  have hstable : (prefixWord ++ tailWord_7732274).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7732274).length < 2 ^ (prefixWord ++ tailWord_7732274).sum := by decide
  have hdescent : baseEnd_7732274 < baseStart_7732274 := by decide
  rcases family_descends (prefixWord ++ tailWord_7732274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7732277 : List Nat := [1, 3, 3, 1, 1, 1, 1, 12]
def baseStart_7732277 : Nat := 118140960795 + 7732277 * 2 ^ 59
def prefixEnd_7732277 : Nat := 4983230072969 + 3 ^ 40 * 7732277 * 2
def baseEnd_7732277 : Nat := 147050913137227746828793

theorem tailTrace_7732277 : CollatzResearch.WordTrace tailWord_7732277 prefixEnd_7732277 147050913137227746828793 := by
  unfold tailWord_7732277
  simp only [CollatzResearch.WordTrace]
  refine ⟨282019311008288471620939085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188012874005525647747292723 282019311008288471620939085)
  ·
    refine ⟨105757241628108176857852157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 282019311008288471620939085 105757241628108176857852157)
    ·
      refine ⟨39658965610540566321694559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 105757241628108176857852157 39658965610540566321694559)
      ·
        refine ⟨59488448415810849482541839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39658965610540566321694559 59488448415810849482541839)
        ·
          refine ⟨89232672623716274223812759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59488448415810849482541839 89232672623716274223812759)
          ·
            refine ⟨133849008935574411335719139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89232672623716274223812759 133849008935574411335719139)
            ·
              refine ⟨200773513403361617003578709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 133849008935574411335719139 200773513403361617003578709)
              ·
                refine ⟨147050913137227746828793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 12 200773513403361617003578709 147050913137227746828793)
                ·
                  rfl

theorem cell23_7732277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 1, 12].length) (baseStart_7732277 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7732277 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7732277 prefixEnd_7732277 := by exact prefixLift 7732277
  have htrace : WordTrace (prefixWord ++ tailWord_7732277) baseStart_7732277 baseEnd_7732277 := by
    simpa [prefixWord, tailWord_7732277, baseEnd_7732277] using wordTrace_append hprefix tailTrace_7732277
  have hstable : (prefixWord ++ tailWord_7732277).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7732277).length < 2 ^ (prefixWord ++ tailWord_7732277).sum := by decide
  have hdescent : baseEnd_7732277 < baseStart_7732277 := by decide
  rcases family_descends (prefixWord ++ tailWord_7732277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7732281 : List Nat := [1, 2, 1, 5, 2, 3, 1, 1, 1, 6]
def baseStart_7732281 : Nat := 118140960795 + 7732281 * 2 ^ 59
def prefixEnd_7732281 : Nat := 4983230072969 + 3 ^ 40 * 7732281 * 2
def baseEnd_7732281 : Nat := 1323458902875922382909131

theorem tailTrace_7732281 : CollatzResearch.WordTrace tailWord_7732281 prefixEnd_7732281 1323458902875922382909131 := by
  unfold tailWord_7732281
  simp only [CollatzResearch.WordTrace]
  refine ⟨282019456900273980304084697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188012971266849320202723131 282019456900273980304084697)
  ·
    refine ⟨211514592675205485228063523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 282019456900273980304084697 211514592675205485228063523)
    ·
      refine ⟨317271889012808227842095285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 211514592675205485228063523 317271889012808227842095285)
      ·
        refine ⟨29744239594950771360196433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 317271889012808227842095285 29744239594950771360196433)
        ·
          refine ⟨22308179696213078520147325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29744239594950771360196433 22308179696213078520147325)
          ·
            refine ⟨8365567386079904445055247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22308179696213078520147325 8365567386079904445055247)
            ·
              refine ⟨12548351079119856667582871, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8365567386079904445055247 12548351079119856667582871)
              ·
                refine ⟨18822526618679785001374307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12548351079119856667582871 18822526618679785001374307)
                ·
                  refine ⟨28233789928019677502061461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18822526618679785001374307 28233789928019677502061461)
                  ·
                    refine ⟨1323458902875922382909131, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28233789928019677502061461 1323458902875922382909131)
                    ·
                      rfl

theorem cell23_7732281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 3, 1, 1, 1, 6].length) (baseStart_7732281 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7732281 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7732281 prefixEnd_7732281 := by exact prefixLift 7732281
  have htrace : WordTrace (prefixWord ++ tailWord_7732281) baseStart_7732281 baseEnd_7732281 := by
    simpa [prefixWord, tailWord_7732281, baseEnd_7732281] using wordTrace_append hprefix tailTrace_7732281
  have hstable : (prefixWord ++ tailWord_7732281).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7732281).length < 2 ^ (prefixWord ++ tailWord_7732281).sum := by decide
  have hdescent : baseEnd_7732281 < baseStart_7732281 := by decide
  rcases family_descends (prefixWord ++ tailWord_7732281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7732284 : List Nat := [2, 2, 2, 2, 2, 3, 1, 1, 1, 1, 6]
def baseStart_7732284 : Nat := 118140960795 + 7732284 * 2 ^ 59
def prefixEnd_7732284 : Nat := 4983230072969 + 3 ^ 40 * 7732284 * 2
def baseEnd_7732284 : Nat := 3970378249069730636989879

theorem tailTrace_7732284 : CollatzResearch.WordTrace tailWord_7732284 prefixEnd_7732284 3970378249069730636989879 := by
  unfold tailWord_7732284
  simp only [CollatzResearch.WordTrace]
  refine ⟨141009783159631555908221953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 188013044212842074544295937 141009783159631555908221953)
  ·
    refine ⟨105757337369723666931166465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 141009783159631555908221953 105757337369723666931166465)
    ·
      refine ⟨79318003027292750198374849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 105757337369723666931166465 79318003027292750198374849)
      ·
        refine ⟨59488502270469562648781137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79318003027292750198374849 59488502270469562648781137)
        ·
          refine ⟨44616376702852171986585853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59488502270469562648781137 44616376702852171986585853)
          ·
            refine ⟨16731141263569564494969695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44616376702852171986585853 16731141263569564494969695)
            ·
              refine ⟨25096711895354346742454543, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16731141263569564494969695 25096711895354346742454543)
              ·
                refine ⟨37645067843031520113681815, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25096711895354346742454543 37645067843031520113681815)
                ·
                  refine ⟨56467601764547280170522723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37645067843031520113681815 56467601764547280170522723)
                  ·
                    refine ⟨84701402646820920255784085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 56467601764547280170522723 84701402646820920255784085)
                    ·
                      refine ⟨3970378249069730636989879, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 84701402646820920255784085 3970378249069730636989879)
                      ·
                        rfl

theorem cell23_7732284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 3, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 3, 1, 1, 1, 1, 6].length) (baseStart_7732284 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7732284 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7732284 prefixEnd_7732284 := by exact prefixLift 7732284
  have htrace : WordTrace (prefixWord ++ tailWord_7732284) baseStart_7732284 baseEnd_7732284 := by
    simpa [prefixWord, tailWord_7732284, baseEnd_7732284] using wordTrace_append hprefix tailTrace_7732284
  have hstable : (prefixWord ++ tailWord_7732284).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7732284).length < 2 ^ (prefixWord ++ tailWord_7732284).sum := by decide
  have hdescent : baseEnd_7732284 < baseStart_7732284 := by decide
  rcases family_descends (prefixWord ++ tailWord_7732284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7732291 : List Nat := [1, 1, 1, 3, 1, 2, 6, 2, 1, 2, 3]
def baseStart_7732291 : Nat := 118140960795 + 7732291 * 2 ^ 59
def prefixEnd_7732291 : Nat := 4983230072969 + 3 ^ 40 * 7732291 * 2
def baseEnd_7732291 : Nat := 3970381843434312109602347

theorem tailTrace_7732291 : CollatzResearch.WordTrace tailWord_7732291 prefixEnd_7732291 3970381843434312109602347 := by
  unfold tailWord_7732291
  simp only [CollatzResearch.WordTrace]
  refine ⟨282019821630237752011948727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188013214420158501341299151 282019821630237752011948727)
  ·
    refine ⟨423029732445356628017923091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 282019821630237752011948727 423029732445356628017923091)
    ·
      refine ⟨634544598668034942026884637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 423029732445356628017923091 634544598668034942026884637)
      ·
        refine ⟨237954224500513103260081739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 634544598668034942026884637 237954224500513103260081739)
        ·
          refine ⟨356931336750769654890122609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 237954224500513103260081739 356931336750769654890122609)
          ·
            refine ⟨267698502563077241167591957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 356931336750769654890122609 267698502563077241167591957)
            ·
              refine ⟨12548367307644245679730873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 267698502563077241167591957 12548367307644245679730873)
              ·
                refine ⟨9411275480733184259798155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12548367307644245679730873 9411275480733184259798155)
                ·
                  refine ⟨14116913221099776389697233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9411275480733184259798155 14116913221099776389697233)
                  ·
                    refine ⟨10587684915824832292272925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14116913221099776389697233 10587684915824832292272925)
                    ·
                      refine ⟨3970381843434312109602347, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10587684915824832292272925 3970381843434312109602347)
                      ·
                        rfl

theorem cell23_7732291_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 6, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 6, 2, 1, 2, 3].length) (baseStart_7732291 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7732291 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7732291 prefixEnd_7732291 := by exact prefixLift 7732291
  have htrace : WordTrace (prefixWord ++ tailWord_7732291) baseStart_7732291 baseEnd_7732291 := by
    simpa [prefixWord, tailWord_7732291, baseEnd_7732291] using wordTrace_append hprefix tailTrace_7732291
  have hstable : (prefixWord ++ tailWord_7732291).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7732291).length < 2 ^ (prefixWord ++ tailWord_7732291).sum := by decide
  have hdescent : baseEnd_7732291 < baseStart_7732291 := by decide
  rcases family_descends (prefixWord ++ tailWord_7732291) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7732304 : List Nat := [2, 1, 1, 1, 1, 3, 1, 6, 1, 3, 3]
def baseStart_7732304 : Nat := 118140960795 + 7732304 * 2 ^ 59
def prefixEnd_7732304 : Nat := 4983230072969 + 3 ^ 40 * 7732304 * 2
def baseEnd_7732304 : Nat := 3970388518682820558739787

theorem tailTrace_7732304 : CollatzResearch.WordTrace tailWord_7732304 prefixEnd_7732304 3970388518682820558739787 := by
  unfold tailWord_7732304
  simp only [CollatzResearch.WordTrace]
  refine ⟨141010147889595327616085983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 188013530519460436821447977 141010147889595327616085983)
  ·
    refine ⟨211515221834392991424128975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141010147889595327616085983 211515221834392991424128975)
    ·
      refine ⟨317272832751589487136193463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 211515221834392991424128975 317272832751589487136193463)
      ·
        refine ⟨475909249127384230704290195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 317272832751589487136193463 475909249127384230704290195)
        ·
          refine ⟨713863873691076346056435293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 475909249127384230704290195 713863873691076346056435293)
          ·
            refine ⟨267698952634153629771163235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 713863873691076346056435293 267698952634153629771163235)
            ·
              refine ⟨401548428951230444656744853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 267698952634153629771163235 401548428951230444656744853)
              ·
                refine ⟨18822582607088927093284915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 401548428951230444656744853 18822582607088927093284915)
                ·
                  refine ⟨28233873910633390639927373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18822582607088927093284915 28233873910633390639927373)
                  ·
                    refine ⟨10587702716487521489972765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28233873910633390639927373 10587702716487521489972765)
                    ·
                      refine ⟨3970388518682820558739787, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10587702716487521489972765 3970388518682820558739787)
                      ·
                        rfl

theorem cell23_7732304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 6, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 6, 1, 3, 3].length) (baseStart_7732304 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7732304 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7732304 prefixEnd_7732304 := by exact prefixLift 7732304
  have htrace : WordTrace (prefixWord ++ tailWord_7732304) baseStart_7732304 baseEnd_7732304 := by
    simpa [prefixWord, tailWord_7732304, baseEnd_7732304] using wordTrace_append hprefix tailTrace_7732304
  have hstable : (prefixWord ++ tailWord_7732304).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7732304).length < 2 ^ (prefixWord ++ tailWord_7732304).sum := by decide
  have hdescent : baseEnd_7732304 < baseStart_7732304 := by decide
  rcases family_descends (prefixWord ++ tailWord_7732304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7732305 : List Nat := [1, 2, 2, 1, 3, 1, 5, 3, 1, 2, 2]
def baseStart_7732305 : Nat := 118140960795 + 7732305 * 2 ^ 59
def prefixEnd_7732305 : Nat := 4983230072969 + 3 ^ 40 * 7732305 * 2
def baseEnd_7732305 : Nat := 3970389032163475054827283

theorem tailTrace_7732305 : CollatzResearch.WordTrace tailWord_7732305 prefixEnd_7732305 3970389032163475054827283 := by
  unfold tailWord_7732305
  simp only [CollatzResearch.WordTrace]
  refine ⟨282020332252187032402958369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188013554834791354935305579 282020332252187032402958369)
  ·
    refine ⟨211515249189140274302218777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 282020332252187032402958369 211515249189140274302218777)
    ·
      refine ⟨158636436891855205726664083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 211515249189140274302218777 158636436891855205726664083)
      ·
        refine ⟨237954655337782808589996125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 158636436891855205726664083 237954655337782808589996125)
        ·
          refine ⟨89232995751668553221248547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 237954655337782808589996125 89232995751668553221248547)
          ·
            refine ⟨133849493627502829831872821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89232995751668553221248547 133849493627502829831872821)
            ·
              refine ⟨12548390027578390296738077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 133849493627502829831872821 12548390027578390296738077)
              ·
                refine ⟨4705646260341896361276779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12548390027578390296738077 4705646260341896361276779)
                ·
                  refine ⟨7058469390512844541915169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4705646260341896361276779 7058469390512844541915169)
                  ·
                    refine ⟨5293852042884633406436377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7058469390512844541915169 5293852042884633406436377)
                    ·
                      refine ⟨3970389032163475054827283, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5293852042884633406436377 3970389032163475054827283)
                      ·
                        rfl

theorem cell23_7732305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 5, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 5, 3, 1, 2, 2].length) (baseStart_7732305 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7732305 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7732305 prefixEnd_7732305 := by exact prefixLift 7732305
  have htrace : WordTrace (prefixWord ++ tailWord_7732305) baseStart_7732305 baseEnd_7732305 := by
    simpa [prefixWord, tailWord_7732305, baseEnd_7732305] using wordTrace_append hprefix tailTrace_7732305
  have hstable : (prefixWord ++ tailWord_7732305).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7732305).length < 2 ^ (prefixWord ++ tailWord_7732305).sum := by decide
  have hdescent : baseEnd_7732305 < baseStart_7732305 := by decide
  rcases family_descends (prefixWord ++ tailWord_7732305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7732318 : List Nat := [4, 4, 1, 1, 1, 1, 1, 2, 1, 1, 6]
def baseStart_7732318 : Nat := 118140960795 + 7732318 * 2 ^ 59
def prefixEnd_7732318 : Nat := 4983230072969 + 3 ^ 40 * 7732318 * 2
def baseEnd_7732318 : Nat := 3970395707411983503964723

theorem tailTrace_7732318 : CollatzResearch.WordTrace tailWord_7732318 prefixEnd_7732318 3970395707411983503964723 := by
  unfold tailWord_7732318
  simp only [CollatzResearch.WordTrace]
  refine ⟨35252600800142491952897701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 188013870934093290415454405 35252600800142491952897701)
  ·
    refine ⟨6609862650026717241168319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 35252600800142491952897701 6609862650026717241168319)
    ·
      refine ⟨9914793975040075861752479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6609862650026717241168319 9914793975040075861752479)
      ·
        refine ⟨14872190962560113792628719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9914793975040075861752479 14872190962560113792628719)
        ·
          refine ⟨22308286443840170688943079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14872190962560113792628719 22308286443840170688943079)
          ·
            refine ⟨33462429665760256033414619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22308286443840170688943079 33462429665760256033414619)
            ·
              refine ⟨50193644498640384050121929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33462429665760256033414619 50193644498640384050121929)
              ·
                refine ⟨37645233373980288037591447, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50193644498640384050121929 37645233373980288037591447)
                ·
                  refine ⟨56467850060970432056387171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37645233373980288037591447 56467850060970432056387171)
                  ·
                    refine ⟨84701775091455648084580757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 56467850060970432056387171 84701775091455648084580757)
                    ·
                      refine ⟨3970395707411983503964723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 84701775091455648084580757 3970395707411983503964723)
                      ·
                        rfl

theorem cell23_7732318_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 1, 2, 1, 1, 6].length) (baseStart_7732318 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7732318 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7732318 prefixEnd_7732318 := by exact prefixLift 7732318
  have htrace : WordTrace (prefixWord ++ tailWord_7732318) baseStart_7732318 baseEnd_7732318 := by
    simpa [prefixWord, tailWord_7732318, baseEnd_7732318] using wordTrace_append hprefix tailTrace_7732318
  have hstable : (prefixWord ++ tailWord_7732318).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7732318).length < 2 ^ (prefixWord ++ tailWord_7732318).sum := by decide
  have hdescent : baseEnd_7732318 < baseStart_7732318 := by decide
  rcases family_descends (prefixWord ++ tailWord_7732318) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7732321 : List Nat := [1, 2, 3, 1, 1, 2, 4, 1, 4, 1, 3]
def baseStart_7732321 : Nat := 118140960795 + 7732321 * 2 ^ 59
def prefixEnd_7732321 : Nat := 4983230072969 + 3 ^ 40 * 7732321 * 2
def baseEnd_7732321 : Nat := 3970397247853946992227209

theorem tailTrace_7732321 : CollatzResearch.WordTrace tailWord_7732321 prefixEnd_7732321 3970397247853946992227209 := by
  unfold tailWord_7732321
  simp only [CollatzResearch.WordTrace]
  refine ⟨282020915820129067135540817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188013943880086044757027211 282020915820129067135540817)
  ·
    refine ⟨211515686865096800351655613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 282020915820129067135540817 211515686865096800351655613)
    ·
      refine ⟨79318382574411300131870855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 211515686865096800351655613 79318382574411300131870855)
      ·
        refine ⟨118977573861616950197806283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79318382574411300131870855 118977573861616950197806283)
        ·
          refine ⟨178466360792425425296709425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 118977573861616950197806283 178466360792425425296709425)
          ·
            refine ⟨133849770594319068972532069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 178466360792425425296709425 133849770594319068972532069)
            ·
              refine ⟨25096831986434825432349763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 133849770594319068972532069 25096831986434825432349763)
              ·
                refine ⟨37645247979652238148524645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25096831986434825432349763 37645247979652238148524645)
                ·
                  refine ⟨7058483996184794652848371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 37645247979652238148524645 7058483996184794652848371)
                  ·
                    refine ⟨10587725994277191979272557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7058483996184794652848371 10587725994277191979272557)
                    ·
                      refine ⟨3970397247853946992227209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10587725994277191979272557 3970397247853946992227209)
                      ·
                        rfl

theorem cell23_7732321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 4, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 4, 1, 4, 1, 3].length) (baseStart_7732321 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7732321 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7732321 prefixEnd_7732321 := by exact prefixLift 7732321
  have htrace : WordTrace (prefixWord ++ tailWord_7732321) baseStart_7732321 baseEnd_7732321 := by
    simpa [prefixWord, tailWord_7732321, baseEnd_7732321] using wordTrace_append hprefix tailTrace_7732321
  have hstable : (prefixWord ++ tailWord_7732321).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7732321).length < 2 ^ (prefixWord ++ tailWord_7732321).sum := by decide
  have hdescent : baseEnd_7732321 < baseStart_7732321 := by decide
  rcases family_descends (prefixWord ++ tailWord_7732321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7732322 : List Nat := [3, 3, 2, 2, 1, 3, 1, 1, 3, 2, 2]
def baseStart_7732322 : Nat := 118140960795 + 7732322 * 2 ^ 59
def prefixEnd_7732322 : Nat := 4983230072969 + 3 ^ 40 * 7732322 * 2
def baseEnd_7732322 : Nat := 3970397761334601488314705

theorem tailTrace_7732322 : CollatzResearch.WordTrace tailWord_7732322 prefixEnd_7732322 3970397761334601488314705 := by
  unfold tailWord_7732322
  simp only [CollatzResearch.WordTrace]
  refine ⟨70505238073281361076581805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 188013968195416962870884813 70505238073281361076581805)
  ·
    refine ⟨26439464277480510403718177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 70505238073281361076581805 26439464277480510403718177)
    ·
      refine ⟨19829598208110382802788633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26439464277480510403718177 19829598208110382802788633)
      ·
        refine ⟨14872198656082787102091475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19829598208110382802788633 14872198656082787102091475)
        ·
          refine ⟨22308297984124180653137213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14872198656082787102091475 22308297984124180653137213)
          ·
            refine ⟨8365611744046567744926455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22308297984124180653137213 8365611744046567744926455)
            ·
              refine ⟨12548417616069851617389683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8365611744046567744926455 12548417616069851617389683)
              ·
                refine ⟨18822626424104777426084525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12548417616069851617389683 18822626424104777426084525)
                ·
                  refine ⟨7058484909039291534781697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18822626424104777426084525 7058484909039291534781697)
                  ·
                    refine ⟨5293863681779468651086273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7058484909039291534781697 5293863681779468651086273)
                    ·
                      refine ⟨3970397761334601488314705, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5293863681779468651086273 3970397761334601488314705)
                      ·
                        rfl

theorem cell23_7732322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 3, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 3, 1, 1, 3, 2, 2].length) (baseStart_7732322 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7732322 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7732322 prefixEnd_7732322 := by exact prefixLift 7732322
  have htrace : WordTrace (prefixWord ++ tailWord_7732322) baseStart_7732322 baseEnd_7732322 := by
    simpa [prefixWord, tailWord_7732322, baseEnd_7732322] using wordTrace_append hprefix tailTrace_7732322
  have hstable : (prefixWord ++ tailWord_7732322).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7732322).length < 2 ^ (prefixWord ++ tailWord_7732322).sum := by decide
  have hdescent : baseEnd_7732322 < baseStart_7732322 := by decide
  rcases family_descends (prefixWord ++ tailWord_7732322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7732338 : List Nat := [3, 2, 1, 2, 2, 1, 3, 3, 2, 1, 3]
def baseStart_7732338 : Nat := 118140960795 + 7732338 * 2 ^ 59
def prefixEnd_7732338 : Nat := 4983230072969 + 3 ^ 40 * 7732338 * 2
def baseEnd_7732338 : Nat := 3970405977025073425714631

theorem tailTrace_7732338 : CollatzResearch.WordTrace tailWord_7732338 prefixEnd_7732338 3970405977025073425714631 := by
  unfold tailWord_7732338
  simp only [CollatzResearch.WordTrace]
  refine ⟨70505383965266869759727417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 188014357240711652692606445 70505383965266869759727417)
  ·
    refine ⟨52879037973950152319795563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70505383965266869759727417 52879037973950152319795563)
    ·
      refine ⟨79318556960925228479693345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52879037973950152319795563 79318556960925228479693345)
      ·
        refine ⟨59488917720693921359770009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79318556960925228479693345 59488917720693921359770009)
        ·
          refine ⟨44616688290520441019827507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59488917720693921359770009 44616688290520441019827507)
          ·
            refine ⟨66925032435780661529741261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44616688290520441019827507 66925032435780661529741261)
            ·
              refine ⟨25096887163417748073652973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 66925032435780661529741261 25096887163417748073652973)
              ·
                refine ⟨9411332686281655527619865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25096887163417748073652973 9411332686281655527619865)
                ·
                  refine ⟨7058499514711241645714899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9411332686281655527619865 7058499514711241645714899)
                  ·
                    refine ⟨10587749272066862468572349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7058499514711241645714899 10587749272066862468572349)
                    ·
                      refine ⟨3970405977025073425714631, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10587749272066862468572349 3970405977025073425714631)
                      ·
                        rfl

theorem cell23_7732338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 3, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 3, 3, 2, 1, 3].length) (baseStart_7732338 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7732338 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7732338 prefixEnd_7732338 := by exact prefixLift 7732338
  have htrace : WordTrace (prefixWord ++ tailWord_7732338) baseStart_7732338 baseEnd_7732338 := by
    simpa [prefixWord, tailWord_7732338, baseEnd_7732338] using wordTrace_append hprefix tailTrace_7732338
  have hstable : (prefixWord ++ tailWord_7732338).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7732338).length < 2 ^ (prefixWord ++ tailWord_7732338).sum := by decide
  have hdescent : baseEnd_7732338 < baseStart_7732338 := by decide
  rcases family_descends (prefixWord ++ tailWord_7732338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7732361 : List Nat := [1, 2, 1, 1, 4, 3, 1, 1, 3, 4, 2]
def baseStart_7732361 : Nat := 118140960795 + 7732361 * 2 ^ 59
def prefixEnd_7732361 : Nat := 4983230072969 + 3 ^ 40 * 7732361 * 2
def baseEnd_7732361 : Nat := 3970417787080126835727025

theorem tailTrace_7732361 : CollatzResearch.WordTrace tailWord_7732361 prefixEnd_7732361 3970417787080126835727025 := by
  unfold tailWord_7732361
  simp only [CollatzResearch.WordTrace]
  refine ⟨282022374739984153966996937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188014916493322769311331291 282022374739984153966996937)
  ·
    refine ⟨211516781054988115475247703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 282022374739984153966996937 211516781054988115475247703)
    ·
      refine ⟨317275171582482173212871555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 211516781054988115475247703 317275171582482173212871555)
      ·
        refine ⟨475912757373723259819307333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 317275171582482173212871555 475912757373723259819307333)
        ·
          refine ⟨89233642007573111216120125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 475912757373723259819307333 89233642007573111216120125)
          ·
            refine ⟨33462615752839916706045047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 89233642007573111216120125 33462615752839916706045047)
            ·
              refine ⟨50193923629259875059067571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33462615752839916706045047 50193923629259875059067571)
              ·
                refine ⟨75290885443889812588601357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50193923629259875059067571 75290885443889812588601357)
                ·
                  refine ⟨28234082041458679720725509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 75290885443889812588601357 28234082041458679720725509)
                  ·
                    refine ⟨5293890382773502447636033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28234082041458679720725509 5293890382773502447636033)
                    ·
                      refine ⟨3970417787080126835727025, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5293890382773502447636033 3970417787080126835727025)
                      ·
                        rfl

theorem cell23_7732361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 1, 1, 3, 4, 2].length) (baseStart_7732361 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7732361 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7732361 prefixEnd_7732361 := by exact prefixLift 7732361
  have htrace : WordTrace (prefixWord ++ tailWord_7732361) baseStart_7732361 baseEnd_7732361 := by
    simpa [prefixWord, tailWord_7732361, baseEnd_7732361] using wordTrace_append hprefix tailTrace_7732361
  have hstable : (prefixWord ++ tailWord_7732361).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7732361).length < 2 ^ (prefixWord ++ tailWord_7732361).sum := by decide
  have hdescent : baseEnd_7732361 < baseStart_7732361 := by decide
  rcases family_descends (prefixWord ++ tailWord_7732361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7732364 : List Nat := [2, 2, 1, 2, 1, 1, 1, 2, 4, 4, 3]
def baseStart_7732364 : Nat := 118140960795 + 7732364 * 2 ^ 59
def prefixEnd_7732364 : Nat := 4983230072969 + 3 ^ 40 * 7732364 * 2
def baseEnd_7732364 : Nat := 3970419327522090323989511

theorem tailTrace_7732364 : CollatzResearch.WordTrace tailWord_7732364 prefixEnd_7732364 3970419327522090323989511 := by
  unfold tailWord_7732364
  simp only [CollatzResearch.WordTrace]
  refine ⟨141011242079486642739678073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 188014989439315523652904097 141011242079486642739678073)
  ·
    refine ⟨105758431559614982054758555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 141011242079486642739678073 105758431559614982054758555)
    ·
      refine ⟨158637647339422473082137833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105758431559614982054758555 158637647339422473082137833)
      ·
        refine ⟨118978235504566854811603375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 158637647339422473082137833 118978235504566854811603375)
        ·
          refine ⟨178467353256850282217405063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 118978235504566854811603375 178467353256850282217405063)
          ·
            refine ⟨267701029885275423326107595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 178467353256850282217405063 267701029885275423326107595)
            ·
              refine ⟨401551544827913134989161393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 267701029885275423326107595 401551544827913134989161393)
              ·
                refine ⟨301163658620934851241871045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 401551544827913134989161393 301163658620934851241871045)
                ·
                  refine ⟨56468185991425284607850821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 301163658620934851241871045 56468185991425284607850821)
                  ·
                    refine ⟨10587784873392240863972029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 56468185991425284607850821 10587784873392240863972029)
                    ·
                      refine ⟨3970419327522090323989511, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10587784873392240863972029 3970419327522090323989511)
                      ·
                        rfl

theorem cell23_7732364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 2, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 2, 4, 4, 3].length) (baseStart_7732364 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7732364 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7732364 prefixEnd_7732364 := by exact prefixLift 7732364
  have htrace : WordTrace (prefixWord ++ tailWord_7732364) baseStart_7732364 baseEnd_7732364 := by
    simpa [prefixWord, tailWord_7732364, baseEnd_7732364] using wordTrace_append hprefix tailTrace_7732364
  have hstable : (prefixWord ++ tailWord_7732364).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7732364).length < 2 ^ (prefixWord ++ tailWord_7732364).sum := by decide
  have hdescent : baseEnd_7732364 < baseStart_7732364 := by decide
  rcases family_descends (prefixWord ++ tailWord_7732364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7732384 : List Nat := [2, 1, 1, 4, 2, 1, 2, 3, 7]
def baseStart_7732384 : Nat := 118140960795 + 7732384 * 2 ^ 59
def prefixEnd_7732384 : Nat := 4983230072969 + 3 ^ 40 * 7732384 * 2
def baseEnd_7732384 : Nat := 441158844126131138415491

theorem tailTrace_7732384 : CollatzResearch.WordTrace tailWord_7732384 prefixEnd_7732384 441158844126131138415491 := by
  unfold tailWord_7732384
  simp only [CollatzResearch.WordTrace]
  refine ⟨141011606809450414447542103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 188015475745933885930056137 141011606809450414447542103)
  ·
    refine ⟨211517410214175621671313155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141011606809450414447542103 211517410214175621671313155)
    ·
      refine ⟨317276115321263432506969733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 211517410214175621671313155 317276115321263432506969733)
      ·
        refine ⟨59489271622736893595056825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 317276115321263432506969733 59489271622736893595056825)
        ·
          refine ⟨44616953717052670196292619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59489271622736893595056825 44616953717052670196292619)
          ·
            refine ⟨66925430575579005294438929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44616953717052670196292619 66925430575579005294438929)
            ·
              refine ⟨50194072931684253970829197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66925430575579005294438929 50194072931684253970829197)
              ·
                refine ⟨18822777349381595239060949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 50194072931684253970829197 18822777349381595239060949)
                ·
                  refine ⟨441158844126131138415491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18822777349381595239060949 441158844126131138415491)
                  ·
                    rfl

theorem cell23_7732384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 2, 3, 7].length) (baseStart_7732384 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7732384 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7732384 prefixEnd_7732384 := by exact prefixLift 7732384
  have htrace : WordTrace (prefixWord ++ tailWord_7732384) baseStart_7732384 baseEnd_7732384 := by
    simpa [prefixWord, tailWord_7732384, baseEnd_7732384] using wordTrace_append hprefix tailTrace_7732384
  have hstable : (prefixWord ++ tailWord_7732384).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7732384).length < 2 ^ (prefixWord ++ tailWord_7732384).sum := by decide
  have hdescent : baseEnd_7732384 < baseStart_7732384 := by decide
  rcases family_descends (prefixWord ++ tailWord_7732384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7732391 : List Nat := [1, 1, 6, 2, 1, 1, 1, 1, 1, 4, 4]
def baseStart_7732391 : Nat := 118140960795 + 7732391 * 2 ^ 59
def prefixEnd_7732391 : Nat := 4983230072969 + 3 ^ 40 * 7732391 * 2
def baseEnd_7732391 : Nat := 3970433191499761718351887

theorem tailTrace_7732391 : CollatzResearch.WordTrace tailWord_7732391 prefixEnd_7732391 3970433191499761718351887 := by
  unfold tailWord_7732391
  simp only [CollatzResearch.WordTrace]
  refine ⟨282023468929875469090589027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188015645953250312727059351 282023468929875469090589027)
  ·
    refine ⟨423035203394813203635883541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 282023468929875469090589027 423035203394813203635883541)
    ·
      refine ⟨19829775159131868920432041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 423035203394813203635883541 19829775159131868920432041)
      ·
        refine ⟨14872331369348901690324031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19829775159131868920432041 14872331369348901690324031)
        ·
          refine ⟨22308497054023352535486047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14872331369348901690324031 22308497054023352535486047)
          ·
            refine ⟨33462745581035028803229071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22308497054023352535486047 33462745581035028803229071)
            ·
              refine ⟨50194118371552543204843607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33462745581035028803229071 50194118371552543204843607)
              ·
                refine ⟨75291177557328814807265411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50194118371552543204843607 75291177557328814807265411)
                ·
                  refine ⟨112936766335993222210898117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 75291177557328814807265411 112936766335993222210898117)
                  ·
                    refine ⟨21175643687998729164543397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 112936766335993222210898117 21175643687998729164543397)
                    ·
                      refine ⟨3970433191499761718351887, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21175643687998729164543397 3970433191499761718351887)
                      ·
                        rfl

theorem cell23_7732391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 1, 1, 1, 4, 4].length) (baseStart_7732391 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7732391 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7732391 prefixEnd_7732391 := by exact prefixLift 7732391
  have htrace : WordTrace (prefixWord ++ tailWord_7732391) baseStart_7732391 baseEnd_7732391 := by
    simpa [prefixWord, tailWord_7732391, baseEnd_7732391] using wordTrace_append hprefix tailTrace_7732391
  have hstable : (prefixWord ++ tailWord_7732391).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7732391).length < 2 ^ (prefixWord ++ tailWord_7732391).sum := by decide
  have hdescent : baseEnd_7732391 < baseStart_7732391 := by decide
  rcases family_descends (prefixWord ++ tailWord_7732391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7732401 : List Nat := [1, 2, 2, 5, 1, 2, 1, 2, 7]
def baseStart_7732401 : Nat := 118140960795 + 7732401 * 2 ^ 59
def prefixEnd_7732401 : Nat := 4983230072969 + 3 ^ 40 * 7732401 * 2
def baseEnd_7732401 : Nat := 441159814034034075469649

theorem tailTrace_7732401 : CollatzResearch.WordTrace tailWord_7732401 prefixEnd_7732401 441159814034034075469649 := by
  unfold tailWord_7732401
  simp only [CollatzResearch.WordTrace]
  refine ⟨282023833659839240798453057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188015889106559493865635371 282023833659839240798453057)
  ·
    refine ⟨211517875244879430598839793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 282023833659839240798453057 211517875244879430598839793)
    ·
      refine ⟨158638406433659572949129845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 211517875244879430598839793 158638406433659572949129845)
      ·
        refine ⟨14872350603155584963980923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 158638406433659572949129845 14872350603155584963980923)
        ·
          refine ⟨22308525904733377445971385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14872350603155584963980923 22308525904733377445971385)
          ·
            refine ⟨16731394428550033084478539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22308525904733377445971385 16731394428550033084478539)
            ·
              refine ⟨25097091642825049626717809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16731394428550033084478539 25097091642825049626717809)
              ·
                refine ⟨18822818732118787220038357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25097091642825049626717809 18822818732118787220038357)
                ·
                  refine ⟨441159814034034075469649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18822818732118787220038357 441159814034034075469649)
                  ·
                    rfl

theorem cell23_7732401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 2, 1, 2, 7].length) (baseStart_7732401 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7732401 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7732401 prefixEnd_7732401 := by exact prefixLift 7732401
  have htrace : WordTrace (prefixWord ++ tailWord_7732401) baseStart_7732401 baseEnd_7732401 := by
    simpa [prefixWord, tailWord_7732401, baseEnd_7732401] using wordTrace_append hprefix tailTrace_7732401
  have hstable : (prefixWord ++ tailWord_7732401).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7732401).length < 2 ^ (prefixWord ++ tailWord_7732401).sum := by decide
  have hdescent : baseEnd_7732401 < baseStart_7732401 := by decide
  rcases family_descends (prefixWord ++ tailWord_7732401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7732424 : List Nat := [2, 1, 3, 1, 2, 1, 2, 1, 3, 2, 5]
def baseStart_7732424 : Nat := 118140960795 + 7732424 * 2 ^ 59
def prefixEnd_7732424 : Nat := 4983230072969 + 3 ^ 40 * 7732424 * 2
def baseEnd_7732424 : Nat := 3970450136361360089239235

theorem tailTrace_7732424 : CollatzResearch.WordTrace tailWord_7732424 prefixEnd_7732424 3970450136361360089239235 := by
  unfold tailWord_7732424
  simp only [CollatzResearch.WordTrace]
  refine ⟨141012336269377957863270163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 188016448359170610484360217 141012336269377957863270163)
  ·
    refine ⟨211518504404066936794905245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141012336269377957863270163 211518504404066936794905245)
    ·
      refine ⟨79319439151525101298089467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 211518504404066936794905245 79319439151525101298089467)
      ·
        refine ⟨118979158727287651947134201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79319439151525101298089467 118979158727287651947134201)
        ·
          refine ⟨89234369045465738960350651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 118979158727287651947134201 89234369045465738960350651)
          ·
            refine ⟨133851553568198608440525977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89234369045465738960350651 133851553568198608440525977)
            ·
              refine ⟨100388665176148956330394483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 133851553568198608440525977 100388665176148956330394483)
              ·
                refine ⟨150582997764223434495591725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 100388665176148956330394483 150582997764223434495591725)
                ·
                  refine ⟨56468624161583787935846897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 150582997764223434495591725 56468624161583787935846897)
                  ·
                    refine ⟨42351468121187840951885173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 56468624161583787935846897 42351468121187840951885173)
                    ·
                      refine ⟨3970450136361360089239235, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42351468121187840951885173 3970450136361360089239235)
                      ·
                        rfl

theorem cell23_7732424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 2, 1, 3, 2, 5].length) (baseStart_7732424 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7732424 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7732424 prefixEnd_7732424 := by exact prefixLift 7732424
  have htrace : WordTrace (prefixWord ++ tailWord_7732424) baseStart_7732424 baseEnd_7732424 := by
    simpa [prefixWord, tailWord_7732424, baseEnd_7732424] using wordTrace_append hprefix tailTrace_7732424
  have hstable : (prefixWord ++ tailWord_7732424).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7732424).length < 2 ^ (prefixWord ++ tailWord_7732424).sum := by decide
  have hdescent : baseEnd_7732424 < baseStart_7732424 := by decide
  rcases family_descends (prefixWord ++ tailWord_7732424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7732429 : List Nat := [1, 6, 2, 2, 1, 1, 1, 1, 4, 2, 2]
def baseStart_7732429 : Nat := 118140960795 + 7732429 * 2 ^ 59
def prefixEnd_7732429 : Nat := 4983230072969 + 3 ^ 40 * 7732429 * 2
def baseEnd_7732429 : Nat := 3970452703764632569676713

theorem tailTrace_7732429 : CollatzResearch.WordTrace tailWord_7732429 prefixEnd_7732429 3970452703764632569676713 := by
  unfold tailWord_7732429
  simp only [CollatzResearch.WordTrace]
  refine ⟨282024854903737801580472341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188016569935825201053648227 282024854903737801580472341)
  ·
    refine ⟨13219915073612709449084641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 282024854903737801580472341 13219915073612709449084641)
    ·
      refine ⟨9914936305209532086813481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13219915073612709449084641 9914936305209532086813481)
      ·
        refine ⟨7436202228907149065110111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9914936305209532086813481 7436202228907149065110111)
        ·
          refine ⟨11154303343360723597665167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7436202228907149065110111 11154303343360723597665167)
          ·
            refine ⟨16731455015041085396497751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11154303343360723597665167 16731455015041085396497751)
            ·
              refine ⟨25097182522561628094746627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16731455015041085396497751 25097182522561628094746627)
              ·
                refine ⟨37645773783842442142119941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25097182522561628094746627 37645773783842442142119941)
                ·
                  refine ⟨7058582584470457901647489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 37645773783842442142119941 7058582584470457901647489)
                  ·
                    refine ⟨5293936938352843426235617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7058582584470457901647489 5293936938352843426235617)
                    ·
                      refine ⟨3970452703764632569676713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5293936938352843426235617 3970452703764632569676713)
                      ·
                        rfl

theorem cell23_7732429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 1, 1, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 1, 1, 1, 1, 4, 2, 2].length) (baseStart_7732429 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7732429 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7732429 prefixEnd_7732429 := by exact prefixLift 7732429
  have htrace : WordTrace (prefixWord ++ tailWord_7732429) baseStart_7732429 baseEnd_7732429 := by
    simpa [prefixWord, tailWord_7732429, baseEnd_7732429] using wordTrace_append hprefix tailTrace_7732429
  have hstable : (prefixWord ++ tailWord_7732429).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7732429).length < 2 ^ (prefixWord ++ tailWord_7732429).sum := by decide
  have hdescent : baseEnd_7732429 < baseStart_7732429 := by decide
  rcases family_descends (prefixWord ++ tailWord_7732429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7732474 : List Nat := [3, 1, 1, 1, 1, 4, 1, 1, 10]
def baseStart_7732474 : Nat := 118140960795 + 7732474 * 2 ^ 59
def prefixEnd_7732474 : Nat := 4983230072969 + 3 ^ 40 * 7732474 * 2
def baseEnd_7732474 : Nat := 441163978932676099290445

theorem tailTrace_7732474 : CollatzResearch.WordTrace tailWord_7732474 prefixEnd_7732474 441163978932676099290445 := by
  unfold tailWord_7732474
  simp only [CollatzResearch.WordTrace]
  refine ⟨70506624047143693566465119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 188017664125716516177240317 70506624047143693566465119)
  ·
    refine ⟨105759936070715540349697679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70506624047143693566465119 105759936070715540349697679)
    ·
      refine ⟨158639904106073310524546519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105759936070715540349697679 158639904106073310524546519)
      ·
        refine ⟨237959856159109965786819779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 158639904106073310524546519 237959856159109965786819779)
        ·
          refine ⟨356939784238664948680229669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 237959856159109965786819779 356939784238664948680229669)
          ·
            refine ⟨66926209544749677877543063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 356939784238664948680229669 66926209544749677877543063)
            ·
              refine ⟨100389314317124516816314595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66926209544749677877543063 100389314317124516816314595)
              ·
                refine ⟨150583971475686775224471893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 100389314317124516816314595 150583971475686775224471893)
                ·
                  refine ⟨441163978932676099290445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 150583971475686775224471893 441163978932676099290445)
                  ·
                    rfl

theorem cell23_7732474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 1, 1, 10].length) (baseStart_7732474 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7732474 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7732474 prefixEnd_7732474 := by exact prefixLift 7732474
  have htrace : WordTrace (prefixWord ++ tailWord_7732474) baseStart_7732474 baseEnd_7732474 := by
    simpa [prefixWord, tailWord_7732474, baseEnd_7732474] using wordTrace_append hprefix tailTrace_7732474
  have hstable : (prefixWord ++ tailWord_7732474).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7732474).length < 2 ^ (prefixWord ++ tailWord_7732474).sum := by decide
  have hdescent : baseEnd_7732474 < baseStart_7732474 := by decide
  rcases family_descends (prefixWord ++ tailWord_7732474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7732508 : List Nat := [2, 2, 3, 1, 1, 1, 6, 1, 6]
def baseStart_7732508 : Nat := 118140960795 + 7732508 * 2 ^ 59
def prefixEnd_7732508 : Nat := 4983230072969 + 3 ^ 40 * 7732508 * 2
def baseEnd_7732508 : Nat := 441165918748481973398761

theorem tailTrace_7732508 : CollatzResearch.WordTrace tailWord_7732508 prefixEnd_7732508 441165918748481973398761 := by
  unfold tailWord_7732508
  simp only [CollatzResearch.WordTrace]
  refine ⟨141013868135225799036299089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 188018490846967732048398785 141013868135225799036299089)
  ·
    refine ⟨105760401101419349277224317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 141013868135225799036299089 105760401101419349277224317)
    ·
      refine ⟨39660150413032255978959119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 105760401101419349277224317 39660150413032255978959119)
      ·
        refine ⟨59490225619548383968438679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39660150413032255978959119 59490225619548383968438679)
        ·
          refine ⟨89235338429322575952658019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59490225619548383968438679 89235338429322575952658019)
          ·
            refine ⟨133853007643983863928987029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89235338429322575952658019 133853007643983863928987029)
            ·
              refine ⟨6274359733311743621671267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 133853007643983863928987029 6274359733311743621671267)
              ·
                refine ⟨9411539599967615432506901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6274359733311743621671267 9411539599967615432506901)
                ·
                  refine ⟨441165918748481973398761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9411539599967615432506901 441165918748481973398761)
                  ·
                    rfl

theorem cell23_7732508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 6, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 6, 1, 6].length) (baseStart_7732508 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7732508 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7732508 prefixEnd_7732508 := by exact prefixLift 7732508
  have htrace : WordTrace (prefixWord ++ tailWord_7732508) baseStart_7732508 baseEnd_7732508 := by
    simpa [prefixWord, tailWord_7732508, baseEnd_7732508] using wordTrace_append hprefix tailTrace_7732508
  have hstable : (prefixWord ++ tailWord_7732508).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7732508).length < 2 ^ (prefixWord ++ tailWord_7732508).sum := by decide
  have hdescent : baseEnd_7732508 < baseStart_7732508 := by decide
  rcases family_descends (prefixWord ++ tailWord_7732508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7732561 : List Nat := [1, 2, 2, 1, 4, 1, 2, 1, 3, 1, 5]
def baseStart_7732561 : Nat := 118140960795 + 7732561 * 2 ^ 59
def prefixEnd_7732561 : Nat := 4983230072969 + 3 ^ 40 * 7732561 * 2
def baseEnd_7732561 : Nat := 3970520483211026053226105

theorem tailTrace_7732561 : CollatzResearch.WordTrace tailWord_7732561 prefixEnd_7732561 3970520483211026053226105 := by
  unfold tailWord_7732561
  simp only [CollatzResearch.WordTrace]
  refine ⟨282029669339259588124277537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188019779559506392082851691 282029669339259588124277537)
  ·
    refine ⟨211522252004444691093208153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 282029669339259588124277537 211522252004444691093208153)
    ·
      refine ⟨158641689003333518319906115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 211522252004444691093208153 158641689003333518319906115)
      ·
        refine ⟨237962533505000277479859173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 158641689003333518319906115 237962533505000277479859173)
        ·
          refine ⟨44617975032187552027473595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 237962533505000277479859173 44617975032187552027473595)
          ·
            refine ⟨66926962548281328041210393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44617975032187552027473595 66926962548281328041210393)
            ·
              refine ⟨50195221911210996030907795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66926962548281328041210393 50195221911210996030907795)
              ·
                refine ⟨75292832866816494046361693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50195221911210996030907795 75292832866816494046361693)
                ·
                  refine ⟨28234812325056185267385635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 75292832866816494046361693 28234812325056185267385635)
                  ·
                    refine ⟨42352218487584277901078453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28234812325056185267385635 42352218487584277901078453)
                    ·
                      refine ⟨3970520483211026053226105, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42352218487584277901078453 3970520483211026053226105)
                      ·
                        rfl

theorem cell23_7732561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 2, 1, 3, 1, 5].length) (baseStart_7732561 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7732561 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7732561 prefixEnd_7732561 := by exact prefixLift 7732561
  have htrace : WordTrace (prefixWord ++ tailWord_7732561) baseStart_7732561 baseEnd_7732561 := by
    simpa [prefixWord, tailWord_7732561, baseEnd_7732561] using wordTrace_append hprefix tailTrace_7732561
  have hstable : (prefixWord ++ tailWord_7732561).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7732561).length < 2 ^ (prefixWord ++ tailWord_7732561).sum := by decide
  have hdescent : baseEnd_7732561 < baseStart_7732561 := by decide
  rcases family_descends (prefixWord ++ tailWord_7732561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7732568 : List Nat := [2, 1, 2, 2, 1, 1, 3, 5, 2, 4]
def baseStart_7732568 : Nat := 118140960795 + 7732568 * 2 ^ 59
def prefixEnd_7732568 : Nat := 4983230072969 + 3 ^ 40 * 7732568 * 2
def baseEnd_7732568 : Nat := 1323508025858535841946191

theorem tailTrace_7732568 : CollatzResearch.WordTrace tailWord_7732568 prefixEnd_7732568 1323508025858535841946191 := by
  unfold tailWord_7732568
  simp only [CollatzResearch.WordTrace]
  refine ⟨141014962325117114159891179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 188019949766822818879854905 141014962325117114159891179)
  ·
    refine ⟨211522443487675671239836769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141014962325117114159891179 211522443487675671239836769)
    ·
      refine ⟨158641832615756753429877577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 211522443487675671239836769 158641832615756753429877577)
      ·
        refine ⟨118981374461817565072408183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 158641832615756753429877577 118981374461817565072408183)
        ·
          refine ⟨178472061692726347608612275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 118981374461817565072408183 178472061692726347608612275)
          ·
            refine ⟨267708092539089521412918413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 178472061692726347608612275 267708092539089521412918413)
            ·
              refine ⟨100390534702158570529844405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 267708092539089521412918413 100390534702158570529844405)
              ·
                refine ⟨9411612628327365987172913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 100390534702158570529844405 9411612628327365987172913)
                ·
                  refine ⟨7058709471245524490379685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9411612628327365987172913 7058709471245524490379685)
                  ·
                    refine ⟨1323508025858535841946191, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7058709471245524490379685 1323508025858535841946191)
                    ·
                      rfl

theorem cell23_7732568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 3, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 3, 5, 2, 4].length) (baseStart_7732568 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7732568 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7732568 prefixEnd_7732568 := by exact prefixLift 7732568
  have htrace : WordTrace (prefixWord ++ tailWord_7732568) baseStart_7732568 baseEnd_7732568 := by
    simpa [prefixWord, tailWord_7732568, baseEnd_7732568] using wordTrace_append hprefix tailTrace_7732568
  have hstable : (prefixWord ++ tailWord_7732568).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7732568).length < 2 ^ (prefixWord ++ tailWord_7732568).sum := by decide
  have hdescent : baseEnd_7732568 < baseStart_7732568 := by decide
  rcases family_descends (prefixWord ++ tailWord_7732568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7732588 : List Nat := [2, 2, 1, 1, 5, 1, 2, 2, 1, 2, 4]
def baseStart_7732588 : Nat := 118140960795 + 7732588 * 2 ^ 59
def prefixEnd_7732588 : Nat := 4983230072969 + 3 ^ 40 * 7732588 * 2
def baseEnd_7732588 : Nat := 3970534347188697447588481

theorem tailTrace_7732588 : CollatzResearch.WordTrace tailWord_7732588 prefixEnd_7732588 3970534347188697447588481 := by
  unfold tailWord_7732588
  simp only [CollatzResearch.WordTrace]
  refine ⟨141015327055080885867755209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 188020436073441181157006945 141015327055080885867755209)
  ·
    refine ⟨105761495291310664400816407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 141015327055080885867755209 105761495291310664400816407)
    ·
      refine ⟨158642242936965996601224611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105761495291310664400816407 158642242936965996601224611)
      ·
        refine ⟨237963364405448994901836917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 158642242936965996601224611 237963364405448994901836917)
        ·
          refine ⟨22309065413010843272047211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 237963364405448994901836917 22309065413010843272047211)
          ·
            refine ⟨33463598119516264908070817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22309065413010843272047211 33463598119516264908070817)
            ·
              refine ⟨25097698589637198681053113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33463598119516264908070817 25097698589637198681053113)
              ·
                refine ⟨18823273942227899010789835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25097698589637198681053113 18823273942227899010789835)
                ·
                  refine ⟨28234910913341848516184753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18823273942227899010789835 28234910913341848516184753)
                  ·
                    refine ⟨21176183185006386387138565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28234910913341848516184753 21176183185006386387138565)
                    ·
                      refine ⟨3970534347188697447588481, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21176183185006386387138565 3970534347188697447588481)
                      ·
                        rfl

theorem cell23_7732588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 2, 4].length) (baseStart_7732588 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7732588 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7732588 prefixEnd_7732588 := by exact prefixLift 7732588
  have htrace : WordTrace (prefixWord ++ tailWord_7732588) baseStart_7732588 baseEnd_7732588 := by
    simpa [prefixWord, tailWord_7732588, baseEnd_7732588] using wordTrace_append hprefix tailTrace_7732588
  have hstable : (prefixWord ++ tailWord_7732588).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7732588).length < 2 ^ (prefixWord ++ tailWord_7732588).sum := by decide
  have hdescent : baseEnd_7732588 < baseStart_7732588 := by decide
  rcases family_descends (prefixWord ++ tailWord_7732588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7732609 : List Nat := [1, 2, 4, 3, 2, 1, 2, 1, 3, 2, 2]
def baseStart_7732609 : Nat := 118140960795 + 7732609 * 2 ^ 59
def prefixEnd_7732609 : Nat := 4983230072969 + 3 ^ 40 * 7732609 * 2
def baseEnd_7732609 : Nat := 3970545130282441865425885

theorem tailTrace_7732609 : CollatzResearch.WordTrace tailWord_7732609 prefixEnd_7732609 3970545130282441865425885 := by
  unfold tailWord_7732609
  simp only [CollatzResearch.WordTrace]
  refine ⟨282031420043085692322024881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188020946695390461548016587 282031420043085692322024881)
  ·
    refine ⟨211523565032314269241518661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 282031420043085692322024881 211523565032314269241518661)
    ·
      refine ⟨39660668443558925482784749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 211523565032314269241518661 39660668443558925482784749)
      ·
        refine ⟨14872750666334597056044281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39660668443558925482784749 14872750666334597056044281)
        ·
          refine ⟨11154562999750947792033211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14872750666334597056044281 11154562999750947792033211)
          ·
            refine ⟨16731844499626421688049817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11154562999750947792033211 16731844499626421688049817)
            ·
              refine ⟨12548883374719816266037363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16731844499626421688049817 12548883374719816266037363)
              ·
                refine ⟨18823325062079724399056045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12548883374719816266037363 18823325062079724399056045)
                ·
                  refine ⟨7058746898279896649646017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18823325062079724399056045 7058746898279896649646017)
                  ·
                    refine ⟨5294060173709922487234513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7058746898279896649646017 5294060173709922487234513)
                    ·
                      refine ⟨3970545130282441865425885, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5294060173709922487234513 3970545130282441865425885)
                      ·
                        rfl

theorem cell23_7732609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 2, 1, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 2, 1, 2, 1, 3, 2, 2].length) (baseStart_7732609 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7732609 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7732609 prefixEnd_7732609 := by exact prefixLift 7732609
  have htrace : WordTrace (prefixWord ++ tailWord_7732609) baseStart_7732609 baseEnd_7732609 := by
    simpa [prefixWord, tailWord_7732609, baseEnd_7732609] using wordTrace_append hprefix tailTrace_7732609
  have hstable : (prefixWord ++ tailWord_7732609).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7732609).length < 2 ^ (prefixWord ++ tailWord_7732609).sum := by decide
  have hdescent : baseEnd_7732609 < baseStart_7732609 := by decide
  rcases family_descends (prefixWord ++ tailWord_7732609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7732622 : List Nat := [4, 1, 1, 4, 2, 2, 1, 1, 1, 2, 4]
def baseStart_7732622 : Nat := 118140960795 + 7732622 * 2 ^ 59
def prefixEnd_7732622 : Nat := 4983230072969 + 3 ^ 40 * 7732622 * 2
def baseEnd_7732622 : Nat := 3970551805530950314563325

theorem tailTrace_7732622 : CollatzResearch.WordTrace tailWord_7732622 prefixEnd_7732622 3970551805530950314563325 := by
  unfold tailWord_7732622
  simp only [CollatzResearch.WordTrace]
  refine ⟨35253986774004824442781015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 188021262794692397028165413 35253986774004824442781015)
  ·
    refine ⟨52880980161007236664171523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35253986774004824442781015 52880980161007236664171523)
    ·
      refine ⟨79321470241510854996257285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52880980161007236664171523 79321470241510854996257285)
      ·
        refine ⟨14872775670283285311798241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 79321470241510854996257285 14872775670283285311798241)
        ·
          refine ⟨11154581752712463983848681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14872775670283285311798241 11154581752712463983848681)
          ·
            refine ⟨8365936314534347987886511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11154581752712463983848681 8365936314534347987886511)
            ·
              refine ⟨12548904471801521981829767, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8365936314534347987886511 12548904471801521981829767)
              ·
                refine ⟨18823356707702282972744651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12548904471801521981829767 18823356707702282972744651)
                ·
                  refine ⟨28235035061553424459116977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18823356707702282972744651 28235035061553424459116977)
                  ·
                    refine ⟨21176276296165068344337733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28235035061553424459116977 21176276296165068344337733)
                    ·
                      refine ⟨3970551805530950314563325, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21176276296165068344337733 3970551805530950314563325)
                      ·
                        rfl

theorem cell23_7732622_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 2, 2, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 2, 2, 1, 1, 1, 2, 4].length) (baseStart_7732622 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7732622 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7732622 prefixEnd_7732622 := by exact prefixLift 7732622
  have htrace : WordTrace (prefixWord ++ tailWord_7732622) baseStart_7732622 baseEnd_7732622 := by
    simpa [prefixWord, tailWord_7732622, baseEnd_7732622] using wordTrace_append hprefix tailTrace_7732622
  have hstable : (prefixWord ++ tailWord_7732622).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7732622).length < 2 ^ (prefixWord ++ tailWord_7732622).sum := by decide
  have hdescent : baseEnd_7732622 < baseStart_7732622 := by decide
  rcases family_descends (prefixWord ++ tailWord_7732622) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7732632 : List Nat := [2, 1, 2, 5, 3, 1, 2, 7]
def baseStart_7732632 : Nat := 118140960795 + 7732632 * 2 ^ 59
def prefixEnd_7732632 : Nat := 4983230072969 + 3 ^ 40 * 7732632 * 2
def baseEnd_7732632 : Nat := 147057664456944269460677

theorem tailTrace_7732632 : CollatzResearch.WordTrace tailWord_7732632 prefixEnd_7732632 147057664456944269460677 := by
  unfold tailWord_7732632
  simp only [CollatzResearch.WordTrace]
  refine ⟨141016129461001183625056075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 188021505948001578166741433 141016129461001183625056075)
  ·
    refine ⟨211524194191501775437584113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141016129461001183625056075 211524194191501775437584113)
    ·
      refine ⟨158643145643626331578188085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 211524194191501775437584113 158643145643626331578188085)
      ·
        refine ⟨14872794904089968585455133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 158643145643626331578188085 14872794904089968585455133)
        ·
          refine ⟨5577298089033738219545675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14872794904089968585455133 5577298089033738219545675)
          ·
            refine ⟨8365947133550607329318513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5577298089033738219545675 8365947133550607329318513)
            ·
              refine ⟨6274460350162955496988885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8365947133550607329318513 6274460350162955496988885)
              ·
                refine ⟨147057664456944269460677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6274460350162955496988885 147057664456944269460677)
                ·
                  rfl

theorem cell23_7732632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 3, 1, 2, 7].length) (baseStart_7732632 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7732632 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7732632 prefixEnd_7732632 := by exact prefixLift 7732632
  have htrace : WordTrace (prefixWord ++ tailWord_7732632) baseStart_7732632 baseEnd_7732632 := by
    simpa [prefixWord, tailWord_7732632, baseEnd_7732632] using wordTrace_append hprefix tailTrace_7732632
  have hstable : (prefixWord ++ tailWord_7732632).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7732632).length < 2 ^ (prefixWord ++ tailWord_7732632).sum := by decide
  have hdescent : baseEnd_7732632 < baseStart_7732632 := by decide
  rcases family_descends (prefixWord ++ tailWord_7732632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7732676 : List Nat := [2, 3, 3, 2, 1, 3, 2, 1, 2, 1, 3]
def baseStart_7732676 : Nat := 118140960795 + 7732676 * 2 ^ 59
def prefixEnd_7732676 : Nat := 4983230072969 + 3 ^ 40 * 7732676 * 2
def baseEnd_7732676 : Nat := 3970579533486293103288077

theorem tailTrace_7732676 : CollatzResearch.WordTrace tailWord_7732676 prefixEnd_7732676 3970579533486293103288077 := by
  unfold tailWord_7732676
  simp only [CollatzResearch.WordTrace]
  refine ⟨141016931866921481382356941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 188022575822561975176475921 141016931866921481382356941)
  ·
    refine ⟨52881349450095555518383853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 141016931866921481382356941 52881349450095555518383853)
    ·
      refine ⟨19830506043785833319393945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 52881349450095555518383853 19830506043785833319393945)
      ·
        refine ⟨14872879532839374989545459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19830506043785833319393945 14872879532839374989545459)
        ·
          refine ⟨22309319299259062484318189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14872879532839374989545459 22309319299259062484318189)
          ·
            refine ⟨8365994737222148431619321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22309319299259062484318189 8365994737222148431619321)
            ·
              refine ⟨6274496052916611323714491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8365994737222148431619321 6274496052916611323714491)
              ·
                refine ⟨9411744079374916985571737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6274496052916611323714491 9411744079374916985571737)
                ·
                  refine ⟨7058808059531187739178803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9411744079374916985571737 7058808059531187739178803)
                  ·
                    refine ⟨10588212089296781608768205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7058808059531187739178803 10588212089296781608768205)
                    ·
                      refine ⟨3970579533486293103288077, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10588212089296781608768205 3970579533486293103288077)
                      ·
                        rfl

theorem cell23_7732676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 3, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 3, 2, 1, 2, 1, 3].length) (baseStart_7732676 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7732676 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7732676 prefixEnd_7732676 := by exact prefixLift 7732676
  have htrace : WordTrace (prefixWord ++ tailWord_7732676) baseStart_7732676 baseEnd_7732676 := by
    simpa [prefixWord, tailWord_7732676, baseEnd_7732676] using wordTrace_append hprefix tailTrace_7732676
  have hstable : (prefixWord ++ tailWord_7732676).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7732676).length < 2 ^ (prefixWord ++ tailWord_7732676).sum := by decide
  have hdescent : baseEnd_7732676 < baseStart_7732676 := by decide
  rcases family_descends (prefixWord ++ tailWord_7732676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7732722 : List Nat := [3, 2, 1, 4, 1, 2, 1, 4, 5]
def baseStart_7732722 : Nat := 118140960795 + 7732722 * 2 ^ 59
def prefixEnd_7732722 : Nat := 4983230072969 + 3 ^ 40 * 7732722 * 2
def baseEnd_7732722 : Nat := 441178128177377769256985

theorem tailTrace_7732722 : CollatzResearch.WordTrace tailWord_7732722 prefixEnd_7732722 441178128177377769256985 := by
  unfold tailWord_7732722
  simp only [CollatzResearch.WordTrace]
  refine ⟨70508885372919078155222105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 188023694327784208413925613 70508885372919078155222105)
  ·
    refine ⟨52881664029689308616416579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70508885372919078155222105 52881664029689308616416579)
    ·
      refine ⟨79322496044533962924624869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52881664029689308616416579 79322496044533962924624869)
      ·
        refine ⟨14872968008350118048367163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 79322496044533962924624869 14872968008350118048367163)
        ·
          refine ⟨22309452012525177072550745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14872968008350118048367163 22309452012525177072550745)
          ·
            refine ⟨16732089009393882804413059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22309452012525177072550745 16732089009393882804413059)
            ·
              refine ⟨25098133514090824206619589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16732089009393882804413059 25098133514090824206619589)
              ·
                refine ⟨4705900033892029538741173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25098133514090824206619589 4705900033892029538741173)
                ·
                  refine ⟨441178128177377769256985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4705900033892029538741173 441178128177377769256985)
                  ·
                    rfl

theorem cell23_7732722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 2, 1, 4, 5].length) (baseStart_7732722 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7732722 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7732722 prefixEnd_7732722 := by exact prefixLift 7732722
  have htrace : WordTrace (prefixWord ++ tailWord_7732722) baseStart_7732722 baseEnd_7732722 := by
    simpa [prefixWord, tailWord_7732722, baseEnd_7732722] using wordTrace_append hprefix tailTrace_7732722
  have hstable : (prefixWord ++ tailWord_7732722).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7732722).length < 2 ^ (prefixWord ++ tailWord_7732722).sum := by decide
  have hdescent : baseEnd_7732722 < baseStart_7732722 := by decide
  rcases family_descends (prefixWord ++ tailWord_7732722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7732728 : List Nat := [2, 1, 2, 1, 1, 5, 2, 1, 1, 2, 5]
def baseStart_7732728 : Nat := 118140960795 + 7732728 * 2 ^ 59
def prefixEnd_7732728 : Nat := 4983230072969 + 3 ^ 40 * 7732728 * 2
def baseEnd_7732728 : Nat := 3970606234480326899837837

theorem tailTrace_7732728 : CollatzResearch.WordTrace tailWord_7732728 prefixEnd_7732728 3970606234480326899837837 := by
  unfold tailWord_7732728
  simp only [CollatzResearch.WordTrace]
  refine ⟨141017880164827287822803419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 188023840219769717097071225 141017880164827287822803419)
  ·
    refine ⟨211526820247240931734205129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141017880164827287822803419 211526820247240931734205129)
    ·
      refine ⟨158645115185430698800653847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 211526820247240931734205129 158645115185430698800653847)
      ·
        refine ⟨237967672778146048200980771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 158645115185430698800653847 237967672778146048200980771)
        ·
          refine ⟨356951509167219072301471157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 237967672778146048200980771 356951509167219072301471157)
          ·
            refine ⟨33464203984426788028262921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 356951509167219072301471157 33464203984426788028262921)
            ·
              refine ⟨25098152988320091021197191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33464203984426788028262921 25098152988320091021197191)
              ·
                refine ⟨37647229482480136531795787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25098152988320091021197191 37647229482480136531795787)
                ·
                  refine ⟨56470844223720204797693681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37647229482480136531795787 56470844223720204797693681)
                  ·
                    refine ⟨42353133167790153598270261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 56470844223720204797693681 42353133167790153598270261)
                    ·
                      refine ⟨3970606234480326899837837, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42353133167790153598270261 3970606234480326899837837)
                      ·
                        rfl

theorem cell23_7732728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 2, 1, 1, 2, 5].length) (baseStart_7732728 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7732728 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7732728 prefixEnd_7732728 := by exact prefixLift 7732728
  have htrace : WordTrace (prefixWord ++ tailWord_7732728) baseStart_7732728 baseEnd_7732728 := by
    simpa [prefixWord, tailWord_7732728, baseEnd_7732728] using wordTrace_append hprefix tailTrace_7732728
  have hstable : (prefixWord ++ tailWord_7732728).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7732728).length < 2 ^ (prefixWord ++ tailWord_7732728).sum := by decide
  have hdescent : baseEnd_7732728 < baseStart_7732728 := by decide
  rcases family_descends (prefixWord ++ tailWord_7732728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7732755 : List Nat := [1, 1, 1, 2, 1, 6, 3, 1, 2, 1, 4]
def baseStart_7732755 : Nat := 118140960795 + 7732755 * 2 ^ 59
def prefixEnd_7732755 : Nat := 4983230072969 + 3 ^ 40 * 7732755 * 2
def baseEnd_7732755 : Nat := 3970620098457998294200213

theorem tailTrace_7732755 : CollatzResearch.WordTrace tailWord_7732755 prefixEnd_7732755 3970620098457998294200213 := by
  unfold tailWord_7732755
  simp only [CollatzResearch.WordTrace]
  refine ⟨282036745100556759256839719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188024496733704506171226479 282036745100556759256839719)
  ·
    refine ⟨423055117650835138885259579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 282036745100556759256839719 423055117650835138885259579)
    ·
      refine ⟨634582676476252708327889369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 423055117650835138885259579 634582676476252708327889369)
      ·
        refine ⟨475937007357189531245917027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 634582676476252708327889369 475937007357189531245917027)
        ·
          refine ⟨713905511035784296868875541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 475937007357189531245917027 713905511035784296868875541)
          ·
            refine ⟨33464320829802388915728541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 713905511035784296868875541 33464320829802388915728541)
            ·
              refine ⟨12549120311175895843398203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33464320829802388915728541 12549120311175895843398203)
              ·
                refine ⟨18823680466763843765097305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12549120311175895843398203 18823680466763843765097305)
                ·
                  refine ⟨14117760350072882823822979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18823680466763843765097305 14117760350072882823822979)
                  ·
                    refine ⟨21176640525109324235734469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14117760350072882823822979 21176640525109324235734469)
                    ·
                      refine ⟨3970620098457998294200213, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21176640525109324235734469 3970620098457998294200213)
                      ·
                        rfl

theorem cell23_7732755_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 3, 1, 2, 1, 4].length) (baseStart_7732755 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7732755 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7732755 prefixEnd_7732755 := by exact prefixLift 7732755
  have htrace : WordTrace (prefixWord ++ tailWord_7732755) baseStart_7732755 baseEnd_7732755 := by
    simpa [prefixWord, tailWord_7732755, baseEnd_7732755] using wordTrace_append hprefix tailTrace_7732755
  have hstable : (prefixWord ++ tailWord_7732755).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7732755).length < 2 ^ (prefixWord ++ tailWord_7732755).sum := by decide
  have hdescent : baseEnd_7732755 < baseStart_7732755 := by decide
  rcases family_descends (prefixWord ++ tailWord_7732755) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7732765 : List Nat := [1, 4, 2, 2, 1, 1, 1, 2, 5, 4]
def baseStart_7732765 : Nat := 118140960795 + 7732765 * 2 ^ 59
def prefixEnd_7732765 : Nat := 4983230072969 + 3 ^ 40 * 7732765 * 2
def baseEnd_7732765 : Nat := 1323541744421514418358389

theorem tailTrace_7732765 : CollatzResearch.WordTrace tailWord_7732765 prefixEnd_7732765 1323541744421514418358389 := by
  unfold tailWord_7732765
  simp only [CollatzResearch.WordTrace]
  refine ⟨282037109830520530964703749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188024739887013687309802499 282037109830520530964703749)
  ·
    refine ⟨52881958093222599555881953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 282037109830520530964703749 52881958093222599555881953)
    ·
      refine ⟨39661468569916949666911465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52881958093222599555881953 39661468569916949666911465)
      ·
        refine ⟨29746101427437712250183599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39661468569916949666911465 29746101427437712250183599)
        ·
          refine ⟨44619152141156568375275399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29746101427437712250183599 44619152141156568375275399)
          ·
            refine ⟨66928728211734852562913099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44619152141156568375275399 66928728211734852562913099)
            ·
              refine ⟨100393092317602278844369649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66928728211734852562913099 100393092317602278844369649)
              ·
                refine ⟨75294819238201709133277237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 100393092317602278844369649 75294819238201709133277237)
                ·
                  refine ⟨7058889303581410231244741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 75294819238201709133277237 7058889303581410231244741)
                  ·
                    refine ⟨1323541744421514418358389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7058889303581410231244741 1323541744421514418358389)
                    ·
                      rfl

theorem cell23_7732765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 1, 2, 5, 4].length) (baseStart_7732765 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7732765 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7732765 prefixEnd_7732765 := by exact prefixLift 7732765
  have htrace : WordTrace (prefixWord ++ tailWord_7732765) baseStart_7732765 baseEnd_7732765 := by
    simpa [prefixWord, tailWord_7732765, baseEnd_7732765] using wordTrace_append hprefix tailTrace_7732765
  have hstable : (prefixWord ++ tailWord_7732765).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7732765).length < 2 ^ (prefixWord ++ tailWord_7732765).sum := by decide
  have hdescent : baseEnd_7732765 < baseStart_7732765 := by decide
  rcases family_descends (prefixWord ++ tailWord_7732765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7732782 : List Nat := [4, 1, 3, 1, 2, 1, 1, 3, 3, 4]
def baseStart_7732782 : Nat := 118140960795 + 7732782 * 2 ^ 59
def prefixEnd_7732782 : Nat := 4983230072969 + 3 ^ 40 * 7732782 * 2
def baseEnd_7732782 : Nat := 1323544654145223229520863

theorem tailTrace_7732782 : CollatzResearch.WordTrace tailWord_7732782 prefixEnd_7732782 1323544654145223229520863 := by
  unfold tailWord_7732782
  simp only [CollatzResearch.WordTrace]
  refine ⟨35254716233932367858509075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 188025153247639295245381733 35254716233932367858509075)
  ·
    refine ⟨52882074350898551787763613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35254716233932367858509075 52882074350898551787763613)
    ·
      refine ⟨19830777881586956920411355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 52882074350898551787763613 19830777881586956920411355)
      ·
        refine ⟨29746166822380435380617033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19830777881586956920411355 29746166822380435380617033)
        ·
          refine ⟨22309625116785326535462775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29746166822380435380617033 22309625116785326535462775)
          ·
            refine ⟨33464437675177989803194163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22309625116785326535462775 33464437675177989803194163)
            ·
              refine ⟨50196656512766984704791245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33464437675177989803194163 50196656512766984704791245)
              ·
                refine ⟨18823746192287619264296717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 50196656512766984704791245 18823746192287619264296717)
                ·
                  refine ⟨7058904822107857224111269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18823746192287619264296717 7058904822107857224111269)
                  ·
                    refine ⟨1323544654145223229520863, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7058904822107857224111269 1323544654145223229520863)
                    ·
                      rfl

theorem cell23_7732782_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 1, 3, 3, 4].length) (baseStart_7732782 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7732782 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7732782 prefixEnd_7732782 := by exact prefixLift 7732782
  have htrace : WordTrace (prefixWord ++ tailWord_7732782) baseStart_7732782 baseEnd_7732782 := by
    simpa [prefixWord, tailWord_7732782, baseEnd_7732782] using wordTrace_append hprefix tailTrace_7732782
  have hstable : (prefixWord ++ tailWord_7732782).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7732782).length < 2 ^ (prefixWord ++ tailWord_7732782).sum := by decide
  have hdescent : baseEnd_7732782 < baseStart_7732782 := by decide
  rcases family_descends (prefixWord ++ tailWord_7732782) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7732839 : List Nat := [1, 1, 5, 1, 1, 1, 2, 6, 1, 1, 3]
def baseStart_7732839 : Nat := 118140960795 + 7732839 * 2 ^ 59
def prefixEnd_7732839 : Nat := 4983230072969 + 3 ^ 40 * 7732839 * 2
def baseEnd_7732839 : Nat := 3970663230832975965549827

theorem tailTrace_7732839 : CollatzResearch.WordTrace tailWord_7732839 prefixEnd_7732839 3970663230832975965549827 := by
  unfold tailWord_7732839
  simp only [CollatzResearch.WordTrace]
  refine ⟨282039808832252441602897571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188026539221501627735265047 282039808832252441602897571)
  ·
    refine ⟨423059713248378662404346357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 282039808832252441602897571 423059713248378662404346357)
    ·
      refine ⟨39661848117035499600407471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 423059713248378662404346357 39661848117035499600407471)
      ·
        refine ⟨59492772175553249400611207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39661848117035499600407471 59492772175553249400611207)
        ·
          refine ⟨89239158263329874100916811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59492772175553249400611207 89239158263329874100916811)
          ·
            refine ⟨133858737394994811151375217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89239158263329874100916811 133858737394994811151375217)
            ·
              refine ⟨100394053046246108363531413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 133858737394994811151375217 100394053046246108363531413)
              ·
                refine ⟨4705971236542786329540535, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 100394053046246108363531413 4705971236542786329540535)
                ·
                  refine ⟨7058956854814179494310803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4705971236542786329540535 7058956854814179494310803)
                  ·
                    refine ⟨10588435282221269241466205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7058956854814179494310803 10588435282221269241466205)
                    ·
                      refine ⟨3970663230832975965549827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10588435282221269241466205 3970663230832975965549827)
                      ·
                        rfl

theorem cell23_7732839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 2, 6, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 2, 6, 1, 1, 3].length) (baseStart_7732839 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7732839 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7732839 prefixEnd_7732839 := by exact prefixLift 7732839
  have htrace : WordTrace (prefixWord ++ tailWord_7732839) baseStart_7732839 baseEnd_7732839 := by
    simpa [prefixWord, tailWord_7732839, baseEnd_7732839] using wordTrace_append hprefix tailTrace_7732839
  have hstable : (prefixWord ++ tailWord_7732839).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7732839).length < 2 ^ (prefixWord ++ tailWord_7732839).sum := by decide
  have hdescent : baseEnd_7732839 < baseStart_7732839 := by decide
  rcases family_descends (prefixWord ++ tailWord_7732839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7732846 : List Nat := [4, 1, 2, 2, 4, 1, 2, 1, 6]
def baseStart_7732846 : Nat := 118140960795 + 7732846 * 2 ^ 59
def prefixEnd_7732846 : Nat := 4983230072969 + 3 ^ 40 * 7732846 * 2
def baseEnd_7732846 : Nat := 441185202799728604240255

theorem tailTrace_7732846 : CollatzResearch.WordTrace tailWord_7732846 prefixEnd_7732846 441185202799728604240255 := by
  unfold tailWord_7732846
  simp only [CollatzResearch.WordTrace]
  refine ⟨35255008017903385224800299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 188026709428818054532268261 35255008017903385224800299)
  ·
    refine ⟨52882512026855077837200449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35255008017903385224800299 52882512026855077837200449)
    ·
      refine ⟨39661884020141308377900337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52882512026855077837200449 39661884020141308377900337)
      ·
        refine ⟨29746413015105981283425253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39661884020141308377900337 29746413015105981283425253)
        ·
          refine ⟨5577452440332371490642235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 29746413015105981283425253 5577452440332371490642235)
          ·
            refine ⟨8366178660498557235963353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5577452440332371490642235 8366178660498557235963353)
            ·
              refine ⟨6274633995373917926972515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8366178660498557235963353 6274633995373917926972515)
              ·
                refine ⟨9411950993060876890458773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6274633995373917926972515 9411950993060876890458773)
                ·
                  refine ⟨441185202799728604240255, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9411950993060876890458773 441185202799728604240255)
                  ·
                    rfl

theorem cell23_7732846_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 4, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 4, 1, 2, 1, 6].length) (baseStart_7732846 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7732846 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7732846 prefixEnd_7732846 := by exact prefixLift 7732846
  have htrace : WordTrace (prefixWord ++ tailWord_7732846) baseStart_7732846 baseEnd_7732846 := by
    simpa [prefixWord, tailWord_7732846, baseEnd_7732846] using wordTrace_append hprefix tailTrace_7732846
  have hstable : (prefixWord ++ tailWord_7732846).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7732846).length < 2 ^ (prefixWord ++ tailWord_7732846).sum := by decide
  have hdescent : baseEnd_7732846 < baseStart_7732846 := by decide
  rcases family_descends (prefixWord ++ tailWord_7732846) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7732875 : List Nat := [1, 1, 1, 1, 4, 1, 5, 2, 1, 2, 4]
def baseStart_7732875 : Nat := 118140960795 + 7732875 * 2 ^ 59
def prefixEnd_7732875 : Nat := 4983230072969 + 3 ^ 40 * 7732875 * 2
def baseEnd_7732875 : Nat := 3970681716136537824699661

theorem tailTrace_7732875 : CollatzResearch.WordTrace tailWord_7732875 prefixEnd_7732875 3970681716136537824699661 := by
  unfold tailWord_7732875
  simp only [CollatzResearch.WordTrace]
  refine ⟨282041121860122019751208079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188027414573414679834138719 282041121860122019751208079)
  ·
    refine ⟨423061682790183029626812119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 282041121860122019751208079 423061682790183029626812119)
    ·
      refine ⟨634592524185274544440218179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 423061682790183029626812119 634592524185274544440218179)
      ·
        refine ⟨951888786277911816660327269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 634592524185274544440218179 951888786277911816660327269)
        ·
          refine ⟨178479147427108465623811363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 951888786277911816660327269 178479147427108465623811363)
          ·
            refine ⟨267718721140662698435717045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 178479147427108465623811363 267718721140662698435717045)
            ·
              refine ⟨25098630106937127978348473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 267718721140662698435717045 25098630106937127978348473)
              ·
                refine ⟨18823972580202845983761355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25098630106937127978348473 18823972580202845983761355)
                ·
                  refine ⟨28235958870304268975642033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18823972580202845983761355 28235958870304268975642033)
                  ·
                    refine ⟨21176969152728201731731525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28235958870304268975642033 21176969152728201731731525)
                    ·
                      refine ⟨3970681716136537824699661, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21176969152728201731731525 3970681716136537824699661)
                      ·
                        rfl

theorem cell23_7732875_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 5, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 5, 2, 1, 2, 4].length) (baseStart_7732875 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7732875 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7732875 prefixEnd_7732875 := by exact prefixLift 7732875
  have htrace : WordTrace (prefixWord ++ tailWord_7732875) baseStart_7732875 baseEnd_7732875 := by
    simpa [prefixWord, tailWord_7732875, baseEnd_7732875] using wordTrace_append hprefix tailTrace_7732875
  have hstable : (prefixWord ++ tailWord_7732875).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7732875).length < 2 ^ (prefixWord ++ tailWord_7732875).sum := by decide
  have hdescent : baseEnd_7732875 < baseStart_7732875 := by decide
  rcases family_descends (prefixWord ++ tailWord_7732875) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7732925 : List Nat := [1, 4, 1, 2, 1, 2, 2, 1, 2, 2, 5]
def baseStart_7732925 : Nat := 118140960795 + 7732925 * 2 ^ 59
def prefixEnd_7732925 : Nat := 4983230072969 + 3 ^ 40 * 7732925 * 2
def baseEnd_7732925 : Nat := 3970707390169262629074431

theorem tailTrace_7732925 : CollatzResearch.WordTrace tailWord_7732925 prefixEnd_7732925 3970707390169262629074431 := by
  unfold tailWord_7732925
  simp only [CollatzResearch.WordTrace]
  refine ⟨282042945509940878290528229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188028630339960585527018819 282042945509940878290528229)
  ·
    refine ⟨52883052283113914679474043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 282042945509940878290528229 52883052283113914679474043)
    ·
      refine ⟨79324578424670872019211065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52883052283113914679474043 79324578424670872019211065)
      ·
        refine ⟨59493433818503154014408299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79324578424670872019211065 59493433818503154014408299)
        ·
          refine ⟨89240150727754731021612449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59493433818503154014408299 89240150727754731021612449)
          ·
            refine ⟨66930113045816048266209337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 89240150727754731021612449 66930113045816048266209337)
            ·
              refine ⟨50197584784362036199657003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66930113045816048266209337 50197584784362036199657003)
              ·
                refine ⟨75296377176543054299485505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50197584784362036199657003 75296377176543054299485505)
                ·
                  refine ⟨56472282882407290724614129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 75296377176543054299485505 56472282882407290724614129)
                  ·
                    refine ⟨42354212161805468043460597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 56472282882407290724614129 42354212161805468043460597)
                    ·
                      refine ⟨3970707390169262629074431, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42354212161805468043460597 3970707390169262629074431)
                      ·
                        rfl

theorem cell23_7732925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 2, 1, 2, 2, 5].length) (baseStart_7732925 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7732925 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7732925 prefixEnd_7732925 := by exact prefixLift 7732925
  have htrace : WordTrace (prefixWord ++ tailWord_7732925) baseStart_7732925 baseEnd_7732925 := by
    simpa [prefixWord, tailWord_7732925, baseEnd_7732925] using wordTrace_append hprefix tailTrace_7732925
  have hstable : (prefixWord ++ tailWord_7732925).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7732925).length < 2 ^ (prefixWord ++ tailWord_7732925).sum := by decide
  have hdescent : baseEnd_7732925 < baseStart_7732925 := by decide
  rcases family_descends (prefixWord ++ tailWord_7732925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7732945 : List Nat := [1, 2, 2, 1, 2, 4, 1, 2, 2, 6]
def baseStart_7732945 : Nat := 118140960795 + 7732945 * 2 ^ 59
def prefixEnd_7732945 : Nat := 4983230072969 + 3 ^ 40 * 7732945 * 2
def baseEnd_7732945 : Nat := 1323572553260784183608113

theorem tailTrace_7732945 : CollatzResearch.WordTrace tailWord_7732945 prefixEnd_7732945 1323572553260784183608113 := by
  unfold tailWord_7732945
  simp only [CollatzResearch.WordTrace]
  refine ⟨282043674969868421706256289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188029116646578947804170859 282043674969868421706256289)
  ·
    refine ⟨211532756227401316279692217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 282043674969868421706256289 211532756227401316279692217)
    ·
      refine ⟨158649567170550987209769163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 211532756227401316279692217 158649567170550987209769163)
      ·
        refine ⟨237974350755826480814653745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 158649567170550987209769163 237974350755826480814653745)
        ·
          refine ⟨178480763066869860610990309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 237974350755826480814653745 178480763066869860610990309)
          ·
            refine ⟨33465143075038098864560683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 178480763066869860610990309 33465143075038098864560683)
            ·
              refine ⟨50197714612557148296841025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33465143075038098864560683 50197714612557148296841025)
              ·
                refine ⟨37648285959417861222630769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50197714612557148296841025 37648285959417861222630769)
                ·
                  refine ⟨28236214469563395916973077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37648285959417861222630769 28236214469563395916973077)
                  ·
                    refine ⟨1323572553260784183608113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28236214469563395916973077 1323572553260784183608113)
                    ·
                      rfl

theorem cell23_7732945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 1, 2, 2, 6].length) (baseStart_7732945 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7732945 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7732945 prefixEnd_7732945 := by exact prefixLift 7732945
  have htrace : WordTrace (prefixWord ++ tailWord_7732945) baseStart_7732945 baseEnd_7732945 := by
    simpa [prefixWord, tailWord_7732945, baseEnd_7732945] using wordTrace_append hprefix tailTrace_7732945
  have hstable : (prefixWord ++ tailWord_7732945).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7732945).length < 2 ^ (prefixWord ++ tailWord_7732945).sum := by decide
  have hdescent : baseEnd_7732945 < baseStart_7732945 := by decide
  rcases family_descends (prefixWord ++ tailWord_7732945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7732946 : List Nat := [3, 2, 2, 2, 2, 1, 3, 2, 2, 1, 3]
def baseStart_7732946 : Nat := 118140960795 + 7732946 * 2 ^ 59
def prefixEnd_7732946 : Nat := 4983230072969 + 3 ^ 40 * 7732946 * 2
def baseEnd_7732946 : Nat := 3970718173263007046911835

theorem tailTrace_7732946 : CollatzResearch.WordTrace tailWord_7732946 prefixEnd_7732946 3970718173263007046911835 := by
  unfold tailWord_7732946
  simp only [CollatzResearch.WordTrace]
  refine ⟨70510927860716199719260673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 188029140961909865918028461 70510927860716199719260673)
  ·
    refine ⟨52883195895537149789445505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70510927860716199719260673 52883195895537149789445505)
    ·
      refine ⟨39662396921652862342084129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52883195895537149789445505 39662396921652862342084129)
      ·
        refine ⟨29746797691239646756563097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39662396921652862342084129 29746797691239646756563097)
        ·
          refine ⟨22310098268429735067422323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29746797691239646756563097 22310098268429735067422323)
          ·
            refine ⟨33465147402644602601133485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22310098268429735067422323 33465147402644602601133485)
            ·
              refine ⟨12549430275991725975425057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33465147402644602601133485 12549430275991725975425057)
              ·
                refine ⟨9412072706993794481568793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12549430275991725975425057 9412072706993794481568793)
                ·
                  refine ⟨7059054530245345861176595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9412072706993794481568793 7059054530245345861176595)
                  ·
                    refine ⟨10588581795368018791764893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7059054530245345861176595 10588581795368018791764893)
                    ·
                      refine ⟨3970718173263007046911835, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10588581795368018791764893 3970718173263007046911835)
                      ·
                        rfl

theorem cell23_7732946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 3, 2, 2, 1, 3].length) (baseStart_7732946 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7732946 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7732946 prefixEnd_7732946 := by exact prefixLift 7732946
  have htrace : WordTrace (prefixWord ++ tailWord_7732946) baseStart_7732946 baseEnd_7732946 := by
    simpa [prefixWord, tailWord_7732946, baseEnd_7732946] using wordTrace_append hprefix tailTrace_7732946
  have hstable : (prefixWord ++ tailWord_7732946).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7732946).length < 2 ^ (prefixWord ++ tailWord_7732946).sum := by decide
  have hdescent : baseEnd_7732946 < baseStart_7732946 := by decide
  rcases family_descends (prefixWord ++ tailWord_7732946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7732963 : List Nat := [1, 1, 1, 7, 2, 1, 3, 1, 2, 1, 3]
def baseStart_7732963 : Nat := 118140960795 + 7732963 * 2 ^ 59
def prefixEnd_7732963 : Nat := 4983230072969 + 3 ^ 40 * 7732963 * 2
def baseEnd_7732963 : Nat := 3970726902434133480399257

theorem tailTrace_7732963 : CollatzResearch.WordTrace tailWord_7732963 prefixEnd_7732963 3970726902434133480399257 := by
  unfold tailWord_7732963
  simp only [CollatzResearch.WordTrace]
  refine ⟨282044331483803210780411543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188029554322535473853607695 282044331483803210780411543)
  ·
    refine ⟨423066497225704816170617315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 282044331483803210780411543 423066497225704816170617315)
    ·
      refine ⟨634599745838557224255925973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 423066497225704816170617315 634599745838557224255925973)
      ·
        refine ⟨14873431543091184943498265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 634599745838557224255925973 14873431543091184943498265)
        ·
          refine ⟨11155073657318388707623699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14873431543091184943498265 11155073657318388707623699)
          ·
            refine ⟨16732610485977583061435549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11155073657318388707623699 16732610485977583061435549)
            ·
              refine ⟨6274728932241593648038331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16732610485977583061435549 6274728932241593648038331)
              ·
                refine ⟨9412093398362390472057497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6274728932241593648038331 9412093398362390472057497)
                ·
                  refine ⟨7059070048771792854043123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9412093398362390472057497 7059070048771792854043123)
                  ·
                    refine ⟨10588605073157689281064685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7059070048771792854043123 10588605073157689281064685)
                    ·
                      refine ⟨3970726902434133480399257, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10588605073157689281064685 3970726902434133480399257)
                      ·
                        rfl

theorem cell23_7732963_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 2, 1, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 2, 1, 3, 1, 2, 1, 3].length) (baseStart_7732963 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7732963 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7732963 prefixEnd_7732963 := by exact prefixLift 7732963
  have htrace : WordTrace (prefixWord ++ tailWord_7732963) baseStart_7732963 baseEnd_7732963 := by
    simpa [prefixWord, tailWord_7732963, baseEnd_7732963] using wordTrace_append hprefix tailTrace_7732963
  have hstable : (prefixWord ++ tailWord_7732963).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7732963).length < 2 ^ (prefixWord ++ tailWord_7732963).sum := by decide
  have hdescent : baseEnd_7732963 < baseStart_7732963 := by decide
  rcases family_descends (prefixWord ++ tailWord_7732963) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7732975 : List Nat := [1, 1, 2, 1, 5, 1, 1, 4, 7]
def baseStart_7732975 : Nat := 118140960795 + 7732975 * 2 ^ 59
def prefixEnd_7732975 : Nat := 4983230072969 + 3 ^ 40 * 7732975 * 2
def baseEnd_7732975 : Nat := 441192562689109714827689

theorem tailTrace_7732975 : CollatzResearch.WordTrace tailWord_7732975 prefixEnd_7732975 441192562689109714827689 := by
  unfold tailWord_7732975
  simp only [CollatzResearch.WordTrace]
  refine ⟨282044769159759736829848379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188029846106506491219898919 282044769159759736829848379)
  ·
    refine ⟨423067153739639605244772569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 282044769159759736829848379 423067153739639605244772569)
    ·
      refine ⟨317300365304729703933579427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 423067153739639605244772569 317300365304729703933579427)
      ·
        refine ⟨475950547957094555900369141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 317300365304729703933579427 475950547957094555900369141)
        ·
          refine ⟨44620363870977614615659607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 475950547957094555900369141 44620363870977614615659607)
          ·
            refine ⟨66930545806466421923489411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44620363870977614615659607 66930545806466421923489411)
            ·
              refine ⟨100395818709699632885234117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66930545806466421923489411 100395818709699632885234117)
              ·
                refine ⟨18824216008068681165981397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 100395818709699632885234117 18824216008068681165981397)
                ·
                  refine ⟨441192562689109714827689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18824216008068681165981397 441192562689109714827689)
                  ·
                    rfl

theorem cell23_7732975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 1, 4, 7].length) (baseStart_7732975 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7732975 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7732975 prefixEnd_7732975 := by exact prefixLift 7732975
  have htrace : WordTrace (prefixWord ++ tailWord_7732975) baseStart_7732975 baseEnd_7732975 := by
    simpa [prefixWord, tailWord_7732975, baseEnd_7732975] using wordTrace_append hprefix tailTrace_7732975
  have hstable : (prefixWord ++ tailWord_7732975).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7732975).length < 2 ^ (prefixWord ++ tailWord_7732975).sum := by decide
  have hdescent : baseEnd_7732975 < baseStart_7732975 := by decide
  rcases family_descends (prefixWord ++ tailWord_7732975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7732998 : List Nat := [6, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2]
def baseStart_7732998 : Nat := 118140960795 + 7732998 * 2 ^ 59
def prefixEnd_7732998 : Nat := 4983230072969 + 3 ^ 40 * 7732998 * 2
def baseEnd_7732998 : Nat := 3970744874257040843461597

theorem tailTrace_7732998 : CollatzResearch.WordTrace tailWord_7732998 prefixEnd_7732998 3970744874257040843461597 := by
  unfold tailWord_7732998
  simp only [CollatzResearch.WordTrace]
  refine ⟨8813925251208637867435489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 188030405359117607838623765 8813925251208637867435489)
  ·
    refine ⟨6610443938406478400576617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8813925251208637867435489 6610443938406478400576617)
    ·
      refine ⟨4957832953804858800432463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6610443938406478400576617 4957832953804858800432463)
      ·
        refine ⟨7436749430707288200648695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4957832953804858800432463 7436749430707288200648695)
        ·
          refine ⟨11155124146060932300973043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7436749430707288200648695 11155124146060932300973043)
          ·
            refine ⟨16732686219091398451459565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11155124146060932300973043 16732686219091398451459565)
            ·
              refine ⟨6274757332159274419297337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16732686219091398451459565 6274757332159274419297337)
              ·
                refine ⟨4706067999119455814473003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6274757332159274419297337 4706067999119455814473003)
                ·
                  refine ⟨7059101998679183721709505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4706067999119455814473003 7059101998679183721709505)
                  ·
                    refine ⟨5294326499009387791282129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7059101998679183721709505 5294326499009387791282129)
                    ·
                      refine ⟨3970744874257040843461597, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5294326499009387791282129 3970744874257040843461597)
                      ·
                        rfl

theorem cell23_7732998_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2].length) (baseStart_7732998 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7732998 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7732998 prefixEnd_7732998 := by exact prefixLift 7732998
  have htrace : WordTrace (prefixWord ++ tailWord_7732998) baseStart_7732998 baseEnd_7732998 := by
    simpa [prefixWord, tailWord_7732998, baseEnd_7732998] using wordTrace_append hprefix tailTrace_7732998
  have hstable : (prefixWord ++ tailWord_7732998).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7732998).length < 2 ^ (prefixWord ++ tailWord_7732998).sum := by decide
  have hdescent : baseEnd_7732998 < baseStart_7732998 := by decide
  rcases family_descends (prefixWord ++ tailWord_7732998) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7733076 : List Nat := [2, 4, 1, 1, 3, 2, 1, 1, 2, 4, 2]
def baseStart_7733076 : Nat := 118140960795 + 7733076 * 2 ^ 59
def prefixEnd_7733076 : Nat := 4983230072969 + 3 ^ 40 * 7733076 * 2
def baseEnd_7733076 : Nat := 3970784925748091538286237

theorem tailTrace_7733076 : CollatzResearch.WordTrace tailWord_7733076 prefixEnd_7733076 3970784925748091538286237 := by
  unfold tailWord_7733076
  simp only [CollatzResearch.WordTrace]
  refine ⟨141024226466196915539637541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 188032301954929220719516721 141024226466196915539637541)
  ·
    refine ⟨26442042462411921663682039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 141024226466196915539637541 26442042462411921663682039)
    ·
      refine ⟨39663063693617882495523059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26442042462411921663682039 39663063693617882495523059)
      ·
        refine ⟨59494595540426823743284589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39663063693617882495523059 59494595540426823743284589)
        ·
          refine ⟨22310473327660058903731721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 59494595540426823743284589 22310473327660058903731721)
          ·
            refine ⟨16732854995745044177798791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22310473327660058903731721 16732854995745044177798791)
            ·
              refine ⟨25099282493617566266698187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16732854995745044177798791 25099282493617566266698187)
              ·
                refine ⟨37648923740426349400047281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25099282493617566266698187 37648923740426349400047281)
                ·
                  refine ⟨28236692805319762050035461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37648923740426349400047281 28236692805319762050035461)
                  ·
                    refine ⟨5294379900997455384381649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28236692805319762050035461 5294379900997455384381649)
                    ·
                      refine ⟨3970784925748091538286237, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5294379900997455384381649 3970784925748091538286237)
                      ·
                        rfl

theorem cell23_7733076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 2, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 2, 1, 1, 2, 4, 2].length) (baseStart_7733076 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7733076 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7733076 prefixEnd_7733076 := by exact prefixLift 7733076
  have htrace : WordTrace (prefixWord ++ tailWord_7733076) baseStart_7733076 baseEnd_7733076 := by
    simpa [prefixWord, tailWord_7733076, baseEnd_7733076] using wordTrace_append hprefix tailTrace_7733076
  have hstable : (prefixWord ++ tailWord_7733076).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7733076).length < 2 ^ (prefixWord ++ tailWord_7733076).sum := by decide
  have hdescent : baseEnd_7733076 < baseStart_7733076 := by decide
  rcases family_descends (prefixWord ++ tailWord_7733076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7733082 : List Nat := [3, 1, 1, 2, 1, 3, 1, 5, 6]
def baseStart_7733082 : Nat := 118140960795 + 7733082 * 2 ^ 59
def prefixEnd_7733082 : Nat := 4983230072969 + 3 ^ 40 * 7733082 * 2
def baseEnd_7733082 : Nat := 441198667403557612756801

theorem tailTrace_7733082 : CollatzResearch.WordTrace tailWord_7733082 prefixEnd_7733082 441198667403557612756801 := by
  unfold tailWord_7733082
  simp only [CollatzResearch.WordTrace]
  refine ⟨70512167942593023525998375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 188032447846914729402662333 70512167942593023525998375)
  ·
    refine ⟨105768251913889535288997563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70512167942593023525998375 105768251913889535288997563)
    ·
      refine ⟨158652377870834302933496345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105768251913889535288997563 158652377870834302933496345)
      ·
        refine ⟨118989283403125727200122259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 158652377870834302933496345 118989283403125727200122259)
        ·
          refine ⟨178483925104688590800183389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 118989283403125727200122259 178483925104688590800183389)
          ·
            refine ⟨66931471914258221550068771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 178483925104688590800183389 66931471914258221550068771)
            ·
              refine ⟨100397207871387332325103157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66931471914258221550068771 100397207871387332325103157)
              ·
                refine ⟨9412238237942562405478421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 100397207871387332325103157 9412238237942562405478421)
                ·
                  refine ⟨441198667403557612756801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9412238237942562405478421 441198667403557612756801)
                  ·
                    rfl

theorem cell23_7733082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 1, 5, 6].length) (baseStart_7733082 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7733082 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7733082 prefixEnd_7733082 := by exact prefixLift 7733082
  have htrace : WordTrace (prefixWord ++ tailWord_7733082) baseStart_7733082 baseEnd_7733082 := by
    simpa [prefixWord, tailWord_7733082, baseEnd_7733082] using wordTrace_append hprefix tailTrace_7733082
  have hstable : (prefixWord ++ tailWord_7733082).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7733082).length < 2 ^ (prefixWord ++ tailWord_7733082).sum := by decide
  have hdescent : baseEnd_7733082 < baseStart_7733082 := by decide
  rcases family_descends (prefixWord ++ tailWord_7733082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7733119 : List Nat := [1, 1, 2, 2, 1, 1, 3, 3, 4, 3, 2]
def baseStart_7733119 : Nat := 118140960795 + 7733119 * 2 ^ 59
def prefixEnd_7733119 : Nat := 4983230072969 + 3 ^ 40 * 7733119 * 2
def baseEnd_7733119 : Nat := 3970807005416234870048539

theorem tailTrace_7733119 : CollatzResearch.WordTrace tailWord_7733119 prefixEnd_7733119 3970807005416234870048539 := by
  unfold tailWord_7733119
  simp only [CollatzResearch.WordTrace]
  refine ⟨282050021271238049423090411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188033347514158699615393607 282050021271238049423090411)
  ·
    refine ⟨423075031906857074134635617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 282050021271238049423090411 423075031906857074134635617)
    ·
      refine ⟨317306273930142805600976713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 423075031906857074134635617 317306273930142805600976713)
      ·
        refine ⟨237979705447607104200732535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 317306273930142805600976713 237979705447607104200732535)
        ·
          refine ⟨356969558171410656301098803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 237979705447607104200732535 356969558171410656301098803)
          ·
            refine ⟨535454337257115984451648205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 356969558171410656301098803 535454337257115984451648205)
            ·
              refine ⟨200795376471418494169368077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 535454337257115984451648205 200795376471418494169368077)
              ·
                refine ⟨75298266176781935313513029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 200795376471418494169368077 75298266176781935313513029)
                ·
                  refine ⟨14118424908146612871283693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 75298266176781935313513029 14118424908146612871283693)
                  ·
                    refine ⟨5294409340554979826731385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14118424908146612871283693 5294409340554979826731385)
                    ·
                      refine ⟨3970807005416234870048539, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5294409340554979826731385 3970807005416234870048539)
                      ·
                        rfl

theorem cell23_7733119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 3, 3, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 3, 3, 4, 3, 2].length) (baseStart_7733119 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7733119 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7733119 prefixEnd_7733119 := by exact prefixLift 7733119
  have htrace : WordTrace (prefixWord ++ tailWord_7733119) baseStart_7733119 baseEnd_7733119 := by
    simpa [prefixWord, tailWord_7733119, baseEnd_7733119] using wordTrace_append hprefix tailTrace_7733119
  have hstable : (prefixWord ++ tailWord_7733119).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7733119).length < 2 ^ (prefixWord ++ tailWord_7733119).sum := by decide
  have hdescent : baseEnd_7733119 < baseStart_7733119 := by decide
  rcases family_descends (prefixWord ++ tailWord_7733119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7733146 : List Nat := [3, 1, 1, 4, 2, 2, 2, 2, 1, 5]
def baseStart_7733146 : Nat := 118140960795 + 7733146 * 2 ^ 59
def prefixEnd_7733146 : Nat := 4983230072969 + 3 ^ 40 * 7733146 * 2
def baseEnd_7733146 : Nat := 1323606956464635421470305

theorem tailTrace_7733146 : CollatzResearch.WordTrace tailWord_7733146 prefixEnd_7733146 1323606956464635421470305 := by
  unfold tailWord_7733146
  simp only [CollatzResearch.WordTrace]
  refine ⟨70512751510535058258580823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 188034004028093488689548861 70512751510535058258580823)
  ·
    refine ⟨105769127265802587387871235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70512751510535058258580823 105769127265802587387871235)
    ·
      refine ⟨158653690898703881081806853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105769127265802587387871235 158653690898703881081806853)
      ·
        refine ⟨29747567043506977702838785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 158653690898703881081806853 29747567043506977702838785)
        ·
          refine ⟨22310675282630233277129089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29747567043506977702838785 22310675282630233277129089)
          ·
            refine ⟨16733006461972674957846817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22310675282630233277129089 16733006461972674957846817)
            ·
              refine ⟨12549754846479506218385113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16733006461972674957846817 12549754846479506218385113)
              ·
                refine ⟨9412316134859629663788835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12549754846479506218385113 9412316134859629663788835)
                ·
                  refine ⟨14118474202289444495683253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9412316134859629663788835 14118474202289444495683253)
                  ·
                    refine ⟨1323606956464635421470305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14118474202289444495683253 1323606956464635421470305)
                    ·
                      rfl

theorem cell23_7733146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 2, 2, 2, 1, 5].length) (baseStart_7733146 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7733146 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7733146 prefixEnd_7733146 := by exact prefixLift 7733146
  have htrace : WordTrace (prefixWord ++ tailWord_7733146) baseStart_7733146 baseEnd_7733146 := by
    simpa [prefixWord, tailWord_7733146, baseEnd_7733146] using wordTrace_append hprefix tailTrace_7733146
  have hstable : (prefixWord ++ tailWord_7733146).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7733146).length < 2 ^ (prefixWord ++ tailWord_7733146).sum := by decide
  have hdescent : baseEnd_7733146 < baseStart_7733146 := by decide
  rcases family_descends (prefixWord ++ tailWord_7733146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7733152 : List Nat := [2, 1, 1, 4, 1, 1, 1, 1, 5, 1, 5]
def baseStart_7733152 : Nat := 118140960795 + 7733152 * 2 ^ 59
def prefixEnd_7733152 : Nat := 4983230072969 + 3 ^ 40 * 7733152 * 2
def baseEnd_7733152 : Nat := 3970823950277833240935887

theorem tailTrace_7733152 : CollatzResearch.WordTrace tailWord_7733152 prefixEnd_7733152 3970823950277833240935887 := by
  unfold tailWord_7733152
  simp only [CollatzResearch.WordTrace]
  refine ⟨141025612440059248029520855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 188034149920078997372694473 141025612440059248029520855)
  ·
    refine ⟨211538418660088872044281283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141025612440059248029520855 211538418660088872044281283)
    ·
      refine ⟨317307627990133308066421925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 211538418660088872044281283 317307627990133308066421925)
      ·
        refine ⟨59495180248149995262454111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 317307627990133308066421925 59495180248149995262454111)
        ·
          refine ⟨89242770372224992893681167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59495180248149995262454111 89242770372224992893681167)
          ·
            refine ⟨133864155558337489340521751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89242770372224992893681167 133864155558337489340521751)
            ·
              refine ⟨200796233337506234010782627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 133864155558337489340521751 200796233337506234010782627)
              ·
                refine ⟨301194350006259351016173941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 200796233337506234010782627 301194350006259351016173941)
                ·
                  refine ⟨28236970313086814157766307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 301194350006259351016173941 28236970313086814157766307)
                  ·
                    refine ⟨42355455469630221236649461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28236970313086814157766307 42355455469630221236649461)
                    ·
                      refine ⟨3970823950277833240935887, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42355455469630221236649461 3970823950277833240935887)
                      ·
                        rfl

theorem cell23_7733152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 1, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 1, 1, 5, 1, 5].length) (baseStart_7733152 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7733152 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7733152 prefixEnd_7733152 := by exact prefixLift 7733152
  have htrace : WordTrace (prefixWord ++ tailWord_7733152) baseStart_7733152 baseEnd_7733152 := by
    simpa [prefixWord, tailWord_7733152, baseEnd_7733152] using wordTrace_append hprefix tailTrace_7733152
  have hstable : (prefixWord ++ tailWord_7733152).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7733152).length < 2 ^ (prefixWord ++ tailWord_7733152).sum := by decide
  have hdescent : baseEnd_7733152 < baseStart_7733152 := by decide
  rcases family_descends (prefixWord ++ tailWord_7733152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7733169 : List Nat := [1, 2, 2, 4, 2, 1, 1, 3, 1, 1, 5]
def baseStart_7733169 : Nat := 118140960795 + 7733169 * 2 ^ 59
def prefixEnd_7733169 : Nat := 4983230072969 + 3 ^ 40 * 7733169 * 2
def baseEnd_7733169 : Nat := 3970832679448959674423309

theorem tailTrace_7733169 : CollatzResearch.WordTrace tailWord_7733169 prefixEnd_7733169 3970832679448959674423309 := by
  unfold tailWord_7733169
  simp only [CollatzResearch.WordTrace]
  refine ⟨282051844921056907962410561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188034563280704605308273707 282051844921056907962410561)
  ·
    refine ⟨211538883690792680971807921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 282051844921056907962410561 211538883690792680971807921)
    ·
      refine ⟨158654162768094510728855941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 211538883690792680971807921 158654162768094510728855941)
      ·
        refine ⟨29747655519017720761660489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 158654162768094510728855941 29747655519017720761660489)
        ·
          refine ⟨22310741639263290571245367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29747655519017720761660489 22310741639263290571245367)
          ·
            refine ⟨33466112458894935856868051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22310741639263290571245367 33466112458894935856868051)
            ·
              refine ⟨50199168688342403785302077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33466112458894935856868051 50199168688342403785302077)
              ·
                refine ⟨18824688258128401419488279, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 50199168688342403785302077 18824688258128401419488279)
                ·
                  refine ⟨28237032387192602129232419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18824688258128401419488279 28237032387192602129232419)
                  ·
                    refine ⟨42355548580788903193848629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28237032387192602129232419 42355548580788903193848629)
                    ·
                      refine ⟨3970832679448959674423309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42355548580788903193848629 3970832679448959674423309)
                      ·
                        rfl

theorem cell23_7733169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 1, 3, 1, 1, 5].length) (baseStart_7733169 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7733169 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7733169 prefixEnd_7733169 := by exact prefixLift 7733169
  have htrace : WordTrace (prefixWord ++ tailWord_7733169) baseStart_7733169 baseEnd_7733169 := by
    simpa [prefixWord, tailWord_7733169, baseEnd_7733169] using wordTrace_append hprefix tailTrace_7733169
  have hstable : (prefixWord ++ tailWord_7733169).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7733169).length < 2 ^ (prefixWord ++ tailWord_7733169).sum := by decide
  have hdescent : baseEnd_7733169 < baseStart_7733169 := by decide
  rcases family_descends (prefixWord ++ tailWord_7733169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7733199 : List Nat := [1, 1, 2, 1, 1, 5, 2, 3, 1, 3, 3]
def baseStart_7733199 : Nat := 118140960795 + 7733199 * 2 ^ 59
def prefixEnd_7733199 : Nat := 4983230072969 + 3 ^ 40 * 7733199 * 2
def baseEnd_7733199 : Nat := 3970848083868594557048171

theorem tailTrace_7733199 : CollatzResearch.WordTrace tailWord_7733199 prefixEnd_7733199 3970848083868594557048171 := by
  unfold tailWord_7733199
  simp only [CollatzResearch.WordTrace]
  refine ⟨282052939110948223086002651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188035292740632148724001767 282052939110948223086002651)
  ·
    refine ⟨423079408666422334629003977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 282052939110948223086002651 423079408666422334629003977)
    ·
      refine ⟨317309556499816750971752983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 423079408666422334629003977 317309556499816750971752983)
      ·
        refine ⟨475964334749725126457629475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 317309556499816750971752983 475964334749725126457629475)
        ·
          refine ⟨713946502124587689686444213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 475964334749725126457629475 713946502124587689686444213)
          ·
            refine ⟨66932484574180095908104145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 713946502124587689686444213 66932484574180095908104145)
            ·
              refine ⟨50199363430635071931078109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66932484574180095908104145 50199363430635071931078109)
              ·
                refine ⟨18824761286488151974154291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 50199363430635071931078109 18824761286488151974154291)
                ·
                  refine ⟨28237141929732227961231437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18824761286488151974154291 28237141929732227961231437)
                  ·
                    refine ⟨10588928223649585485461789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28237141929732227961231437 10588928223649585485461789)
                    ·
                      refine ⟨3970848083868594557048171, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10588928223649585485461789 3970848083868594557048171)
                      ·
                        rfl

theorem cell23_7733199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 2, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 2, 3, 1, 3, 3].length) (baseStart_7733199 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7733199 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7733199 prefixEnd_7733199 := by exact prefixLift 7733199
  have htrace : WordTrace (prefixWord ++ tailWord_7733199) baseStart_7733199 baseEnd_7733199 := by
    simpa [prefixWord, tailWord_7733199, baseEnd_7733199] using wordTrace_append hprefix tailTrace_7733199
  have hstable : (prefixWord ++ tailWord_7733199).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7733199).length < 2 ^ (prefixWord ++ tailWord_7733199).sum := by decide
  have hdescent : baseEnd_7733199 < baseStart_7733199 := by decide
  rcases family_descends (prefixWord ++ tailWord_7733199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7733249 : List Nat := [1, 2, 4, 1, 2, 1, 3, 1, 2, 6]
def baseStart_7733249 : Nat := 118140960795 + 7733249 * 2 ^ 59
def prefixEnd_7733249 : Nat := 4983230072969 + 3 ^ 40 * 7733249 * 2
def baseEnd_7733249 : Nat := 1323624585967106453807647

theorem tailTrace_7733249 : CollatzResearch.WordTrace tailWord_7733249 prefixEnd_7733249 1323624585967106453807647 := by
  unfold tailWord_7733249
  simp only [CollatzResearch.WordTrace]
  refine ⟨282054762760767081625322801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188036508507178054416881867 282054762760767081625322801)
  ·
    refine ⟨211541072070575311218992101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 282054762760767081625322801 211541072070575311218992101)
    ·
      refine ⟨39663951013232870853561019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 211541072070575311218992101 39663951013232870853561019)
      ·
        refine ⟨59495926519849306280341529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39663951013232870853561019 59495926519849306280341529)
        ·
          refine ⟨44621944889886979710256147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59495926519849306280341529 44621944889886979710256147)
          ·
            refine ⟨66932917334830469565384221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44621944889886979710256147 66932917334830469565384221)
            ·
              refine ⟨25099844000561426087019083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 66932917334830469565384221 25099844000561426087019083)
              ·
                refine ⟨37649766000842139130528625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25099844000561426087019083 37649766000842139130528625)
                ·
                  refine ⟨28237324500631604347896469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37649766000842139130528625 28237324500631604347896469)
                  ·
                    refine ⟨1323624585967106453807647, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28237324500631604347896469 1323624585967106453807647)
                    ·
                      rfl

theorem cell23_7733249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 3, 1, 2, 6].length) (baseStart_7733249 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7733249 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7733249 prefixEnd_7733249 := by exact prefixLift 7733249
  have htrace : WordTrace (prefixWord ++ tailWord_7733249) baseStart_7733249 baseEnd_7733249 := by
    simpa [prefixWord, tailWord_7733249, baseEnd_7733249] using wordTrace_append hprefix tailTrace_7733249
  have hstable : (prefixWord ++ tailWord_7733249).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7733249).length < 2 ^ (prefixWord ++ tailWord_7733249).sum := by decide
  have hdescent : baseEnd_7733249 < baseStart_7733249 := by decide
  rcases family_descends (prefixWord ++ tailWord_7733249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7733259 : List Nat := [1, 1, 1, 1, 6, 1, 1, 2, 2, 4, 3]
def baseStart_7733259 : Nat := 118140960795 + 7733259 * 2 ^ 59
def prefixEnd_7733259 : Nat := 4983230072969 + 3 ^ 40 * 7733259 * 2
def baseEnd_7733259 : Nat := 3970878892707864322297895

theorem tailTrace_7733259 : CollatzResearch.WordTrace tailWord_7733259 prefixEnd_7733259 3970878892707864322297895 := by
  unfold tailWord_7733259
  simp only [CollatzResearch.WordTrace]
  refine ⟨282055127490730853333186831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188036751660487235555457887 282055127490730853333186831)
  ·
    refine ⟨423082691236096279999780247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 282055127490730853333186831 423082691236096279999780247)
    ·
      refine ⟨634624036854144419999670371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 423082691236096279999780247 634624036854144419999670371)
      ·
        refine ⟨951936055281216629999505557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 634624036854144419999670371 951936055281216629999505557)
        ·
          refine ⟨44622002591307029531226823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 951936055281216629999505557 44622002591307029531226823)
          ·
            refine ⟨66933003886960544296840235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44622002591307029531226823 66933003886960544296840235)
            ·
              refine ⟨100399505830440816445260353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66933003886960544296840235 100399505830440816445260353)
              ·
                refine ⟨75299629372830612333945265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 100399505830440816445260353 75299629372830612333945265)
                ·
                  refine ⟨56474722029622959250458949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 75299629372830612333945265 56474722029622959250458949)
                  ·
                    refine ⟨10589010380554304859461053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 56474722029622959250458949 10589010380554304859461053)
                    ·
                      refine ⟨3970878892707864322297895, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10589010380554304859461053 3970878892707864322297895)
                      ·
                        rfl

theorem cell23_7733259_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 1, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 1, 2, 2, 4, 3].length) (baseStart_7733259 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7733259 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7733259 prefixEnd_7733259 := by exact prefixLift 7733259
  have htrace : WordTrace (prefixWord ++ tailWord_7733259) baseStart_7733259 baseEnd_7733259 := by
    simpa [prefixWord, tailWord_7733259, baseEnd_7733259] using wordTrace_append hprefix tailTrace_7733259
  have hstable : (prefixWord ++ tailWord_7733259).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7733259).length < 2 ^ (prefixWord ++ tailWord_7733259).sum := by decide
  have hdescent : baseEnd_7733259 < baseStart_7733259 := by decide
  rcases family_descends (prefixWord ++ tailWord_7733259) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7733277 : List Nat := [1, 4, 2, 2, 2, 3, 2, 1, 1, 3, 2]
def baseStart_7733277 : Nat := 118140960795 + 7733277 * 2 ^ 59
def prefixEnd_7733277 : Nat := 4983230072969 + 3 ^ 40 * 7733277 * 2
def baseEnd_7733277 : Nat := 3970888135359645251872813

theorem tailTrace_7733277 : CollatzResearch.WordTrace tailWord_7733277 prefixEnd_7733277 3970888135359645251872813 := by
  unfold tailWord_7733277
  simp only [CollatzResearch.WordTrace]
  refine ⟨282055784004665642407342085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188037189336443761604894723 282055784004665642407342085)
  ·
    refine ⟨52885459500874807951376641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 282055784004665642407342085 52885459500874807951376641)
    ·
      refine ⟨39664094625656105963532481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52885459500874807951376641 39664094625656105963532481)
      ·
        refine ⟨29748070969242079472649361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39664094625656105963532481 29748070969242079472649361)
        ·
          refine ⟨22311053226931559604487021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29748070969242079472649361 22311053226931559604487021)
          ·
            refine ⟨8366644960099334851682633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22311053226931559604487021 8366644960099334851682633)
            ·
              refine ⟨6274983720074501138761975, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8366644960099334851682633 6274983720074501138761975)
              ·
                refine ⟨9412475580111751708142963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6274983720074501138761975 9412475580111751708142963)
                ·
                  refine ⟨14118713370167627562214445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9412475580111751708142963 14118713370167627562214445)
                  ·
                    refine ⟨5294517513812860335830417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14118713370167627562214445 5294517513812860335830417)
                    ·
                      refine ⟨3970888135359645251872813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5294517513812860335830417 3970888135359645251872813)
                      ·
                        rfl

theorem cell23_7733277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 3, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 3, 2, 1, 1, 3, 2].length) (baseStart_7733277 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7733277 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7733277 prefixEnd_7733277 := by exact prefixLift 7733277
  have htrace : WordTrace (prefixWord ++ tailWord_7733277) baseStart_7733277 baseEnd_7733277 := by
    simpa [prefixWord, tailWord_7733277, baseEnd_7733277] using wordTrace_append hprefix tailTrace_7733277
  have hstable : (prefixWord ++ tailWord_7733277).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7733277).length < 2 ^ (prefixWord ++ tailWord_7733277).sum := by decide
  have hdescent : baseEnd_7733277 < baseStart_7733277 := by decide
  rcases family_descends (prefixWord ++ tailWord_7733277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7733290 : List Nat := [3, 1, 4, 1, 2, 2, 1, 1, 4, 2, 2]
def baseStart_7733290 : Nat := 118140960795 + 7733290 * 2 ^ 59
def prefixEnd_7733290 : Nat := 4983230072969 + 3 ^ 40 * 7733290 * 2
def baseEnd_7733290 : Nat := 3970894810608153701010253

theorem tailTrace_7733290 : CollatzResearch.WordTrace tailWord_7733290 prefixEnd_7733290 3970894810608153701010253 := by
  unfold tailWord_7733290
  simp only [CollatzResearch.WordTrace]
  refine ⟨70514064538404636406891331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 188037505435745697085043549 70514064538404636406891331)
  ·
    refine ⟨105771096807606954610336997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70514064538404636406891331 105771096807606954610336997)
    ·
      refine ⟨19832080651426303989438187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 105771096807606954610336997 19832080651426303989438187)
      ·
        refine ⟨29748120977139455984157281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19832080651426303989438187 29748120977139455984157281)
        ·
          refine ⟨22311090732854591988117961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29748120977139455984157281 22311090732854591988117961)
          ·
            refine ⟨16733318049640943991088471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22311090732854591988117961 16733318049640943991088471)
            ·
              refine ⟨25099977074461415986632707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16733318049640943991088471 25099977074461415986632707)
              ·
                refine ⟨37649965611692123979949061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25099977074461415986632707 37649965611692123979949061)
                ·
                  refine ⟨7059368552192273246240449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 37649965611692123979949061 7059368552192273246240449)
                  ·
                    refine ⟨5294526414144204934680337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7059368552192273246240449 5294526414144204934680337)
                    ·
                      refine ⟨3970894810608153701010253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5294526414144204934680337 3970894810608153701010253)
                      ·
                        rfl

theorem cell23_7733290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 2, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 2, 1, 1, 4, 2, 2].length) (baseStart_7733290 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7733290 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7733290 prefixEnd_7733290 := by exact prefixLift 7733290
  have htrace : WordTrace (prefixWord ++ tailWord_7733290) baseStart_7733290 baseEnd_7733290 := by
    simpa [prefixWord, tailWord_7733290, baseEnd_7733290] using wordTrace_append hprefix tailTrace_7733290
  have hstable : (prefixWord ++ tailWord_7733290).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7733290).length < 2 ^ (prefixWord ++ tailWord_7733290).sum := by decide
  have hdescent : baseEnd_7733290 < baseStart_7733290 := by decide
  rcases family_descends (prefixWord ++ tailWord_7733290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7733296 : List Nat := [2, 1, 1, 1, 2, 5, 2, 4, 5]
def baseStart_7733296 : Nat := 118140960795 + 7733296 * 2 ^ 59
def prefixEnd_7733296 : Nat := 4983230072969 + 3 ^ 40 * 7733296 * 2
def baseEnd_7733296 : Nat := 441210876832453408615025

theorem tailTrace_7733296 : CollatzResearch.WordTrace tailWord_7733296 prefixEnd_7733296 441210876832453408615025 := by
  unfold tailWord_7733296
  simp only [CollatzResearch.WordTrace]
  refine ⟨141028238495798404326141871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 188037651327731205768189161 141028238495798404326141871)
  ·
    refine ⟨211542357743697606489212807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141028238495798404326141871 211542357743697606489212807)
    ·
      refine ⟨317313536615546409733819211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 211542357743697606489212807 317313536615546409733819211)
      ·
        refine ⟨475970304923319614600728817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 317313536615546409733819211 475970304923319614600728817)
        ·
          refine ⟨356977728692489710950546613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 475970304923319614600728817 356977728692489710950546613)
          ·
            refine ⟨33466662064920910401613745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 356977728692489710950546613 33466662064920910401613745)
            ·
              refine ⟨25099996548690682801210309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33466662064920910401613745 25099996548690682801210309)
              ·
                refine ⟨4706249352879503025226933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25099996548690682801210309 4706249352879503025226933)
                ·
                  refine ⟨441210876832453408615025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4706249352879503025226933 441210876832453408615025)
                  ·
                    rfl

theorem cell23_7733296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 2, 4, 5].length) (baseStart_7733296 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7733296 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7733296 prefixEnd_7733296 := by exact prefixLift 7733296
  have htrace : WordTrace (prefixWord ++ tailWord_7733296) baseStart_7733296 baseEnd_7733296 := by
    simpa [prefixWord, tailWord_7733296, baseEnd_7733296] using wordTrace_append hprefix tailTrace_7733296
  have hstable : (prefixWord ++ tailWord_7733296).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7733296).length < 2 ^ (prefixWord ++ tailWord_7733296).sum := by decide
  have hdescent : baseEnd_7733296 < baseStart_7733296 := by decide
  rcases family_descends (prefixWord ++ tailWord_7733296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7733309 : List Nat := [1, 4, 1, 3, 1, 1, 1, 1, 3, 7]
def baseStart_7733309 : Nat := 118140960795 + 7733309 * 2 ^ 59
def prefixEnd_7733309 : Nat := 4983230072969 + 3 ^ 40 * 7733309 * 2
def baseEnd_7733309 : Nat := 1323634855580196375557555

theorem tailTrace_7733309 : CollatzResearch.WordTrace tailWord_7733309 prefixEnd_7733309 1323634855580196375557555 := by
  unfold tailWord_7733309
  simp only [CollatzResearch.WordTrace]
  refine ⟨282056951140549711872506981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188037967427033141248337987 282056951140549711872506981)
  ·
    refine ⟨52885678338853070976095059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 282056951140549711872506981 52885678338853070976095059)
    ·
      refine ⟨79328517508279606464142589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52885678338853070976095059 79328517508279606464142589)
      ·
        refine ⟨29748194065604852424053471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 79328517508279606464142589 29748194065604852424053471)
        ·
          refine ⟨44622291098407278636080207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29748194065604852424053471 44622291098407278636080207)
          ·
            refine ⟨66933436647610917954120311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44622291098407278636080207 66933436647610917954120311)
            ·
              refine ⟨100400154971416376931180467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66933436647610917954120311 100400154971416376931180467)
              ·
                refine ⟨150600232457124565396770701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 100400154971416376931180467 150600232457124565396770701)
                ·
                  refine ⟨56475087171421712023789013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 150600232457124565396770701 56475087171421712023789013)
                  ·
                    refine ⟨1323634855580196375557555, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 56475087171421712023789013 1323634855580196375557555)
                    ·
                      rfl

theorem cell23_7733309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 1, 1, 3, 7].length) (baseStart_7733309 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7733309 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7733309 prefixEnd_7733309 := by exact prefixLift 7733309
  have htrace : WordTrace (prefixWord ++ tailWord_7733309) baseStart_7733309 baseEnd_7733309 := by
    simpa [prefixWord, tailWord_7733309, baseEnd_7733309] using wordTrace_append hprefix tailTrace_7733309
  have hstable : (prefixWord ++ tailWord_7733309).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7733309).length < 2 ^ (prefixWord ++ tailWord_7733309).sum := by decide
  have hdescent : baseEnd_7733309 < baseStart_7733309 := by decide
  rcases family_descends (prefixWord ++ tailWord_7733309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7733330 : List Nat := [3, 2, 2, 1, 4, 2, 1, 3, 5]
def baseStart_7733330 : Nat := 118140960795 + 7733330 * 2 ^ 59
def prefixEnd_7733330 : Nat := 4983230072969 + 3 ^ 40 * 7733330 * 2
def baseEnd_7733330 : Nat := 441212816648259282723341

theorem tailTrace_7733330 : CollatzResearch.WordTrace tailWord_7733330 prefixEnd_7733330 441212816648259282723341 := by
  unfold tailWord_7733330
  simp only [CollatzResearch.WordTrace]
  refine ⟨70514429268368408114755361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 188038478048982421639347629 70514429268368408114755361)
  ·
    refine ⟨52885821951276306086066521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70514429268368408114755361 52885821951276306086066521)
    ·
      refine ⟨39664366463457229564549891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52885821951276306086066521 39664366463457229564549891)
      ·
        refine ⟨59496549695185844346824837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39664366463457229564549891 59496549695185844346824837)
        ·
          refine ⟨11155603067847345815029657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 59496549695185844346824837 11155603067847345815029657)
          ·
            refine ⟨8366702300885509361272243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11155603067847345815029657 8366702300885509361272243)
            ·
              refine ⟨12550053451328264041908365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8366702300885509361272243 12550053451328264041908365)
              ·
                refine ⟨4706270044248099015715637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12550053451328264041908365 4706270044248099015715637)
                ·
                  refine ⟨441212816648259282723341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4706270044248099015715637 441212816648259282723341)
                  ·
                    rfl

theorem cell23_7733330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 4, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 4, 2, 1, 3, 5].length) (baseStart_7733330 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7733330 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7733330 prefixEnd_7733330 := by exact prefixLift 7733330
  have htrace : WordTrace (prefixWord ++ tailWord_7733330) baseStart_7733330 baseEnd_7733330 := by
    simpa [prefixWord, tailWord_7733330, baseEnd_7733330] using wordTrace_append hprefix tailTrace_7733330
  have hstable : (prefixWord ++ tailWord_7733330).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7733330).length < 2 ^ (prefixWord ++ tailWord_7733330).sum := by decide
  have hdescent : baseEnd_7733330 < baseStart_7733330 := by decide
  rcases family_descends (prefixWord ++ tailWord_7733330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7733398 : List Nat := [5, 3, 2, 1, 1, 2, 2, 2, 5]
def baseStart_7733398 : Nat := 118140960795 + 7733398 * 2 ^ 59
def prefixEnd_7733398 : Nat := 4983230072969 + 3 ^ 40 * 7733398 * 2
def baseEnd_7733398 : Nat := 441216696279871030939973

theorem tailTrace_7733398 : CollatzResearch.WordTrace tailWord_7733398 prefixEnd_7733398 441216696279871030939973 := by
  unfold tailWord_7733398
  simp only [CollatzResearch.WordTrace]
  refine ⟨17628762327326705004531053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 188040131491484853381664565 17628762327326705004531053)
  ·
    refine ⟨6610785872747514376699145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17628762327326705004531053 6610785872747514376699145)
    ·
      refine ⟨4958089404560635782524359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6610785872747514376699145 4958089404560635782524359)
      ·
        refine ⟨7437134106840953673786539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4958089404560635782524359 7437134106840953673786539)
        ·
          refine ⟨11155701160261430510679809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7437134106840953673786539 11155701160261430510679809)
          ·
            refine ⟨8366775870196072883009857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11155701160261430510679809 8366775870196072883009857)
            ·
              refine ⟨6275081902647054662257393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8366775870196072883009857 6275081902647054662257393)
              ·
                refine ⟨4706311426985290996693045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6275081902647054662257393 4706311426985290996693045)
                ·
                  refine ⟨441216696279871030939973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4706311426985290996693045 441216696279871030939973)
                  ·
                    rfl

theorem cell23_7733398_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 1, 2, 2, 2, 5].length) (baseStart_7733398 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7733398 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7733398 prefixEnd_7733398 := by exact prefixLift 7733398
  have htrace : WordTrace (prefixWord ++ tailWord_7733398) baseStart_7733398 baseEnd_7733398 := by
    simpa [prefixWord, tailWord_7733398, baseEnd_7733398] using wordTrace_append hprefix tailTrace_7733398
  have hstable : (prefixWord ++ tailWord_7733398).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7733398).length < 2 ^ (prefixWord ++ tailWord_7733398).sum := by decide
  have hdescent : baseEnd_7733398 < baseStart_7733398 := by decide
  rcases family_descends (prefixWord ++ tailWord_7733398) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7733407 : List Nat := [1, 1, 2, 6, 1, 1, 4, 2, 1, 4]
def baseStart_7733407 : Nat := 118140960795 + 7733407 * 2 ^ 59
def prefixEnd_7733407 : Nat := 4983230072969 + 3 ^ 40 * 7733407 * 2
def baseEnd_7733407 : Nat := 1323651629281576581082405

theorem tailTrace_7733407 : CollatzResearch.WordTrace tailWord_7733407 prefixEnd_7733407 1323651629281576581082405 := by
  unfold tailWord_7733407
  simp only [CollatzResearch.WordTrace]
  refine ⟨282060525494194674609574475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188040350329463116406382983 282060525494194674609574475)
  ·
    refine ⟨423090788241292011914361713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 282060525494194674609574475 423090788241292011914361713)
    ·
      refine ⟨317318091180969008935771285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 423090788241292011914361713 317318091180969008935771285)
      ·
        refine ⟨14874285524107922293864279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 317318091180969008935771285 14874285524107922293864279)
        ·
          refine ⟨22311428286161883440796419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14874285524107922293864279 22311428286161883440796419)
          ·
            refine ⟨33467142429242825161194629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22311428286161883440796419 33467142429242825161194629)
            ·
              refine ⟨6275089205483029717723993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 33467142429242825161194629 6275089205483029717723993)
              ·
                refine ⟨4706316904112272288292995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6275089205483029717723993 4706316904112272288292995)
                ·
                  refine ⟨7059475356168408432439493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4706316904112272288292995 7059475356168408432439493)
                  ·
                    refine ⟨1323651629281576581082405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7059475356168408432439493 1323651629281576581082405)
                    ·
                      rfl

theorem cell23_7733407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 4, 2, 1, 4].length) (baseStart_7733407 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7733407 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7733407 prefixEnd_7733407 := by exact prefixLift 7733407
  have htrace : WordTrace (prefixWord ++ tailWord_7733407) baseStart_7733407 baseEnd_7733407 := by
    simpa [prefixWord, tailWord_7733407, baseEnd_7733407] using wordTrace_append hprefix tailTrace_7733407
  have hstable : (prefixWord ++ tailWord_7733407).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7733407).length < 2 ^ (prefixWord ++ tailWord_7733407).sum := by decide
  have hdescent : baseEnd_7733407 < baseStart_7733407 := by decide
  rcases family_descends (prefixWord ++ tailWord_7733407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7733413 : List Nat := [1, 3, 1, 2, 1, 3, 2, 3, 3, 1, 3]
def baseStart_7733413 : Nat := 118140960795 + 7733413 * 2 ^ 59
def prefixEnd_7733413 : Nat := 4983230072969 + 3 ^ 40 * 7733413 * 2
def baseEnd_7733413 : Nat := 3970957968728656719772187

theorem tailTrace_7733413 : CollatzResearch.WordTrace tailWord_7733413 prefixEnd_7733413 3970957968728656719772187 := by
  unfold tailWord_7733413
  simp only [CollatzResearch.WordTrace]
  refine ⟨282060744332172937634292893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188040496221448625089528595 282060744332172937634292893)
  ·
    refine ⟨105772779124564851612859835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 282060744332172937634292893 105772779124564851612859835)
    ·
      refine ⟨158659168686847277419289753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105772779124564851612859835 158659168686847277419289753)
      ·
        refine ⟨118994376515135458064467315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 158659168686847277419289753 118994376515135458064467315)
        ·
          refine ⟨178491564772703187096700973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 118994376515135458064467315 178491564772703187096700973)
          ·
            refine ⟨66934336789763695161262865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 178491564772703187096700973 66934336789763695161262865)
            ·
              refine ⟨50200752592322771370947149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66934336789763695161262865 50200752592322771370947149)
              ·
                refine ⟨18825282222121039264105181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 50200752592322771370947149 18825282222121039264105181)
                ·
                  refine ⟨7059480833295389724039443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18825282222121039264105181 7059480833295389724039443)
                  ·
                    refine ⟨10589221249943084586059165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7059480833295389724039443 10589221249943084586059165)
                    ·
                      refine ⟨3970957968728656719772187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10589221249943084586059165 3970957968728656719772187)
                      ·
                        rfl

theorem cell23_7733413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 2, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 2, 3, 3, 1, 3].length) (baseStart_7733413 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7733413 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7733413 prefixEnd_7733413 := by exact prefixLift 7733413
  have htrace : WordTrace (prefixWord ++ tailWord_7733413) baseStart_7733413 baseEnd_7733413 := by
    simpa [prefixWord, tailWord_7733413, baseEnd_7733413] using wordTrace_append hprefix tailTrace_7733413
  have hstable : (prefixWord ++ tailWord_7733413).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7733413).length < 2 ^ (prefixWord ++ tailWord_7733413).sum := by decide
  have hdescent : baseEnd_7733413 < baseStart_7733413 := by decide
  rcases family_descends (prefixWord ++ tailWord_7733413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7733440 : List Nat := [2, 1, 1, 2, 5, 1, 3, 1, 2, 3, 2]
def baseStart_7733440 : Nat := 118140960795 + 7733440 * 2 ^ 59
def prefixEnd_7733440 : Nat := 4983230072969 + 3 ^ 40 * 7733440 * 2
def baseEnd_7733440 : Nat := 3970971832706328114134563

theorem tailTrace_7733440 : CollatzResearch.WordTrace tailWord_7733440 prefixEnd_7733440 3970971832706328114134563 := by
  unfold tailWord_7733440
  simp only [CollatzResearch.WordTrace]
  refine ⟨141030864551537560622762887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 188041152735383414163683849 141030864551537560622762887)
  ·
    refine ⟨211546296827306340934144331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141030864551537560622762887 211546296827306340934144331)
    ·
      refine ⟨317319445240959511401216497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 211546296827306340934144331 317319445240959511401216497)
      ·
        refine ⟨237989583930719633550912373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 317319445240959511401216497 237989583930719633550912373)
        ·
          refine ⟨22311523493504965645398035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 237989583930719633550912373 22311523493504965645398035)
          ·
            refine ⟨33467285240257448468097053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22311523493504965645398035 33467285240257448468097053)
            ·
              refine ⟨12550231965096543175536395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33467285240257448468097053 12550231965096543175536395)
              ·
                refine ⟨18825347947644814763304593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12550231965096543175536395 18825347947644814763304593)
                ·
                  refine ⟨14119010960733611072478445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18825347947644814763304593 14119010960733611072478445)
                  ·
                    refine ⟨5294629110275104152179417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14119010960733611072478445 5294629110275104152179417)
                    ·
                      refine ⟨3970971832706328114134563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5294629110275104152179417 3970971832706328114134563)
                      ·
                        rfl

theorem cell23_7733440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 3, 1, 2, 3, 2].length) (baseStart_7733440 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7733440 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7733440 prefixEnd_7733440 := by exact prefixLift 7733440
  have htrace : WordTrace (prefixWord ++ tailWord_7733440) baseStart_7733440 baseEnd_7733440 := by
    simpa [prefixWord, tailWord_7733440, baseEnd_7733440] using wordTrace_append hprefix tailTrace_7733440
  have hstable : (prefixWord ++ tailWord_7733440).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7733440).length < 2 ^ (prefixWord ++ tailWord_7733440).sum := by decide
  have hdescent : baseEnd_7733440 < baseStart_7733440 := by decide
  rcases family_descends (prefixWord ++ tailWord_7733440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7733466 : List Nat := [3, 1, 1, 2, 2, 1, 2, 2, 3, 2, 4]
def baseStart_7733466 : Nat := 118140960795 + 7733466 * 2 ^ 59
def prefixEnd_7733466 : Nat := 4983230072969 + 3 ^ 40 * 7733466 * 2
def baseEnd_7733466 : Nat := 3970985183203345012409443

theorem tailTrace_7733466 : CollatzResearch.WordTrace tailWord_7733466 prefixEnd_7733466 3970985183203345012409443 := by
  unfold tailWord_7733466
  simp only [CollatzResearch.WordTrace]
  refine ⟨70515669350245231921493063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 188041784933987285123981501 70515669350245231921493063)
  ·
    refine ⟨105773504025367847882239595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70515669350245231921493063 105773504025367847882239595)
    ·
      refine ⟨158660256038051771823359393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105773504025367847882239595 158660256038051771823359393)
      ·
        refine ⟨118995192028538828867519545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 158660256038051771823359393 118995192028538828867519545)
        ·
          refine ⟨89246394021404121650639659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 118995192028538828867519545 89246394021404121650639659)
          ·
            refine ⟨133869591032106182475959489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89246394021404121650639659 133869591032106182475959489)
            ·
              refine ⟨100402193274079636856969617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 133869591032106182475959489 100402193274079636856969617)
              ·
                refine ⟨75301644955559727642727213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 100402193274079636856969617 75301644955559727642727213)
                ·
                  refine ⟨28238116858334897866022705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 75301644955559727642727213 28238116858334897866022705)
                  ·
                    refine ⟨21178587643751173399517029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28238116858334897866022705 21178587643751173399517029)
                    ·
                      refine ⟨3970985183203345012409443, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21178587643751173399517029 3970985183203345012409443)
                      ·
                        rfl

theorem cell23_7733466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 2, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 2, 2, 3, 2, 4].length) (baseStart_7733466 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7733466 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7733466 prefixEnd_7733466 := by exact prefixLift 7733466
  have htrace : WordTrace (prefixWord ++ tailWord_7733466) baseStart_7733466 baseEnd_7733466 := by
    simpa [prefixWord, tailWord_7733466, baseEnd_7733466] using wordTrace_append hprefix tailTrace_7733466
  have hstable : (prefixWord ++ tailWord_7733466).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7733466).length < 2 ^ (prefixWord ++ tailWord_7733466).sum := by decide
  have hdescent : baseEnd_7733466 < baseStart_7733466 := by decide
  rcases family_descends (prefixWord ++ tailWord_7733466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7733490 : List Nat := [3, 2, 1, 3, 2, 1, 1, 4, 1, 2, 3]
def baseStart_7733490 : Nat := 118140960795 + 7733490 * 2 ^ 59
def prefixEnd_7733490 : Nat := 4983230072969 + 3 ^ 40 * 7733490 * 2
def baseEnd_7733490 : Nat := 3970997506739052918509333

theorem tailTrace_7733490 : CollatzResearch.WordTrace tailWord_7733490 prefixEnd_7733490 3970997506739052918509333 := by
  unfold tailWord_7733490
  simp only [CollatzResearch.WordTrace]
  refine ⟨70515888188223494946211481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 188042368501929319856563949 70515888188223494946211481)
  ·
    refine ⟨52886916141167621209658611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70515888188223494946211481 52886916141167621209658611)
    ·
      refine ⟨79330374211751431814487917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52886916141167621209658611 79330374211751431814487917)
      ·
        refine ⟨29748890329406786930432969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 79330374211751431814487917 29748890329406786930432969)
        ·
          refine ⟨22311667747055090197824727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29748890329406786930432969 22311667747055090197824727)
          ·
            refine ⟨33467501620582635296737091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22311667747055090197824727 33467501620582635296737091)
            ·
              refine ⟨50201252430873952945105637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33467501620582635296737091 50201252430873952945105637)
              ·
                refine ⟨9412734830788866177207307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 50201252430873952945105637 9412734830788866177207307)
                ·
                  refine ⟨14119102246183299265810961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9412734830788866177207307 14119102246183299265810961)
                  ·
                    refine ⟨10589326684637474449358221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14119102246183299265810961 10589326684637474449358221)
                    ·
                      refine ⟨3970997506739052918509333, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10589326684637474449358221 3970997506739052918509333)
                      ·
                        rfl

theorem cell23_7733490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 1, 4, 1, 2, 3].length) (baseStart_7733490 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7733490 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7733490 prefixEnd_7733490 := by exact prefixLift 7733490
  have htrace : WordTrace (prefixWord ++ tailWord_7733490) baseStart_7733490 baseEnd_7733490 := by
    simpa [prefixWord, tailWord_7733490, baseEnd_7733490] using wordTrace_append hprefix tailTrace_7733490
  have hstable : (prefixWord ++ tailWord_7733490).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7733490).length < 2 ^ (prefixWord ++ tailWord_7733490).sum := by decide
  have hdescent : baseEnd_7733490 < baseStart_7733490 := by decide
  rcases family_descends (prefixWord ++ tailWord_7733490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7733503 : List Nat := [1, 1, 2, 2, 1, 4, 1, 1, 6, 1, 3]
def baseStart_7733503 : Nat := 118140960795 + 7733503 * 2 ^ 59
def prefixEnd_7733503 : Nat := 4983230072969 + 3 ^ 40 * 7733503 * 2
def baseEnd_7733503 : Nat := 3971004181987561367646773

theorem tailTrace_7733503 : CollatzResearch.WordTrace tailWord_7733503 prefixEnd_7733503 3971004181987561367646773 := by
  unfold tailWord_7733503
  simp only [CollatzResearch.WordTrace]
  refine ⟨282064026901846883005069163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188042684601231255336712775 282064026901846883005069163)
  ·
    refine ⟨423096040352770324507603745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 282064026901846883005069163 423096040352770324507603745)
    ·
      refine ⟨317322030264577743380702809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 423096040352770324507603745 317322030264577743380702809)
      ·
        refine ⟨237991522698433307535527107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 317322030264577743380702809 237991522698433307535527107)
        ·
          refine ⟨356987284047649961303290661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 237991522698433307535527107 356987284047649961303290661)
          ·
            refine ⟨66935115758934367744366999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 356987284047649961303290661 66935115758934367744366999)
            ·
              refine ⟨100402673638401551616550499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66935115758934367744366999 100402673638401551616550499)
              ·
                refine ⟨150604010457602327424825749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 100402673638401551616550499 150604010457602327424825749)
                ·
                  refine ⟨7059562990200109098038707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 150604010457602327424825749 7059562990200109098038707)
                  ·
                    refine ⟨10589344485300163647058061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7059562990200109098038707 10589344485300163647058061)
                    ·
                      refine ⟨3971004181987561367646773, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10589344485300163647058061 3971004181987561367646773)
                      ·
                        rfl

theorem cell23_7733503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 1, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 1, 1, 6, 1, 3].length) (baseStart_7733503 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7733503 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7733503 prefixEnd_7733503 := by exact prefixLift 7733503
  have htrace : WordTrace (prefixWord ++ tailWord_7733503) baseStart_7733503 baseEnd_7733503 := by
    simpa [prefixWord, tailWord_7733503, baseEnd_7733503] using wordTrace_append hprefix tailTrace_7733503
  have hstable : (prefixWord ++ tailWord_7733503).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7733503).length < 2 ^ (prefixWord ++ tailWord_7733503).sum := by decide
  have hdescent : baseEnd_7733503 < baseStart_7733503 := by decide
  rcases family_descends (prefixWord ++ tailWord_7733503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7733516 : List Nat := [2, 2, 1, 2, 2, 2, 1, 2, 2, 2, 5]
def baseStart_7733516 : Nat := 118140960795 + 7733516 * 2 ^ 59
def prefixEnd_7733516 : Nat := 4983230072969 + 3 ^ 40 * 7733516 * 2
def baseEnd_7733516 : Nat := 3971010857236069816784213

theorem tailTrace_7733516 : CollatzResearch.WordTrace tailWord_7733516 prefixEnd_7733516 3971010857236069816784213 := by
  unfold tailWord_7733516
  simp only [CollatzResearch.WordTrace]
  refine ⟨141032250525399893112646201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 188043000700533190816861601 141032250525399893112646201)
  ·
    refine ⟨105774187894049919834484651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 141032250525399893112646201 105774187894049919834484651)
    ·
      refine ⟨158661281841074879751726977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105774187894049919834484651 158661281841074879751726977)
      ·
        refine ⟨118995961380806159813795233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 158661281841074879751726977 118995961380806159813795233)
        ·
          refine ⟨89246971035604619860346425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 118995961380806159813795233 89246971035604619860346425)
          ·
            refine ⟨66935228276703464895259819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 89246971035604619860346425 66935228276703464895259819)
            ·
              refine ⟨100402842415055197342889729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66935228276703464895259819 100402842415055197342889729)
              ·
                refine ⟨75302131811291398007167297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 100402842415055197342889729 75302131811291398007167297)
                ·
                  refine ⟨56476598858468548505375473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 75302131811291398007167297 56476598858468548505375473)
                  ·
                    refine ⟨42357449143851411379031605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 56476598858468548505375473 42357449143851411379031605)
                    ·
                      refine ⟨3971010857236069816784213, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42357449143851411379031605 3971010857236069816784213)
                      ·
                        rfl

theorem cell23_7733516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 1, 2, 2, 2, 5].length) (baseStart_7733516 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7733516 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7733516 prefixEnd_7733516 := by exact prefixLift 7733516
  have htrace : WordTrace (prefixWord ++ tailWord_7733516) baseStart_7733516 baseEnd_7733516 := by
    simpa [prefixWord, tailWord_7733516, baseEnd_7733516] using wordTrace_append hprefix tailTrace_7733516
  have hstable : (prefixWord ++ tailWord_7733516).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7733516).length < 2 ^ (prefixWord ++ tailWord_7733516).sum := by decide
  have hdescent : baseEnd_7733516 < baseStart_7733516 := by decide
  rcases family_descends (prefixWord ++ tailWord_7733516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7733537 : List Nat := [1, 2, 3, 2, 1, 1, 6, 1, 2, 1, 3]
def baseStart_7733537 : Nat := 118140960795 + 7733537 * 2 ^ 59
def prefixEnd_7733537 : Nat := 4983230072969 + 3 ^ 40 * 7733537 * 2
def baseEnd_7733537 : Nat := 3971021640329814234621617

theorem tailTrace_7733537 : CollatzResearch.WordTrace tailWord_7733537 prefixEnd_7733537 3971021640329814234621617 := by
  unfold tailWord_7733537
  simp only [CollatzResearch.WordTrace]
  refine ⟨282065266983723706811806865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188043511322482471207871243 282065266983723706811806865)
  ·
    refine ⟨211548950237792780108855149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 282065266983723706811806865 211548950237792780108855149)
    ·
      refine ⟨79330856339172292540820681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 211548950237792780108855149 79330856339172292540820681)
      ·
        refine ⟨59498142254379219405615511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79330856339172292540820681 59498142254379219405615511)
        ·
          refine ⟨89247213381568829108423267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59498142254379219405615511 89247213381568829108423267)
          ·
            refine ⟨133870820072353243662634901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89247213381568829108423267 133870820072353243662634901)
            ·
              refine ⟨6275194690891558296686011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 133870820072353243662634901 6275194690891558296686011)
              ·
                refine ⟨9412792036337337445029017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6275194690891558296686011 9412792036337337445029017)
                ·
                  refine ⟨7059594027253003083771763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9412792036337337445029017 7059594027253003083771763)
                  ·
                    refine ⟨10589391040879504625657645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7059594027253003083771763 10589391040879504625657645)
                    ·
                      refine ⟨3971021640329814234621617, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10589391040879504625657645 3971021640329814234621617)
                      ·
                        rfl

theorem cell23_7733537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 6, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 6, 1, 2, 1, 3].length) (baseStart_7733537 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7733537 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7733537 prefixEnd_7733537 := by exact prefixLift 7733537
  have htrace : WordTrace (prefixWord ++ tailWord_7733537) baseStart_7733537 baseEnd_7733537 := by
    simpa [prefixWord, tailWord_7733537, baseEnd_7733537] using wordTrace_append hprefix tailTrace_7733537
  have hstable : (prefixWord ++ tailWord_7733537).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7733537).length < 2 ^ (prefixWord ++ tailWord_7733537).sum := by decide
  have hdescent : baseEnd_7733537 < baseStart_7733537 := by decide
  rcases family_descends (prefixWord ++ tailWord_7733537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7733560 : List Nat := [2, 1, 2, 1, 3, 1, 2, 1, 6, 2, 2]
def baseStart_7733560 : Nat := 118140960795 + 7733560 * 2 ^ 59
def prefixEnd_7733560 : Nat := 4983230072969 + 3 ^ 40 * 7733560 * 2
def baseEnd_7733560 : Nat := 3971033450384867644634011

theorem tailTrace_7733560 : CollatzResearch.WordTrace tailWord_7733560 prefixEnd_7733560 3971033450384867644634011 := by
  unfold tailWord_7733560
  simp only [CollatzResearch.WordTrace]
  refine ⟨141033052931320190869947067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 188044070575093587826596089 141033052931320190869947067)
  ·
    refine ⟨211549579396980286304920601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141033052931320190869947067 211549579396980286304920601)
    ·
      refine ⟨158662184547735214728690451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 211549579396980286304920601 158662184547735214728690451)
      ·
        refine ⟨237993276821602822093035677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 158662184547735214728690451 237993276821602822093035677)
        ·
          refine ⟨89247478808101058284888379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 237993276821602822093035677 89247478808101058284888379)
          ·
            refine ⟨133871218212151587427332569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89247478808101058284888379 133871218212151587427332569)
            ·
              refine ⟨100403413659113690570499427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 133871218212151587427332569 100403413659113690570499427)
              ·
                refine ⟨150605120488670535855749141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 100403413659113690570499427 150605120488670535855749141)
                ·
                  refine ⟨7059615022906431368238241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 150605120488670535855749141 7059615022906431368238241)
                  ·
                    refine ⟨5294711267179823526178681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7059615022906431368238241 5294711267179823526178681)
                    ·
                      refine ⟨3971033450384867644634011, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5294711267179823526178681 3971033450384867644634011)
                      ·
                        rfl

theorem cell23_7733560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 2, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 2, 1, 6, 2, 2].length) (baseStart_7733560 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7733560 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7733560 prefixEnd_7733560 := by exact prefixLift 7733560
  have htrace : WordTrace (prefixWord ++ tailWord_7733560) baseStart_7733560 baseEnd_7733560 := by
    simpa [prefixWord, tailWord_7733560, baseEnd_7733560] using wordTrace_append hprefix tailTrace_7733560
  have hstable : (prefixWord ++ tailWord_7733560).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7733560).length < 2 ^ (prefixWord ++ tailWord_7733560).sum := by decide
  have hdescent : baseEnd_7733560 < baseStart_7733560 := by decide
  rcases family_descends (prefixWord ++ tailWord_7733560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7733576 : List Nat := [2, 1, 3, 1, 1, 2, 2, 1, 1, 2, 7]
def baseStart_7733576 : Nat := 118140960795 + 7733576 * 2 ^ 59
def prefixEnd_7733576 : Nat := 4983230072969 + 3 ^ 40 * 7733576 * 2
def baseEnd_7733576 : Nat := 3971041666075339582033937

theorem tailTrace_7733576 : CollatzResearch.WordTrace tailWord_7733576 prefixEnd_7733576 3971041666075339582033937 := by
  unfold tailWord_7733576
  simp only [CollatzResearch.WordTrace]
  refine ⟨141033344715291208236238291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 188044459620388277648317721 141033344715291208236238291)
  ·
    refine ⟨211550017072936812354357437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141033344715291208236238291 211550017072936812354357437)
    ·
      refine ⟨79331256402351304632884039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 211550017072936812354357437 79331256402351304632884039)
      ·
        refine ⟨118996884603526956949326059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79331256402351304632884039 118996884603526956949326059)
        ·
          refine ⟨178495326905290435423989089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 118996884603526956949326059 178495326905290435423989089)
          ·
            refine ⟨133871495178967826567991817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 178495326905290435423989089 133871495178967826567991817)
            ·
              refine ⟨100403621384225869925993863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 133871495178967826567991817 100403621384225869925993863)
              ·
                refine ⟨150605432076338804888990795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 100403621384225869925993863 150605432076338804888990795)
                ·
                  refine ⟨225908148114508207333486193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 150605432076338804888990795 225908148114508207333486193)
                  ·
                    refine ⟨169431111085881155500114645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 225908148114508207333486193 169431111085881155500114645)
                    ·
                      refine ⟨3971041666075339582033937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 169431111085881155500114645 3971041666075339582033937)
                      ·
                        rfl

theorem cell23_7733576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 2, 1, 1, 2, 7].length) (baseStart_7733576 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7733576 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7733576 prefixEnd_7733576 := by exact prefixLift 7733576
  have htrace : WordTrace (prefixWord ++ tailWord_7733576) baseStart_7733576 baseEnd_7733576 := by
    simpa [prefixWord, tailWord_7733576, baseEnd_7733576] using wordTrace_append hprefix tailTrace_7733576
  have hstable : (prefixWord ++ tailWord_7733576).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7733576).length < 2 ^ (prefixWord ++ tailWord_7733576).sum := by decide
  have hdescent : baseEnd_7733576 < baseStart_7733576 := by decide
  rcases family_descends (prefixWord ++ tailWord_7733576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7733613 : List Nat := [1, 5, 1, 1, 1, 2, 3, 1, 1, 7]
def baseStart_7733613 : Nat := 118140960795 + 7733613 * 2 ^ 59
def prefixEnd_7733613 : Nat := 4983230072969 + 3 ^ 40 * 7733613 * 2
def baseEnd_7733613 : Nat := 1323686888286518645757089

theorem tailTrace_7733613 : CollatzResearch.WordTrace tailWord_7733613 prefixEnd_7733613 1323686888286518645757089 := by
  unfold tailWord_7733613
  simp only [CollatzResearch.WordTrace]
  refine ⟨282068038931448371791573493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188045359287632247861048995 282068038931448371791573493)
  ·
    refine ⟨26443878649823284855460015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 282068038931448371791573493 26443878649823284855460015)
    ·
      refine ⟨39665817974734927283190023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26443878649823284855460015 39665817974734927283190023)
      ·
        refine ⟨59498726962102390924785035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39665817974734927283190023 59498726962102390924785035)
        ·
          refine ⟨89248090443153586387177553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59498726962102390924785035 89248090443153586387177553)
          ·
            refine ⟨66936067832365189790383165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 89248090443153586387177553 66936067832365189790383165)
            ·
              refine ⟨25101025437136946171393687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 66936067832365189790383165 25101025437136946171393687)
              ·
                refine ⟨37651538155705419257090531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25101025437136946171393687 37651538155705419257090531)
                ·
                  refine ⟨56477307233558128885635797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37651538155705419257090531 56477307233558128885635797)
                  ·
                    refine ⟨1323686888286518645757089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 56477307233558128885635797 1323686888286518645757089)
                    ·
                      rfl

theorem cell23_7733613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 3, 1, 1, 7].length) (baseStart_7733613 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7733613 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7733613 prefixEnd_7733613 := by exact prefixLift 7733613
  have htrace : WordTrace (prefixWord ++ tailWord_7733613) baseStart_7733613 baseEnd_7733613 := by
    simpa [prefixWord, tailWord_7733613, baseEnd_7733613] using wordTrace_append hprefix tailTrace_7733613
  have hstable : (prefixWord ++ tailWord_7733613).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7733613).length < 2 ^ (prefixWord ++ tailWord_7733613).sum := by decide
  have hdescent : baseEnd_7733613 < baseStart_7733613 := by decide
  rcases family_descends (prefixWord ++ tailWord_7733613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7733663 : List Nat := [1, 1, 2, 5, 1, 1, 1, 1, 2, 4, 4]
def baseStart_7733663 : Nat := 118140960795 + 7733663 * 2 ^ 59
def prefixEnd_7733663 : Nat := 4983230072969 + 3 ^ 40 * 7733663 * 2
def baseEnd_7733663 : Nat := 3971086338892280741646037

theorem tailTrace_7733663 : CollatzResearch.WordTrace tailWord_7733663 prefixEnd_7733663 3971086338892280741646037 := by
  unfold tailWord_7733663
  simp only [CollatzResearch.WordTrace]
  refine ⟨282069862581267230330893643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188046575054178153553929095 282069862581267230330893643)
  ·
    refine ⟨423104793871900845496340465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 282069862581267230330893643 423104793871900845496340465)
    ·
      refine ⟨317328595403925634122255349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 423104793871900845496340465 317328595403925634122255349)
      ·
        refine ⟨29749555819118028198961439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 317328595403925634122255349 29749555819118028198961439)
        ·
          refine ⟨44624333728677042298442159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29749555819118028198961439 44624333728677042298442159)
          ·
            refine ⟨66936500593015563447663239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44624333728677042298442159 66936500593015563447663239)
            ·
              refine ⟨100404750889523345171494859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66936500593015563447663239 100404750889523345171494859)
              ·
                refine ⟨150607126334285017757242289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 100404750889523345171494859 150607126334285017757242289)
                ·
                  refine ⟨112955344750713763317931717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 150607126334285017757242289 112955344750713763317931717)
                  ·
                    refine ⟨21179127140758830622112197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 112955344750713763317931717 21179127140758830622112197)
                    ·
                      refine ⟨3971086338892280741646037, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21179127140758830622112197 3971086338892280741646037)
                      ·
                        rfl

theorem cell23_7733663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 1, 1, 2, 4, 4].length) (baseStart_7733663 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7733663 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7733663 prefixEnd_7733663 := by exact prefixLift 7733663
  have htrace : WordTrace (prefixWord ++ tailWord_7733663) baseStart_7733663 baseEnd_7733663 := by
    simpa [prefixWord, tailWord_7733663, baseEnd_7733663] using wordTrace_append hprefix tailTrace_7733663
  have hstable : (prefixWord ++ tailWord_7733663).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7733663).length < 2 ^ (prefixWord ++ tailWord_7733663).sum := by decide
  have hdescent : baseEnd_7733663 < baseStart_7733663 := by decide
  rcases family_descends (prefixWord ++ tailWord_7733663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7733727 : List Nat := [1, 1, 2, 3, 3, 2, 1, 3, 2, 3, 2]
def baseStart_7733727 : Nat := 118140960795 + 7733727 * 2 ^ 59
def prefixEnd_7733727 : Nat := 4983230072969 + 3 ^ 40 * 7733727 * 2
def baseEnd_7733727 : Nat := 3971119201654168491245743

theorem tailTrace_7733727 : CollatzResearch.WordTrace tailWord_7733727 prefixEnd_7733727 3971119201654168491245743 := by
  unfold tailWord_7733727
  simp only [CollatzResearch.WordTrace]
  refine ⟨282072196853035369261223435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188048131235356912840815623 282072196853035369261223435)
  ·
    refine ⟨423108295279553053891835153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 282072196853035369261223435 423108295279553053891835153)
    ·
      refine ⟨317331221459664790418876365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 423108295279553053891835153 317331221459664790418876365)
      ·
        refine ⟨118999208047374296407078637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 317331221459664790418876365 118999208047374296407078637)
        ·
          refine ⟨44624703017765361152654489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 118999208047374296407078637 44624703017765361152654489)
          ·
            refine ⟨33468527263324020864490867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44624703017765361152654489 33468527263324020864490867)
            ·
              refine ⟨50202790894986031296736301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33468527263324020864490867 50202790894986031296736301)
              ·
                refine ⟨18826046585619761736276113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 50202790894986031296736301 18826046585619761736276113)
                ·
                  refine ⟨14119534939214821302207085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18826046585619761736276113 14119534939214821302207085)
                  ·
                    refine ⟨5294825602205557988327657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14119534939214821302207085 5294825602205557988327657)
                    ·
                      refine ⟨3971119201654168491245743, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5294825602205557988327657 3971119201654168491245743)
                      ·
                        rfl

theorem cell23_7733727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 1, 3, 2, 3, 2].length) (baseStart_7733727 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7733727 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7733727 prefixEnd_7733727 := by exact prefixLift 7733727
  have htrace : WordTrace (prefixWord ++ tailWord_7733727) baseStart_7733727 baseEnd_7733727 := by
    simpa [prefixWord, tailWord_7733727, baseEnd_7733727] using wordTrace_append hprefix tailTrace_7733727
  have hstable : (prefixWord ++ tailWord_7733727).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7733727).length < 2 ^ (prefixWord ++ tailWord_7733727).sum := by decide
  have hdescent : baseEnd_7733727 < baseStart_7733727 := by decide
  rcases family_descends (prefixWord ++ tailWord_7733727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7733750 : List Nat := [5, 1, 1, 1, 2, 1, 1, 2, 3, 6]
def baseStart_7733750 : Nat := 118140960795 + 7733750 * 2 ^ 59
def prefixEnd_7733750 : Nat := 4983230072969 + 3 ^ 40 * 7733750 * 2
def baseEnd_7733750 : Nat := 1323710337236407300419379

theorem tailTrace_7733750 : CollatzResearch.WordTrace tailWord_7733750 prefixEnd_7733750 1323710337236407300419379 := by
  unfold tailWord_7733750
  simp only [CollatzResearch.WordTrace]
  refine ⟨17629564733247002761831919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 188048690487968029459540469 17629564733247002761831919)
  ·
    refine ⟨26444347099870504142747879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17629564733247002761831919 26444347099870504142747879)
    ·
      refine ⟨39666520649805756214121819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26444347099870504142747879 39666520649805756214121819)
      ·
        refine ⟨59499780974708634321182729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39666520649805756214121819 59499780974708634321182729)
        ·
          refine ⟨44624835731031475740887047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59499780974708634321182729 44624835731031475740887047)
          ·
            refine ⟨66937253596547213611330571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44624835731031475740887047 66937253596547213611330571)
            ·
              refine ⟨100405880394820820416995857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66937253596547213611330571 100405880394820820416995857)
              ·
                refine ⟨75304410296115615312746893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 100405880394820820416995857 75304410296115615312746893)
                ·
                  refine ⟨28239153861043355742280085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 75304410296115615312746893 28239153861043355742280085)
                  ·
                    refine ⟨1323710337236407300419379, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28239153861043355742280085 1323710337236407300419379)
                    ·
                      rfl

theorem cell23_7733750_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 1, 2, 3, 6].length) (baseStart_7733750 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7733750 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7733750 prefixEnd_7733750 := by exact prefixLift 7733750
  have htrace : WordTrace (prefixWord ++ tailWord_7733750) baseStart_7733750 baseEnd_7733750 := by
    simpa [prefixWord, tailWord_7733750, baseEnd_7733750] using wordTrace_append hprefix tailTrace_7733750
  have hstable : (prefixWord ++ tailWord_7733750).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7733750).length < 2 ^ (prefixWord ++ tailWord_7733750).sum := by decide
  have hdescent : baseEnd_7733750 < baseStart_7733750 := by decide
  rcases family_descends (prefixWord ++ tailWord_7733750) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7733753 : List Nat := [1, 2, 1, 3, 1, 2, 2, 1, 3, 1, 6]
def baseStart_7733753 : Nat := 118140960795 + 7733753 * 2 ^ 59
def prefixEnd_7733753 : Nat := 4983230072969 + 3 ^ 40 * 7733753 * 2
def baseEnd_7733753 : Nat := 3971132552151185389520623

theorem tailTrace_7733753 : CollatzResearch.WordTrace tailWord_7733753 prefixEnd_7733753 3971132552151185389520623 := by
  unfold tailWord_7733753
  simp only [CollatzResearch.WordTrace]
  refine ⟨282073145150941175701669913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188048763433960783801113275 282073145150941175701669913)
  ·
    refine ⟨211554858863205881776252435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 282073145150941175701669913 211554858863205881776252435)
    ·
      refine ⟨317332288294808822664378653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 211554858863205881776252435 317332288294808822664378653)
      ·
        refine ⟨118999608110553308499141995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 317332288294808822664378653 118999608110553308499141995)
        ·
          refine ⟨178499412165829962748712993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 118999608110553308499141995 178499412165829962748712993)
          ·
            refine ⟨133874559124372472061534745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 178499412165829962748712993 133874559124372472061534745)
            ·
              refine ⟨100405919343279354046151059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 133874559124372472061534745 100405919343279354046151059)
              ·
                refine ⟨150608879014919031069226589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 100405919343279354046151059 150608879014919031069226589)
                ·
                  refine ⟨56478329630594636650959971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 150608879014919031069226589 56478329630594636650959971)
                  ·
                    refine ⟨84717494445891954976439957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 56478329630594636650959971 84717494445891954976439957)
                    ·
                      refine ⟨3971132552151185389520623, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 84717494445891954976439957 3971132552151185389520623)
                      ·
                        rfl

theorem cell23_7733753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 2, 1, 3, 1, 6].length) (baseStart_7733753 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7733753 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7733753 prefixEnd_7733753 := by exact prefixLift 7733753
  have htrace : WordTrace (prefixWord ++ tailWord_7733753) baseStart_7733753 baseEnd_7733753 := by
    simpa [prefixWord, tailWord_7733753, baseEnd_7733753] using wordTrace_append hprefix tailTrace_7733753
  have hstable : (prefixWord ++ tailWord_7733753).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7733753).length < 2 ^ (prefixWord ++ tailWord_7733753).sum := by decide
  have hdescent : baseEnd_7733753 < baseStart_7733753 := by decide
  rcases family_descends (prefixWord ++ tailWord_7733753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7733767 : List Nat := [1, 1, 4, 3, 3, 1, 2, 1, 1, 6]
def baseStart_7733767 : Nat := 118140960795 + 7733767 * 2 ^ 59
def prefixEnd_7733767 : Nat := 4983230072969 + 3 ^ 40 * 7733767 * 2
def baseEnd_7733767 : Nat := 1323713246960116111581853

theorem tailTrace_7733767 : CollatzResearch.WordTrace tailWord_7733767 prefixEnd_7733767 1323713246960116111581853 := by
  unfold tailWord_7733767
  simp only [CollatzResearch.WordTrace]
  refine ⟨282073655772890456092679555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188049103848593637395119703 282073655772890456092679555)
  ·
    refine ⟨423110483659335684139019333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 282073655772890456092679555 423110483659335684139019333)
    ·
      refine ⟨79333215686125440776066125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 423110483659335684139019333 79333215686125440776066125)
      ·
        refine ⟨29749955882297040291024797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 79333215686125440776066125 29749955882297040291024797)
        ·
          refine ⟨11156233455861390109134299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29749955882297040291024797 11156233455861390109134299)
          ·
            refine ⟨16734350183792085163701449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11156233455861390109134299 16734350183792085163701449)
            ·
              refine ⟨12550762637844063872776087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16734350183792085163701449 12550762637844063872776087)
              ·
                refine ⟨18826143956766095809164131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12550762637844063872776087 18826143956766095809164131)
                ·
                  refine ⟨28239215935149143713746197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18826143956766095809164131 28239215935149143713746197)
                  ·
                    refine ⟨1323713246960116111581853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28239215935149143713746197 1323713246960116111581853)
                    ·
                      rfl

theorem cell23_7733767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 3, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 3, 1, 2, 1, 1, 6].length) (baseStart_7733767 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7733767 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7733767 prefixEnd_7733767 := by exact prefixLift 7733767
  have htrace : WordTrace (prefixWord ++ tailWord_7733767) baseStart_7733767 baseEnd_7733767 := by
    simpa [prefixWord, tailWord_7733767, baseEnd_7733767] using wordTrace_append hprefix tailTrace_7733767
  have hstable : (prefixWord ++ tailWord_7733767).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7733767).length < 2 ^ (prefixWord ++ tailWord_7733767).sum := by decide
  have hdescent : baseEnd_7733767 < baseStart_7733767 := by decide
  rcases family_descends (prefixWord ++ tailWord_7733767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7733774 : List Nat := [4, 1, 1, 2, 3, 1, 1, 1, 5, 2, 2]
def baseStart_7733774 : Nat := 118140960795 + 7733774 * 2 ^ 59
def prefixEnd_7733774 : Nat := 4983230072969 + 3 ^ 40 * 7733774 * 2
def baseEnd_7733774 : Nat := 3971143335244929807358027

theorem tailTrace_7733774 : CollatzResearch.WordTrace tailWord_7733774 prefixEnd_7733774 3971143335244929807358027 := by
  unfold tailWord_7733774
  simp only [CollatzResearch.WordTrace]
  refine ⟨35259238885483137036023047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 188049274055910064192122917 35259238885483137036023047)
  ·
    refine ⟨52888858328224705554034571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35259238885483137036023047 52888858328224705554034571)
    ·
      refine ⟨79333287492337058331051857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52888858328224705554034571 79333287492337058331051857)
      ·
        refine ⟨59499965619252793748288893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79333287492337058331051857 59499965619252793748288893)
        ·
          refine ⟨22312487107219797655608335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 59499965619252793748288893 22312487107219797655608335)
          ·
            refine ⟨33468730660829696483412503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22312487107219797655608335 33468730660829696483412503)
            ·
              refine ⟨50203095991244544725118755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33468730660829696483412503 50203095991244544725118755)
              ·
                refine ⟨75304643986866817087678133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50203095991244544725118755 75304643986866817087678133)
                ·
                  refine ⟨7059810373768764101969825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 75304643986866817087678133 7059810373768764101969825)
                  ·
                    refine ⟨5294857780326573076477369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7059810373768764101969825 5294857780326573076477369)
                    ·
                      refine ⟨3971143335244929807358027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5294857780326573076477369 3971143335244929807358027)
                      ·
                        rfl

theorem cell23_7733774_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 1, 1, 5, 2, 2].length) (baseStart_7733774 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7733774 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7733774 prefixEnd_7733774 := by exact prefixLift 7733774
  have htrace : WordTrace (prefixWord ++ tailWord_7733774) baseStart_7733774 baseEnd_7733774 := by
    simpa [prefixWord, tailWord_7733774, baseEnd_7733774] using wordTrace_append hprefix tailTrace_7733774
  have hstable : (prefixWord ++ tailWord_7733774).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7733774).length < 2 ^ (prefixWord ++ tailWord_7733774).sum := by decide
  have hdescent : baseEnd_7733774 < baseStart_7733774 := by decide
  rcases family_descends (prefixWord ++ tailWord_7733774) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7733834 : List Nat := [3, 1, 2, 1, 1, 4, 1, 4, 1, 3, 2]
def baseStart_7733834 : Nat := 118140960795 + 7733834 * 2 ^ 59
def prefixEnd_7733834 : Nat := 4983230072969 + 3 ^ 40 * 7733834 * 2
def baseEnd_7733834 : Nat := 3971174144084199572607751

theorem tailTrace_7733834 : CollatzResearch.WordTrace tailWord_7733834 prefixEnd_7733834 3971174144084199572607751 := by
  unfold tailWord_7733834
  simp only [CollatzResearch.WordTrace]
  refine ⟨70519024865911931633842139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 188050732975765151023579037 70519024865911931633842139)
  ·
    refine ⟨105778537298867897450763209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70519024865911931633842139 105778537298867897450763209)
    ·
      refine ⟨79333902974150923088072407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 105778537298867897450763209 79333902974150923088072407)
      ·
        refine ⟨119000854461226384632108611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79333902974150923088072407 119000854461226384632108611)
        ·
          refine ⟨178501281691839576948162917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 119000854461226384632108611 178501281691839576948162917)
          ·
            refine ⟨33468990317219920677780547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 178501281691839576948162917 33468990317219920677780547)
            ·
              refine ⟨50203485475829881016670821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33468990317219920677780547 50203485475829881016670821)
              ·
                refine ⟨9413153526718102690625779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 50203485475829881016670821 9413153526718102690625779)
                ·
                  refine ⟨14119730290077154035938669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9413153526718102690625779 14119730290077154035938669)
                  ·
                    refine ⟨5294898858778932763477001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14119730290077154035938669 5294898858778932763477001)
                    ·
                      refine ⟨3971174144084199572607751, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5294898858778932763477001 3971174144084199572607751)
                      ·
                        rfl

theorem cell23_7733834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 1, 4, 1, 3, 2].length) (baseStart_7733834 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7733834 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7733834 prefixEnd_7733834 := by exact prefixLift 7733834
  have htrace : WordTrace (prefixWord ++ tailWord_7733834) baseStart_7733834 baseEnd_7733834 := by
    simpa [prefixWord, tailWord_7733834, baseEnd_7733834] using wordTrace_append hprefix tailTrace_7733834
  have hstable : (prefixWord ++ tailWord_7733834).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7733834).length < 2 ^ (prefixWord ++ tailWord_7733834).sum := by decide
  have hdescent : baseEnd_7733834 < baseStart_7733834 := by decide
  rcases family_descends (prefixWord ++ tailWord_7733834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7733837 : List Nat := [1, 6, 1, 1, 2, 1, 1, 1, 2, 2, 5]
def baseStart_7733837 : Nat := 118140960795 + 7733837 * 2 ^ 59
def prefixEnd_7733837 : Nat := 4983230072969 + 3 ^ 40 * 7733837 * 2
def baseEnd_7733837 : Nat := 3971175684526163060870237

theorem tailTrace_7733837 : CollatzResearch.WordTrace tailWord_7733837 prefixEnd_7733837 3971175684526163060870237 := by
  unfold tailWord_7733837
  simp only [CollatzResearch.WordTrace]
  refine ⟨282076208882636858047727765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188050805921757905365151843 282076208882636858047727765)
  ·
    refine ⟨13222322291373602720987239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 282076208882636858047727765 13222322291373602720987239)
    ·
      refine ⟨19833483437060404081480859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13222322291373602720987239 19833483437060404081480859)
      ·
        refine ⟨29750225155590606122221289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19833483437060404081480859 29750225155590606122221289)
        ·
          refine ⟨22312668866692954591665967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29750225155590606122221289 22312668866692954591665967)
          ·
            refine ⟨33469003300039431887498951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22312668866692954591665967 33469003300039431887498951)
            ·
              refine ⟨50203504950059147831248427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33469003300039431887498951 50203504950059147831248427)
              ·
                refine ⟨75305257425088721746872641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50203504950059147831248427 75305257425088721746872641)
                ·
                  refine ⟨56478943068816541310154481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 75305257425088721746872641 56478943068816541310154481)
                  ·
                    refine ⟨42359207301612405982615861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 56478943068816541310154481 42359207301612405982615861)
                    ·
                      refine ⟨3971175684526163060870237, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42359207301612405982615861 3971175684526163060870237)
                      ·
                        rfl

theorem cell23_7733837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 1, 1, 2, 2, 5].length) (baseStart_7733837 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7733837 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7733837 prefixEnd_7733837 := by exact prefixLift 7733837
  have htrace : WordTrace (prefixWord ++ tailWord_7733837) baseStart_7733837 baseEnd_7733837 := by
    simpa [prefixWord, tailWord_7733837, baseEnd_7733837] using wordTrace_append hprefix tailTrace_7733837
  have hstable : (prefixWord ++ tailWord_7733837).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7733837).length < 2 ^ (prefixWord ++ tailWord_7733837).sum := by decide
  have hdescent : baseEnd_7733837 < baseStart_7733837 := by decide
  rcases family_descends (prefixWord ++ tailWord_7733837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7733847 : List Nat := [1, 1, 3, 2, 2, 2, 2, 1, 3, 4, 2]
def baseStart_7733847 : Nat := 118140960795 + 7733847 * 2 ^ 59
def prefixEnd_7733847 : Nat := 4983230072969 + 3 ^ 40 * 7733847 * 2
def baseEnd_7733847 : Nat := 3971180819332708021745191

theorem tailTrace_7733847 : CollatzResearch.WordTrace tailWord_7733847 prefixEnd_7733847 3971180819332708021745191 := by
  unfold tailWord_7733847
  simp only [CollatzResearch.WordTrace]
  refine ⟨282076573612600629755591795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188051049075067086503727863 282076573612600629755591795)
  ·
    refine ⟨423114860418900944633387693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 282076573612600629755591795 423114860418900944633387693)
    ·
      refine ⟨158668072657087854237520385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 423114860418900944633387693 158668072657087854237520385)
      ·
        refine ⟨119001054492815890678140289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 158668072657087854237520385 119001054492815890678140289)
        ·
          refine ⟨89250790869611918008605217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 119001054492815890678140289 89250790869611918008605217)
          ·
            refine ⟨66938093152208938506453913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 89250790869611918008605217 66938093152208938506453913)
            ·
              refine ⟨50203569864156703879840435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66938093152208938506453913 50203569864156703879840435)
              ·
                refine ⟨75305354796235055819760653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50203569864156703879840435 75305354796235055819760653)
                ·
                  refine ⟨28239508048588145932410245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 75305354796235055819760653 28239508048588145932410245)
                  ·
                    refine ⟨5294907759110277362326921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28239508048588145932410245 5294907759110277362326921)
                    ·
                      refine ⟨3971180819332708021745191, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5294907759110277362326921 3971180819332708021745191)
                      ·
                        rfl

theorem cell23_7733847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 2, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 2, 1, 3, 4, 2].length) (baseStart_7733847 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7733847 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7733847 prefixEnd_7733847 := by exact prefixLift 7733847
  have htrace : WordTrace (prefixWord ++ tailWord_7733847) baseStart_7733847 baseEnd_7733847 := by
    simpa [prefixWord, tailWord_7733847, baseEnd_7733847] using wordTrace_append hprefix tailTrace_7733847
  have hstable : (prefixWord ++ tailWord_7733847).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7733847).length < 2 ^ (prefixWord ++ tailWord_7733847).sum := by decide
  have hdescent : baseEnd_7733847 < baseStart_7733847 := by decide
  rcases family_descends (prefixWord ++ tailWord_7733847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7733850 : List Nat := [3, 1, 1, 2, 1, 1, 1, 1, 3, 6, 3]
def baseStart_7733850 : Nat := 118140960795 + 7733850 * 2 ^ 59
def prefixEnd_7733850 : Nat := 4983230072969 + 3 ^ 40 * 7733850 * 2
def baseEnd_7733850 : Nat := 3971182359774671510007677

theorem tailTrace_7733850 : CollatzResearch.WordTrace tailWord_7733850 prefixEnd_7733850 3971182359774671510007677 := by
  unfold tailWord_7733850
  simp only [CollatzResearch.WordTrace]
  refine ⟨70519170757897440316987751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 188051122021059840845300669 70519170757897440316987751)
  ·
    refine ⟨105778756136846160475481627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70519170757897440316987751 105778756136846160475481627)
    ·
      refine ⟨158668134205269240713222441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105778756136846160475481627 158668134205269240713222441)
      ·
        refine ⟨119001100653951930534916831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 158668134205269240713222441 119001100653951930534916831)
        ·
          refine ⟨178501650980927895802375247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 119001100653951930534916831 178501650980927895802375247)
          ·
            refine ⟨267752476471391843703562871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 178501650980927895802375247 267752476471391843703562871)
            ·
              refine ⟨401628714707087765555344307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 267752476471391843703562871 401628714707087765555344307)
              ·
                refine ⟨602443072060631648333016461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 401628714707087765555344307 602443072060631648333016461)
                ·
                  refine ⟨225916152022736868124881173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 602443072060631648333016461 225916152022736868124881173)
                  ·
                    refine ⟨10589819626065790693353805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 225916152022736868124881173 10589819626065790693353805)
                    ·
                      refine ⟨3971182359774671510007677, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10589819626065790693353805 3971182359774671510007677)
                      ·
                        rfl

theorem cell23_7733850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 1, 3, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 1, 3, 6, 3].length) (baseStart_7733850 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7733850 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7733850 prefixEnd_7733850 := by exact prefixLift 7733850
  have htrace : WordTrace (prefixWord ++ tailWord_7733850) baseStart_7733850 baseEnd_7733850 := by
    simpa [prefixWord, tailWord_7733850, baseEnd_7733850] using wordTrace_append hprefix tailTrace_7733850
  have hstable : (prefixWord ++ tailWord_7733850).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7733850).length < 2 ^ (prefixWord ++ tailWord_7733850).sum := by decide
  have hdescent : baseEnd_7733850 < baseStart_7733850 := by decide
  rcases family_descends (prefixWord ++ tailWord_7733850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7733881 : List Nat := [1, 2, 1, 3, 3, 3, 1, 3, 2, 2, 2]
def baseStart_7733881 : Nat := 118140960795 + 7733881 * 2 ^ 59
def prefixEnd_7733881 : Nat := 4983230072969 + 3 ^ 40 * 7733881 * 2
def baseEnd_7733881 : Nat := 3971198277674960888720035

theorem tailTrace_7733881 : CollatzResearch.WordTrace tailWord_7733881 prefixEnd_7733881 3971198277674960888720035 := by
  unfold tailWord_7733881
  simp only [CollatzResearch.WordTrace]
  refine ⟨282077813694477453562329497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188051875796318302374886331 282077813694477453562329497)
  ·
    refine ⟨211558360270858090171747123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 282077813694477453562329497 211558360270858090171747123)
    ·
      refine ⟨317337540406287135257620685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 211558360270858090171747123 317337540406287135257620685)
      ·
        refine ⟨119001577652357675721607757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 317337540406287135257620685 119001577652357675721607757)
        ·
          refine ⟨44625591619634128395602909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 119001577652357675721607757 44625591619634128395602909)
          ·
            refine ⟨16734596857362798148351091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44625591619634128395602909 16734596857362798148351091)
            ·
              refine ⟨25101895286044197222526637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16734596857362798148351091 25101895286044197222526637)
              ·
                refine ⟨9413210732266573958447489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25101895286044197222526637 9413210732266573958447489)
                ·
                  refine ⟨7059908049199930468835617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9413210732266573958447489 7059908049199930468835617)
                  ·
                    refine ⟨5294931036899947851626713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7059908049199930468835617 5294931036899947851626713)
                    ·
                      refine ⟨3971198277674960888720035, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5294931036899947851626713 3971198277674960888720035)
                      ·
                        rfl

theorem cell23_7733881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 3, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 3, 1, 3, 2, 2, 2].length) (baseStart_7733881 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7733881 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7733881 prefixEnd_7733881 := by exact prefixLift 7733881
  have htrace : WordTrace (prefixWord ++ tailWord_7733881) baseStart_7733881 baseEnd_7733881 := by
    simpa [prefixWord, tailWord_7733881, baseEnd_7733881] using wordTrace_append hprefix tailTrace_7733881
  have hstable : (prefixWord ++ tailWord_7733881).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7733881).length < 2 ^ (prefixWord ++ tailWord_7733881).sum := by decide
  have hdescent : baseEnd_7733881 < baseStart_7733881 := by decide
  rcases family_descends (prefixWord ++ tailWord_7733881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7733917 : List Nat := [1, 4, 2, 1, 1, 1, 4, 2, 2, 5]
def baseStart_7733917 : Nat := 118140960795 + 7733917 * 2 ^ 59
def prefixEnd_7733917 : Nat := 4983230072969 + 3 ^ 40 * 7733917 * 2
def baseEnd_7733917 : Nat := 1323738920992840915956623

theorem tailTrace_7733917 : CollatzResearch.WordTrace tailWord_7733917 prefixEnd_7733917 1323738920992840915956623 := by
  unfold tailWord_7733917
  simp only [CollatzResearch.WordTrace]
  refine ⟨282079126722347031710640005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188052751148231354473760003 282079126722347031710640005)
  ·
    refine ⟨52889836260440068445745001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 282079126722347031710640005 52889836260440068445745001)
    ·
      refine ⟨39667377195330051334308751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52889836260440068445745001 39667377195330051334308751)
      ·
        refine ⟨59501065792995077001463127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39667377195330051334308751 59501065792995077001463127)
        ·
          refine ⟨89251598689492615502194691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59501065792995077001463127 89251598689492615502194691)
          ·
            refine ⟨133877398034238923253292037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89251598689492615502194691 133877398034238923253292037)
            ·
              refine ⟨25102012131419798109992257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 133877398034238923253292037 25102012131419798109992257)
              ·
                refine ⟨18826509098564848582494193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25102012131419798109992257 18826509098564848582494193)
                ·
                  refine ⟨14119881823923636436870645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18826509098564848582494193 14119881823923636436870645)
                  ·
                    refine ⟨1323738920992840915956623, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14119881823923636436870645 1323738920992840915956623)
                    ·
                      rfl

theorem cell23_7733917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 4, 2, 2, 5].length) (baseStart_7733917 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7733917 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7733917 prefixEnd_7733917 := by exact prefixLift 7733917
  have htrace : WordTrace (prefixWord ++ tailWord_7733917) baseStart_7733917 baseEnd_7733917 := by
    simpa [prefixWord, tailWord_7733917, baseEnd_7733917] using wordTrace_append hprefix tailTrace_7733917
  have hstable : (prefixWord ++ tailWord_7733917).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7733917).length < 2 ^ (prefixWord ++ tailWord_7733917).sum := by decide
  have hdescent : baseEnd_7733917 < baseStart_7733917 := by decide
  rcases family_descends (prefixWord ++ tailWord_7733917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7733997 : List Nat := [1, 5, 1, 2, 1, 1, 1, 2, 1, 2, 6]
def baseStart_7733997 : Nat := 118140960795 + 7733997 * 2 ^ 59
def prefixEnd_7733997 : Nat := 4983230072969 + 3 ^ 40 * 7733997 * 2
def baseEnd_7733997 : Nat := 3971257841430882434869501

theorem tailTrace_7733997 : CollatzResearch.WordTrace tailWord_7733997 prefixEnd_7733997 3971257841430882434869501 := by
  unfold tailWord_7733997
  simp only [CollatzResearch.WordTrace]
  refine ⟨282082044562057205373552245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188054696374704803582368163 282082044562057205373552245)
  ·
    refine ⟨26445191677692863003770523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 282082044562057205373552245 26445191677692863003770523)
    ·
      refine ⟨39667787516539294505655785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26445191677692863003770523 39667787516539294505655785)
      ·
        refine ⟨29750840637404470879241839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39667787516539294505655785 29750840637404470879241839)
        ·
          refine ⟨44626260956106706318862759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29750840637404470879241839 44626260956106706318862759)
          ·
            refine ⟨66939391434160059478294139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44626260956106706318862759 66939391434160059478294139)
            ·
              refine ⟨100409087151240089217441209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66939391434160059478294139 100409087151240089217441209)
              ·
                refine ⟨75306815363430066913080907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 100409087151240089217441209 75306815363430066913080907)
                ·
                  refine ⟨112960223045145100369621361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 75306815363430066913080907 112960223045145100369621361)
                  ·
                    refine ⟨84720167283858825277216021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 112960223045145100369621361 84720167283858825277216021)
                    ·
                      refine ⟨3971257841430882434869501, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 84720167283858825277216021 3971257841430882434869501)
                      ·
                        rfl

theorem cell23_7733997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 1, 2, 1, 2, 6].length) (baseStart_7733997 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7733997 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7733997 prefixEnd_7733997 := by exact prefixLift 7733997
  have htrace : WordTrace (prefixWord ++ tailWord_7733997) baseStart_7733997 baseEnd_7733997 := by
    simpa [prefixWord, tailWord_7733997, baseEnd_7733997] using wordTrace_append hprefix tailTrace_7733997
  have hstable : (prefixWord ++ tailWord_7733997).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7733997).length < 2 ^ (prefixWord ++ tailWord_7733997).sum := by decide
  have hdescent : baseEnd_7733997 < baseStart_7733997 := by decide
  rcases family_descends (prefixWord ++ tailWord_7733997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7734024 : List Nat := [2, 1, 3, 2, 2, 2, 2, 3, 1, 5]
def baseStart_7734024 : Nat := 118140960795 + 7734024 * 2 ^ 59
def prefixEnd_7734024 : Nat := 4983230072969 + 3 ^ 40 * 7734024 * 2
def baseEnd_7734024 : Nat := 1323757235136184609743959

theorem tailTrace_7734024 : CollatzResearch.WordTrace tailWord_7734024 prefixEnd_7734024 1323757235136184609743959 := by
  unfold tailWord_7734024
  simp only [CollatzResearch.WordTrace]
  refine ⟨141041514666479694492392563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 188055352888639592656523417 141041514666479694492392563)
  ·
    refine ⟨211562271999719541738588845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141041514666479694492392563 211562271999719541738588845)
    ·
      refine ⟨79335851999894828151970817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 211562271999719541738588845 79335851999894828151970817)
      ·
        refine ⟨59501888999921121113978113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79335851999894828151970817 59501888999921121113978113)
        ·
          refine ⟨44626416749940840835483585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59501888999921121113978113 44626416749940840835483585)
          ·
            refine ⟨33469812562455630626612689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44626416749940840835483585 33469812562455630626612689)
            ·
              refine ⟨25102359421841722969959517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33469812562455630626612689 25102359421841722969959517)
              ·
                refine ⟨9413384783190646113734819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25102359421841722969959517 9413384783190646113734819)
                ·
                  refine ⟨14120077174785969170602229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9413384783190646113734819 14120077174785969170602229)
                  ·
                    refine ⟨1323757235136184609743959, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14120077174785969170602229 1323757235136184609743959)
                    ·
                      rfl

theorem cell23_7734024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 2, 3, 1, 5].length) (baseStart_7734024 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7734024 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7734024 prefixEnd_7734024 := by exact prefixLift 7734024
  have htrace : WordTrace (prefixWord ++ tailWord_7734024) baseStart_7734024 baseEnd_7734024 := by
    simpa [prefixWord, tailWord_7734024, baseEnd_7734024] using wordTrace_append hprefix tailTrace_7734024
  have hstable : (prefixWord ++ tailWord_7734024).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7734024).length < 2 ^ (prefixWord ++ tailWord_7734024).sum := by decide
  have hdescent : baseEnd_7734024 < baseStart_7734024 := by decide
  rcases family_descends (prefixWord ++ tailWord_7734024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7734027 : List Nat := [1, 1, 1, 1, 5, 1, 1, 2, 5, 1, 4]
def baseStart_7734027 : Nat := 118140960795 + 7734027 * 2 ^ 59
def prefixEnd_7734027 : Nat := 4983230072969 + 3 ^ 40 * 7734027 * 2
def baseEnd_7734027 : Nat := 3971273245850517317494363

theorem tailTrace_7734027 : CollatzResearch.WordTrace tailWord_7734027 prefixEnd_7734027 3971273245850517317494363 := by
  unfold tailWord_7734027
  simp only [CollatzResearch.WordTrace]
  refine ⟨282083138751948520497144335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188055425834632346998096223 282083138751948520497144335)
  ·
    refine ⟨423124708127922780745716503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 282083138751948520497144335 423124708127922780745716503)
    ·
      refine ⟨634687062191884171118574755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 423124708127922780745716503 634687062191884171118574755)
      ·
        refine ⟨952030593287826256677862133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 634687062191884171118574755 952030593287826256677862133)
        ·
          refine ⟨89252868120733711563549575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 952030593287826256677862133 89252868120733711563549575)
          ·
            refine ⟨133879302181100567345324363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89252868120733711563549575 133879302181100567345324363)
            ·
              refine ⟨200818953271650851017986545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 133879302181100567345324363 200818953271650851017986545)
              ·
                refine ⟨150614214953738138263489909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 200818953271650851017986545 150614214953738138263489909)
                ·
                  refine ⟨14120082651912950462202179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 150614214953738138263489909 14120082651912950462202179)
                  ·
                    refine ⟨21180123977869425693303269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14120082651912950462202179 21180123977869425693303269)
                    ·
                      refine ⟨3971273245850517317494363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21180123977869425693303269 3971273245850517317494363)
                      ·
                        rfl

theorem cell23_7734027_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 1, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 1, 2, 5, 1, 4].length) (baseStart_7734027 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7734027 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7734027 prefixEnd_7734027 := by exact prefixLift 7734027
  have htrace : WordTrace (prefixWord ++ tailWord_7734027) baseStart_7734027 baseEnd_7734027 := by
    simpa [prefixWord, tailWord_7734027, baseEnd_7734027] using wordTrace_append hprefix tailTrace_7734027
  have hstable : (prefixWord ++ tailWord_7734027).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7734027).length < 2 ^ (prefixWord ++ tailWord_7734027).sum := by decide
  have hdescent : baseEnd_7734027 < baseStart_7734027 := by decide
  rcases family_descends (prefixWord ++ tailWord_7734027) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7734045 : List Nat := [1, 4, 2, 4, 2, 1, 2, 1, 6]
def baseStart_7734045 : Nat := 118140960795 + 7734045 * 2 ^ 59
def prefixEnd_7734045 : Nat := 4983230072969 + 3 ^ 40 * 7734045 * 2
def baseEnd_7734045 : Nat := 441253609833588694118809

theorem tailTrace_7734045 : CollatzResearch.WordTrace tailWord_7734045 prefixEnd_7734045 441253609833588694118809 := by
  unfold tailWord_7734045
  simp only [CollatzResearch.WordTrace]
  refine ⟨282083795265883309571299589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188055863510588873047533059 282083795265883309571299589)
  ·
    refine ⟨52890711612353120544618673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 282083795265883309571299589 52890711612353120544618673)
    ·
      refine ⟨39668033709264840408464005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52890711612353120544618673 39668033709264840408464005)
      ·
        refine ⟨7437756320487157576587001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 39668033709264840408464005 7437756320487157576587001)
        ·
          refine ⟨5578317240365368182440251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7437756320487157576587001 5578317240365368182440251)
          ·
            refine ⟨8367475860548052273660377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5578317240365368182440251 8367475860548052273660377)
            ·
              refine ⟨6275606895411039205245283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8367475860548052273660377 6275606895411039205245283)
              ·
                refine ⟨9413410343116558807867925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6275606895411039205245283 9413410343116558807867925)
                ·
                  refine ⟨441253609833588694118809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9413410343116558807867925 441253609833588694118809)
                  ·
                    rfl

theorem cell23_7734045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 2, 1, 2, 1, 6].length) (baseStart_7734045 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7734045 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7734045 prefixEnd_7734045 := by exact prefixLift 7734045
  have htrace : WordTrace (prefixWord ++ tailWord_7734045) baseStart_7734045 baseEnd_7734045 := by
    simpa [prefixWord, tailWord_7734045, baseEnd_7734045] using wordTrace_append hprefix tailTrace_7734045
  have hstable : (prefixWord ++ tailWord_7734045).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7734045).length < 2 ^ (prefixWord ++ tailWord_7734045).sum := by decide
  have hdescent : baseEnd_7734045 < baseStart_7734045 := by decide
  rcases family_descends (prefixWord ++ tailWord_7734045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7734067 : List Nat := [1, 1, 1, 2, 6, 1, 2, 9]
def baseStart_7734067 : Nat := 118140960795 + 7734067 * 2 ^ 59
def prefixEnd_7734067 : Nat := 4983230072969 + 3 ^ 40 * 7734067 * 2
def baseEnd_7734067 : Nat := 147084955002840635592377

theorem tailTrace_7734067 : CollatzResearch.WordTrace tailWord_7734067 prefixEnd_7734067 147084955002840635592377 := by
  unfold tailWord_7734067
  simp only [CollatzResearch.WordTrace]
  refine ⟨282084597671803607328600455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188056398447869071552400303 282084597671803607328600455)
  ·
    refine ⟨423126896507705410992900683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 282084597671803607328600455 423126896507705410992900683)
    ·
      refine ⟨634690344761558116489351025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 423126896507705410992900683 634690344761558116489351025)
      ·
        refine ⟨476017758571168587367013269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 634690344761558116489351025 476017758571168587367013269)
        ·
          refine ⟨22313332433023527532828747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 476017758571168587367013269 22313332433023527532828747)
          ·
            refine ⟨33469998649535291299243121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22313332433023527532828747 33469998649535291299243121)
            ·
              refine ⟨25102498987151468474432341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33469998649535291299243121 25102498987151468474432341)
              ·
                refine ⟨147084955002840635592377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 25102498987151468474432341 147084955002840635592377)
                ·
                  rfl

theorem cell23_7734067_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 2, 9].length) (baseStart_7734067 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7734067 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7734067 prefixEnd_7734067 := by exact prefixLift 7734067
  have htrace : WordTrace (prefixWord ++ tailWord_7734067) baseStart_7734067 baseEnd_7734067 := by
    simpa [prefixWord, tailWord_7734067, baseEnd_7734067] using wordTrace_append hprefix tailTrace_7734067
  have hstable : (prefixWord ++ tailWord_7734067).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7734067).length < 2 ^ (prefixWord ++ tailWord_7734067).sum := by decide
  have hdescent : baseEnd_7734067 < baseStart_7734067 := by decide
  rcases family_descends (prefixWord ++ tailWord_7734067) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7734084 : List Nat := [2, 3, 4, 2, 12]
def baseStart_7734084 : Nat := 118140960795 + 7734084 * 2 ^ 59
def prefixEnd_7734084 : Nat := 4983230072969 + 3 ^ 40 * 7734084 * 2
def baseEnd_7734084 : Nat := 5447602900202775849769

theorem tailTrace_7734084 : CollatzResearch.WordTrace tailWord_7734084 prefixEnd_7734084 5447602900202775849769 := by
  unfold tailWord_7734084
  simp only [CollatzResearch.WordTrace]
  refine ⟨141042608856371009615984653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 188056811808494679487979537 141042608856371009615984653)
  ·
    refine ⟨52890978321139128605994245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 141042608856371009615984653 52890978321139128605994245)
    ·
      refine ⟨9917058435213586613623921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 52890978321139128605994245 9917058435213586613623921)
      ·
        refine ⟨7437793826410189960217941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9917058435213586613623921 7437793826410189960217941)
        ·
          refine ⟨5447602900202775849769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 12 7437793826410189960217941 5447602900202775849769)
          ·
            rfl

theorem cell23_7734084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 12].length) (baseStart_7734084 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7734084 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7734084 prefixEnd_7734084 := by exact prefixLift 7734084
  have htrace : WordTrace (prefixWord ++ tailWord_7734084) baseStart_7734084 baseEnd_7734084 := by
    simpa [prefixWord, tailWord_7734084, baseEnd_7734084] using wordTrace_append hprefix tailTrace_7734084
  have hstable : (prefixWord ++ tailWord_7734084).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7734084).length < 2 ^ (prefixWord ++ tailWord_7734084).sum := by decide
  have hdescent : baseEnd_7734084 < baseStart_7734084 := by decide
  rcases family_descends (prefixWord ++ tailWord_7734084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7734111 : List Nat := [1, 1, 2, 3, 1, 3, 1, 5, 2, 1, 3]
def baseStart_7734111 : Nat := 118140960795 + 7734111 * 2 ^ 59
def prefixEnd_7734111 : Nat := 4983230072969 + 3 ^ 40 * 7734111 * 2
def baseEnd_7734111 : Nat := 3971316378225494988843977

theorem tailTrace_7734111 : CollatzResearch.WordTrace tailWord_7734111 prefixEnd_7734111 3971316378225494988843977 := by
  unfold tailWord_7734111
  simp only [CollatzResearch.WordTrace]
  refine ⟨282086202483644202843202187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188057468322429468562134791 282086202483644202843202187)
  ·
    refine ⟨423129303725466304264803281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 282086202483644202843202187 423129303725466304264803281)
    ·
      refine ⟨317346977794099728198602461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 423129303725466304264803281 317346977794099728198602461)
      ·
        refine ⟨119005116672787398074475923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 317346977794099728198602461 119005116672787398074475923)
        ·
          refine ⟨178507675009181097111713885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 119005116672787398074475923 178507675009181097111713885)
          ·
            refine ⟨66940378128442911416892707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 178507675009181097111713885 66940378128442911416892707)
            ·
              refine ⟨100410567192664367125339061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66940378128442911416892707 100410567192664367125339061)
              ·
                refine ⟨9413490674312284418000537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 100410567192664367125339061 9413490674312284418000537)
                ·
                  refine ⟨7060118005734213313500403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9413490674312284418000537 7060118005734213313500403)
                  ·
                    refine ⟨10590177008601319970250605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7060118005734213313500403 10590177008601319970250605)
                    ·
                      refine ⟨3971316378225494988843977, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10590177008601319970250605 3971316378225494988843977)
                      ·
                        rfl

theorem cell23_7734111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 1, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 1, 5, 2, 1, 3].length) (baseStart_7734111 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7734111 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7734111 prefixEnd_7734111 := by exact prefixLift 7734111
  have htrace : WordTrace (prefixWord ++ tailWord_7734111) baseStart_7734111 baseEnd_7734111 := by
    simpa [prefixWord, tailWord_7734111, baseEnd_7734111] using wordTrace_append hprefix tailTrace_7734111
  have hstable : (prefixWord ++ tailWord_7734111).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7734111).length < 2 ^ (prefixWord ++ tailWord_7734111).sum := by decide
  have hdescent : baseEnd_7734111 < baseStart_7734111 := by decide
  rcases family_descends (prefixWord ++ tailWord_7734111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7734162 : List Nat := [3, 2, 3, 2, 2, 1, 3, 1, 2, 1, 3]
def baseStart_7734162 : Nat := 118140960795 + 7734162 * 2 ^ 59
def prefixEnd_7734162 : Nat := 4983230072969 + 3 ^ 40 * 7734162 * 2
def baseEnd_7734162 : Nat := 3971342565738874289306243

theorem tailTrace_7734162 : CollatzResearch.WordTrace tailWord_7734162 prefixEnd_7734162 3971342565738874289306243 := by
  unfold tailWord_7734162
  simp only [CollatzResearch.WordTrace]
  refine ⟨70522015651614859638327185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 188058708404306292368872493 70522015651614859638327185)
  ·
    refine ⟨52891511738711144728745389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70522015651614859638327185 52891511738711144728745389)
    ·
      refine ⟨19834316902016679273279521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 52891511738711144728745389 19834316902016679273279521)
      ·
        refine ⟨14875737676512509454959641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19834316902016679273279521 14875737676512509454959641)
        ·
          refine ⟨11156803257384382091219731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14875737676512509454959641 11156803257384382091219731)
          ·
            refine ⟨16735204886076573136829597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11156803257384382091219731 16735204886076573136829597)
            ·
              refine ⟨6275701832278714926311099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16735204886076573136829597 6275701832278714926311099)
              ·
                refine ⟨9413552748418072389466649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6275701832278714926311099 9413552748418072389466649)
                ·
                  refine ⟨7060164561313554292099987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9413552748418072389466649 7060164561313554292099987)
                  ·
                    refine ⟨10590246841970331438149981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7060164561313554292099987 10590246841970331438149981)
                    ·
                      refine ⟨3971342565738874289306243, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10590246841970331438149981 3971342565738874289306243)
                      ·
                        rfl

theorem cell23_7734162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 2, 1, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 2, 1, 3, 1, 2, 1, 3].length) (baseStart_7734162 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7734162 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7734162 prefixEnd_7734162 := by exact prefixLift 7734162
  have htrace : WordTrace (prefixWord ++ tailWord_7734162) baseStart_7734162 baseEnd_7734162 := by
    simpa [prefixWord, tailWord_7734162, baseEnd_7734162] using wordTrace_append hprefix tailTrace_7734162
  have hstable : (prefixWord ++ tailWord_7734162).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7734162).length < 2 ^ (prefixWord ++ tailWord_7734162).sum := by decide
  have hdescent : baseEnd_7734162 < baseStart_7734162 := by decide
  rcases family_descends (prefixWord ++ tailWord_7734162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7734208 : List Nat := [2, 1, 1, 2, 3, 4, 3, 2, 5]
def baseStart_7734208 : Nat := 118140960795 + 7734208 * 2 ^ 59
def prefixEnd_7734208 : Nat := 4983230072969 + 3 ^ 40 * 7734208 * 2
def baseEnd_7734208 : Nat := 441262909538775678814559

theorem tailTrace_7734208 : CollatzResearch.WordTrace tailWord_7734208 prefixEnd_7734208 441262909538775678814559 := by
  unfold tailWord_7734208
  simp only [CollatzResearch.WordTrace]
  refine ⟨141044870182146394204741639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 188059826909528525606322185 141044870182146394204741639)
  ·
    refine ⟨211567305273219591307112459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141044870182146394204741639 211567305273219591307112459)
    ·
      refine ⟨317350957909829386960668689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 211567305273219591307112459 317350957909829386960668689)
      ·
        refine ⟨238013218432372040220501517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 317350957909829386960668689 238013218432372040220501517)
        ·
          refine ⟨89254956912139515082688069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 238013218432372040220501517 89254956912139515082688069)
          ·
            refine ⟨16735304421026159078004013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 89254956912139515082688069 16735304421026159078004013)
            ·
              refine ⟨6275739157884809654251505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16735304421026159078004013 6275739157884809654251505)
              ·
                refine ⟨4706804368413607240688629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6275739157884809654251505 4706804368413607240688629)
                ·
                  refine ⟨441262909538775678814559, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4706804368413607240688629 441262909538775678814559)
                  ·
                    rfl

theorem cell23_7734208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 4, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 4, 3, 2, 5].length) (baseStart_7734208 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7734208 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7734208 prefixEnd_7734208 := by exact prefixLift 7734208
  have htrace : WordTrace (prefixWord ++ tailWord_7734208) baseStart_7734208 baseEnd_7734208 := by
    simpa [prefixWord, tailWord_7734208, baseEnd_7734208] using wordTrace_append hprefix tailTrace_7734208
  have hstable : (prefixWord ++ tailWord_7734208).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7734208).length < 2 ^ (prefixWord ++ tailWord_7734208).sum := by decide
  have hdescent : baseEnd_7734208 < baseStart_7734208 := by decide
  rcases family_descends (prefixWord ++ tailWord_7734208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7734224 : List Nat := [2, 1, 1, 1, 1, 2, 3, 1, 6, 1, 4]
def baseStart_7734224 : Nat := 118140960795 + 7734224 * 2 ^ 59
def prefixEnd_7734224 : Nat := 4983230072969 + 3 ^ 40 * 7734224 * 2
def baseEnd_7734224 : Nat := 3971374401539453046730957

theorem tailTrace_7734224 : CollatzResearch.WordTrace tailWord_7734224 prefixEnd_7734224 3971374401539453046730957 := by
  unfold tailWord_7734224
  simp only [CollatzResearch.WordTrace]
  refine ⟨141045161966117411571032863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 188060215954823215428043817 141045161966117411571032863)
  ·
    refine ⟨211567742949176117356549295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141045161966117411571032863 211567742949176117356549295)
    ·
      refine ⟨317351614423764176034823943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 211567742949176117356549295 317351614423764176034823943)
      ·
        refine ⟨476027421635646264052235915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 317351614423764176034823943 476027421635646264052235915)
        ·
          refine ⟨714041132453469396078353873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 476027421635646264052235915 714041132453469396078353873)
          ·
            refine ⟨535530849340102047058765405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 714041132453469396078353873 535530849340102047058765405)
            ·
              refine ⟨200824068502538267647037027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 535530849340102047058765405 200824068502538267647037027)
              ·
                refine ⟨301236102753807401470555541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 200824068502538267647037027 301236102753807401470555541)
                ·
                  refine ⟨14120442316584721943932291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 301236102753807401470555541 14120442316584721943932291)
                  ·
                    refine ⟨21180663474877082915898437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14120442316584721943932291 21180663474877082915898437)
                    ·
                      refine ⟨3971374401539453046730957, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21180663474877082915898437 3971374401539453046730957)
                      ·
                        rfl

theorem cell23_7734224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 3, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 3, 1, 6, 1, 4].length) (baseStart_7734224 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7734224 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7734224 prefixEnd_7734224 := by exact prefixLift 7734224
  have htrace : WordTrace (prefixWord ++ tailWord_7734224) baseStart_7734224 baseEnd_7734224 := by
    simpa [prefixWord, tailWord_7734224, baseEnd_7734224] using wordTrace_append hprefix tailTrace_7734224
  have hstable : (prefixWord ++ tailWord_7734224).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7734224).length < 2 ^ (prefixWord ++ tailWord_7734224).sum := by decide
  have hdescent : baseEnd_7734224 < baseStart_7734224 := by decide
  rcases family_descends (prefixWord ++ tailWord_7734224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7734241 : List Nat := [1, 2, 3, 1, 2, 1, 1, 2, 4, 4, 2]
def baseStart_7734241 : Nat := 118140960795 + 7734241 * 2 ^ 59
def prefixEnd_7734241 : Nat := 4983230072969 + 3 ^ 40 * 7734241 * 2
def baseEnd_7734241 : Nat := 3971383130710579480218379

theorem tailTrace_7734241 : CollatzResearch.WordTrace tailWord_7734241 prefixEnd_7734241 3971383130710579480218379 := by
  unfold tailWord_7734241
  simp only [CollatzResearch.WordTrace]
  refine ⟨282090943973173235045434577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188060629315448823363623051 282090943973173235045434577)
  ·
    refine ⟨211568207979879926284075933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 282090943973173235045434577 211568207979879926284075933)
    ·
      refine ⟨79338077992454972356528475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 211568207979879926284075933 79338077992454972356528475)
      ·
        refine ⟨119007116988682458534792713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79338077992454972356528475 119007116988682458534792713)
        ·
          refine ⟨89255337741511843901094535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 119007116988682458534792713 89255337741511843901094535)
          ·
            refine ⟨133883006612267765851641803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89255337741511843901094535 133883006612267765851641803)
            ·
              refine ⟨200824509918401648777462705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 133883006612267765851641803 200824509918401648777462705)
              ·
                refine ⟨150618382438801236583097029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 200824509918401648777462705 150618382438801236583097029)
                ·
                  refine ⟨28240946707275231859330693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 150618382438801236583097029 28240946707275231859330693)
                  ·
                    refine ⟨5295177507614105973624505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28240946707275231859330693 5295177507614105973624505)
                    ·
                      refine ⟨3971383130710579480218379, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5295177507614105973624505 3971383130710579480218379)
                      ·
                        rfl

theorem cell23_7734241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 1, 2, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 1, 2, 4, 4, 2].length) (baseStart_7734241 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7734241 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7734241 prefixEnd_7734241 := by exact prefixLift 7734241
  have htrace : WordTrace (prefixWord ++ tailWord_7734241) baseStart_7734241 baseEnd_7734241 := by
    simpa [prefixWord, tailWord_7734241, baseEnd_7734241] using wordTrace_append hprefix tailTrace_7734241
  have hstable : (prefixWord ++ tailWord_7734241).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7734241).length < 2 ^ (prefixWord ++ tailWord_7734241).sum := by decide
  have hdescent : baseEnd_7734241 < baseStart_7734241 := by decide
  rcases family_descends (prefixWord ++ tailWord_7734241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7734295 : List Nat := [1, 1, 3, 5, 1, 3, 1, 1, 2, 2, 3]
def baseStart_7734295 : Nat := 118140960795 + 7734295 * 2 ^ 59
def prefixEnd_7734295 : Nat := 4983230072969 + 3 ^ 40 * 7734295 * 2
def baseEnd_7734295 : Nat := 3971410858665922268943131

theorem tailTrace_7734295 : CollatzResearch.WordTrace tailWord_7734295 prefixEnd_7734295 3971410858665922268943131 := by
  unfold tailWord_7734295
  simp only [CollatzResearch.WordTrace]
  refine ⟨282092913514977602267900339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188061942343318401511933559 282092913514977602267900339)
  ·
    refine ⟨423139370272466403401850509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 282092913514977602267900339 423139370272466403401850509)
    ·
      refine ⟨158677263852174901275693941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 423139370272466403401850509 158677263852174901275693941)
      ·
        refine ⟨14875993486141396994596307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 158677263852174901275693941 14875993486141396994596307)
        ·
          refine ⟨22313990229212095491894461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14875993486141396994596307 22313990229212095491894461)
          ·
            refine ⟨8367746335954535809460423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22313990229212095491894461 8367746335954535809460423)
            ·
              refine ⟨12551619503931803714190635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8367746335954535809460423 12551619503931803714190635)
              ·
                refine ⟨18827429255897705571285953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12551619503931803714190635 18827429255897705571285953)
                ·
                  refine ⟨14120571941923279178464465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18827429255897705571285953 14120571941923279178464465)
                  ·
                    refine ⟨10590428956442459383848349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14120571941923279178464465 10590428956442459383848349)
                    ·
                      refine ⟨3971410858665922268943131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10590428956442459383848349 3971410858665922268943131)
                      ·
                        rfl

theorem cell23_7734295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 3, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 3, 1, 1, 2, 2, 3].length) (baseStart_7734295 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7734295 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7734295 prefixEnd_7734295 := by exact prefixLift 7734295
  have htrace : WordTrace (prefixWord ++ tailWord_7734295) baseStart_7734295 baseEnd_7734295 := by
    simpa [prefixWord, tailWord_7734295, baseEnd_7734295] using wordTrace_append hprefix tailTrace_7734295
  have hstable : (prefixWord ++ tailWord_7734295).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7734295).length < 2 ^ (prefixWord ++ tailWord_7734295).sum := by decide
  have hdescent : baseEnd_7734295 < baseStart_7734295 := by decide
  rcases family_descends (prefixWord ++ tailWord_7734295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7734331 : List Nat := [1, 1, 1, 1, 1, 2, 1, 3, 4, 6, 2]
def baseStart_7734331 : Nat := 118140960795 + 7734331 * 2 ^ 59
def prefixEnd_7734331 : Nat := 4983230072969 + 3 ^ 40 * 7734331 * 2
def baseEnd_7734331 : Nat := 3971429343969484128092965

theorem tailTrace_7734331 : CollatzResearch.WordTrace tailWord_7734331 prefixEnd_7734331 3971429343969484128092965 := by
  unfold tailWord_7734331
  simp only [CollatzResearch.WordTrace]
  refine ⟨282094226542847180416210847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188062817695231453610807231 282094226542847180416210847)
  ·
    refine ⟨423141339814270770624316271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 282094226542847180416210847 423141339814270770624316271)
    ·
      refine ⟨634712009721406155936474407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 423141339814270770624316271 634712009721406155936474407)
      ·
        refine ⟨952068014582109233904711611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 634712009721406155936474407 952068014582109233904711611)
        ·
          refine ⟨1428102021873163850857067417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 952068014582109233904711611 1428102021873163850857067417)
          ·
            refine ⟨1071076516404872888142800563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1428102021873163850857067417 1071076516404872888142800563)
            ·
              refine ⟨1606614774607309332214200845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1071076516404872888142800563 1606614774607309332214200845)
              ·
                refine ⟨602480540477740999580325317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1606614774607309332214200845 602480540477740999580325317)
                ·
                  refine ⟨112965101339576437421310997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 602480540477740999580325317 112965101339576437421310997)
                  ·
                    refine ⟨5295239125292645504123953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 112965101339576437421310997 5295239125292645504123953)
                    ·
                      refine ⟨3971429343969484128092965, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5295239125292645504123953 3971429343969484128092965)
                      ·
                        rfl

theorem cell23_7734331_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 3, 4, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 3, 4, 6, 2].length) (baseStart_7734331 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7734331 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7734331 prefixEnd_7734331 := by exact prefixLift 7734331
  have htrace : WordTrace (prefixWord ++ tailWord_7734331) baseStart_7734331 baseEnd_7734331 := by
    simpa [prefixWord, tailWord_7734331, baseEnd_7734331] using wordTrace_append hprefix tailTrace_7734331
  have hstable : (prefixWord ++ tailWord_7734331).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7734331).length < 2 ^ (prefixWord ++ tailWord_7734331).sum := by decide
  have hdescent : baseEnd_7734331 < baseStart_7734331 := by decide
  rcases family_descends (prefixWord ++ tailWord_7734331) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7734341 : List Nat := [1, 3, 1, 1, 1, 3, 5, 1, 1, 6]
def baseStart_7734341 : Nat := 118140960795 + 7734341 * 2 ^ 59
def prefixEnd_7734341 : Nat := 4983230072969 + 3 ^ 40 * 7734341 * 2
def baseEnd_7734341 : Nat := 1323811492925343029655973

theorem tailTrace_7734341 : CollatzResearch.WordTrace tailWord_7734341 prefixEnd_7734341 1323811492925343029655973 := by
  unfold tailWord_7734341
  simp only [CollatzResearch.WordTrace]
  refine ⟨282094591272810952124074877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188063060848540634749383251 282094591272810952124074877)
  ·
    refine ⟨105785471727304107046528079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 282094591272810952124074877 105785471727304107046528079)
    ·
      refine ⟨158678207590956160569792119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105785471727304107046528079 158678207590956160569792119)
      ·
        refine ⟨238017311386434240854688179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 158678207590956160569792119 238017311386434240854688179)
        ·
          refine ⟨357025967079651361282032269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 238017311386434240854688179 357025967079651361282032269)
          ·
            refine ⟨133884737654869260480762101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 357025967079651361282032269 133884737654869260480762101)
            ·
              refine ⟨12551694155143993170071447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 133884737654869260480762101 12551694155143993170071447)
              ·
                refine ⟨18827541232715989755107171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12551694155143993170071447 18827541232715989755107171)
                ·
                  refine ⟨28241311849073984632660757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18827541232715989755107171 28241311849073984632660757)
                  ·
                    refine ⟨1323811492925343029655973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28241311849073984632660757 1323811492925343029655973)
                    ·
                      rfl

theorem cell23_7734341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 5, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 5, 1, 1, 6].length) (baseStart_7734341 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7734341 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7734341 prefixEnd_7734341 := by exact prefixLift 7734341
  have htrace : WordTrace (prefixWord ++ tailWord_7734341) baseStart_7734341 baseEnd_7734341 := by
    simpa [prefixWord, tailWord_7734341, baseEnd_7734341] using wordTrace_append hprefix tailTrace_7734341
  have hstable : (prefixWord ++ tailWord_7734341).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7734341).length < 2 ^ (prefixWord ++ tailWord_7734341).sum := by decide
  have hdescent : baseEnd_7734341 < baseStart_7734341 := by decide
  rcases family_descends (prefixWord ++ tailWord_7734341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7734342 : List Nat := [6, 1, 1, 1, 1, 2, 2, 2, 3, 1, 3]
def baseStart_7734342 : Nat := 118140960795 + 7734342 * 2 ^ 59
def prefixEnd_7734342 : Nat := 4983230072969 + 3 ^ 40 * 7734342 * 2
def baseEnd_7734342 : Nat := 3971434992256683585055415

theorem tailTrace_7734342 : CollatzResearch.WordTrace tailWord_7734342 prefixEnd_7734342 3971434992256683585055415 := by
  unfold tailWord_7734342
  simp only [CollatzResearch.WordTrace]
  refine ⟨8815457117056479040464415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 188063085163871552863240853 8815457117056479040464415)
  ·
    refine ⟨13223185675584718560696623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8815457117056479040464415 13223185675584718560696623)
    ·
      refine ⟨19834778513377077841044935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13223185675584718560696623 19834778513377077841044935)
      ·
        refine ⟨29752167770065616761567403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19834778513377077841044935 29752167770065616761567403)
        ·
          refine ⟨44628251655098425142351105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29752167770065616761567403 44628251655098425142351105)
          ·
            refine ⟨33471188741323818856763329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44628251655098425142351105 33471188741323818856763329)
            ·
              refine ⟨25103391555992864142572497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33471188741323818856763329 25103391555992864142572497)
              ·
                refine ⟨18827543666994648106929373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25103391555992864142572497 18827543666994648106929373)
                ·
                  refine ⟨7060328875122993040098515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18827543666994648106929373 7060328875122993040098515)
                  ·
                    refine ⟨10590493312684489560147773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7060328875122993040098515 10590493312684489560147773)
                    ·
                      refine ⟨3971434992256683585055415, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10590493312684489560147773 3971434992256683585055415)
                      ·
                        rfl

theorem cell23_7734342_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 2, 2, 3, 1, 3].length) (baseStart_7734342 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7734342 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7734342 prefixEnd_7734342 := by exact prefixLift 7734342
  have htrace : WordTrace (prefixWord ++ tailWord_7734342) baseStart_7734342 baseEnd_7734342 := by
    simpa [prefixWord, tailWord_7734342, baseEnd_7734342] using wordTrace_append hprefix tailTrace_7734342
  have hstable : (prefixWord ++ tailWord_7734342).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7734342).length < 2 ^ (prefixWord ++ tailWord_7734342).sum := by decide
  have hdescent : baseEnd_7734342 < baseStart_7734342 := by decide
  rcases family_descends (prefixWord ++ tailWord_7734342) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7734368 : List Nat := [2, 1, 1, 3, 2, 2, 1, 5, 1, 2, 3]
def baseStart_7734368 : Nat := 118140960795 + 7734368 * 2 ^ 59
def prefixEnd_7734368 : Nat := 4983230072969 + 3 ^ 40 * 7734368 * 2
def baseEnd_7734368 : Nat := 3971448342753700483330295

theorem tailTrace_7734368 : CollatzResearch.WordTrace tailWord_7734368 prefixEnd_7734368 3971448342753700483330295 := by
  unfold tailWord_7734368
  simp only [CollatzResearch.WordTrace]
  refine ⟨141047788021856567867653879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 188063717362475423823538505 141047788021856567867653879)
  ·
    refine ⟨211571682032784851801480819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141047788021856567867653879 211571682032784851801480819)
    ·
      refine ⟨317357523049177277702221229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 211571682032784851801480819 317357523049177277702221229)
      ·
        refine ⟨119009071143441479138332961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 317357523049177277702221229 119009071143441479138332961)
        ·
          refine ⟨89256803357581109353749721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 119009071143441479138332961 89256803357581109353749721)
          ·
            refine ⟨66942602518185832015312291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 89256803357581109353749721 66942602518185832015312291)
            ·
              refine ⟨100413903777278748022968437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66942602518185832015312291 100413903777278748022968437)
              ·
                refine ⟨9413803479119882627153291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 100413903777278748022968437 9413803479119882627153291)
                ·
                  refine ⟨14120705218679823940729937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9413803479119882627153291 14120705218679823940729937)
                  ·
                    refine ⟨10590528914009867955547453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14120705218679823940729937 10590528914009867955547453)
                    ·
                      refine ⟨3971448342753700483330295, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10590528914009867955547453 3971448342753700483330295)
                      ·
                        rfl

theorem cell23_7734368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 1, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 1, 5, 1, 2, 3].length) (baseStart_7734368 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7734368 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7734368 prefixEnd_7734368 := by exact prefixLift 7734368
  have htrace : WordTrace (prefixWord ++ tailWord_7734368) baseStart_7734368 baseEnd_7734368 := by
    simpa [prefixWord, tailWord_7734368, baseEnd_7734368] using wordTrace_append hprefix tailTrace_7734368
  have hstable : (prefixWord ++ tailWord_7734368).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7734368).length < 2 ^ (prefixWord ++ tailWord_7734368).sum := by decide
  have hdescent : baseEnd_7734368 < baseStart_7734368 := by decide
  rcases family_descends (prefixWord ++ tailWord_7734368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7734376 : List Nat := [2, 1, 4, 4, 1, 1, 3, 2, 1, 1, 3]
def baseStart_7734376 : Nat := 118140960795 + 7734376 * 2 ^ 59
def prefixEnd_7734376 : Nat := 4983230072969 + 3 ^ 40 * 7734376 * 2
def baseEnd_7734376 : Nat := 3971452450598936452030259

theorem tailTrace_7734376 : CollatzResearch.WordTrace tailWord_7734376 prefixEnd_7734376 3971452450598936452030259 := by
  unfold tailWord_7734376
  simp only [CollatzResearch.WordTrace]
  refine ⟨141047933913842076550799491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 188063911885122768734399321 141047933913842076550799491)
  ·
    refine ⟨211571900870763114826199237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141047933913842076550799491 211571900870763114826199237)
    ·
      refine ⟨39669731413268084029912357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 211571900870763114826199237 39669731413268084029912357)
      ·
        refine ⟨7438074639987765755608567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 39669731413268084029912357 7438074639987765755608567)
        ·
          refine ⟨11157111959981648633412851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7438074639987765755608567 11157111959981648633412851)
          ·
            refine ⟨16735667939972472950119277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11157111959981648633412851 16735667939972472950119277)
            ·
              refine ⟨6275875477489677356294729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16735667939972472950119277 6275875477489677356294729)
              ·
                refine ⟨4706906608117258017221047, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6275875477489677356294729 4706906608117258017221047)
                ·
                  refine ⟨7060359912175887025831571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4706906608117258017221047 7060359912175887025831571)
                  ·
                    refine ⟨10590539868263830538747357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7060359912175887025831571 10590539868263830538747357)
                    ·
                      refine ⟨3971452450598936452030259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10590539868263830538747357 3971452450598936452030259)
                      ·
                        rfl

theorem cell23_7734376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 1, 1, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 1, 1, 3, 2, 1, 1, 3].length) (baseStart_7734376 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7734376 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7734376 prefixEnd_7734376 := by exact prefixLift 7734376
  have htrace : WordTrace (prefixWord ++ tailWord_7734376) baseStart_7734376 baseEnd_7734376 := by
    simpa [prefixWord, tailWord_7734376, baseEnd_7734376] using wordTrace_append hprefix tailTrace_7734376
  have hstable : (prefixWord ++ tailWord_7734376).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7734376).length < 2 ^ (prefixWord ++ tailWord_7734376).sum := by decide
  have hdescent : baseEnd_7734376 < baseStart_7734376 := by decide
  rcases family_descends (prefixWord ++ tailWord_7734376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7734382 : List Nat := [4, 1, 2, 2, 1, 2, 3, 1, 3, 2, 2]
def baseStart_7734382 : Nat := 118140960795 + 7734382 * 2 ^ 59
def prefixEnd_7734382 : Nat := 4983230072969 + 3 ^ 40 * 7734382 * 2
def baseEnd_7734382 : Nat := 3971455531482863428555231

theorem tailTrace_7734382 : CollatzResearch.WordTrace tailWord_7734382 prefixEnd_7734382 3971455531482863428555231 := by
  unfold tailWord_7734382
  simp only [CollatzResearch.WordTrace]
  refine ⟨35262010833207802015789675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 188064057777108277417544933 35262010833207802015789675)
  ·
    refine ⟨52893016249811703023684513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35262010833207802015789675 52893016249811703023684513)
    ·
      refine ⟨39669762187358777267763385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52893016249811703023684513 39669762187358777267763385)
      ·
        refine ⟨29752321640519082950822539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39669762187358777267763385 29752321640519082950822539)
        ·
          refine ⟨44628482460778624426233809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29752321640519082950822539 44628482460778624426233809)
          ·
            refine ⟨33471361845583968319675357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44628482460778624426233809 33471361845583968319675357)
            ·
              refine ⟨12551760692093988119878259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33471361845583968319675357 12551760692093988119878259)
              ·
                refine ⟨18827641038140982179817389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12551760692093988119878259 18827641038140982179817389)
                ·
                  refine ⟨7060365389302868317431521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18827641038140982179817389 7060365389302868317431521)
                  ·
                    refine ⟨5295274041977151238073641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7060365389302868317431521 5295274041977151238073641)
                    ·
                      refine ⟨3971455531482863428555231, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5295274041977151238073641 3971455531482863428555231)
                      ·
                        rfl

theorem cell23_7734382_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 3, 1, 3, 2, 2].length) (baseStart_7734382 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7734382 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7734382 prefixEnd_7734382 := by exact prefixLift 7734382
  have htrace : WordTrace (prefixWord ++ tailWord_7734382) baseStart_7734382 baseEnd_7734382 := by
    simpa [prefixWord, tailWord_7734382, baseEnd_7734382] using wordTrace_append hprefix tailTrace_7734382
  have hstable : (prefixWord ++ tailWord_7734382).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7734382).length < 2 ^ (prefixWord ++ tailWord_7734382).sum := by decide
  have hdescent : baseEnd_7734382 < baseStart_7734382 := by decide
  rcases family_descends (prefixWord ++ tailWord_7734382) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7734442 : List Nat := [3, 1, 5, 1, 1, 1, 1, 2, 3, 3, 2]
def baseStart_7734442 : Nat := 118140960795 + 7734442 * 2 ^ 59
def prefixEnd_7734442 : Nat := 4983230072969 + 3 ^ 40 * 7734442 * 2
def baseEnd_7734442 : Nat := 3971486340322133193804955

theorem tailTrace_7734442 : CollatzResearch.WordTrace tailWord_7734442 prefixEnd_7734442 3971486340322133193804955 := by
  unfold tailWord_7734442
  simp only [CollatzResearch.WordTrace]
  refine ⟨70524568761361261593375395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 188065516696963364249001053 70524568761361261593375395)
  ·
    refine ⟨105786853142041892390063093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70524568761361261593375395 105786853142041892390063093)
    ·
      refine ⟨9917517482066427411568415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 105786853142041892390063093 9917517482066427411568415)
      ·
        refine ⟨14876276223099641117352623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9917517482066427411568415 14876276223099641117352623)
        ·
          refine ⟨22314414334649461676028935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14876276223099641117352623 22314414334649461676028935)
          ·
            refine ⟨33471621501974192514043403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22314414334649461676028935 33471621501974192514043403)
            ·
              refine ⟨50207432252961288771065105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33471621501974192514043403 50207432252961288771065105)
              ·
                refine ⟨37655574189720966578298829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50207432252961288771065105 37655574189720966578298829)
                ·
                  refine ⟨14120840321145362466862061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37655574189720966578298829 14120840321145362466862061)
                  ·
                    refine ⟨5295315120429510925073273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14120840321145362466862061 5295315120429510925073273)
                    ·
                      refine ⟨3971486340322133193804955, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5295315120429510925073273 3971486340322133193804955)
                      ·
                        rfl

theorem cell23_7734442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 1, 2, 3, 3, 2].length) (baseStart_7734442 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7734442 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7734442 prefixEnd_7734442 := by exact prefixLift 7734442
  have htrace : WordTrace (prefixWord ++ tailWord_7734442) baseStart_7734442 baseEnd_7734442 := by
    simpa [prefixWord, tailWord_7734442, baseEnd_7734442] using wordTrace_append hprefix tailTrace_7734442
  have hstable : (prefixWord ++ tailWord_7734442).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7734442).length < 2 ^ (prefixWord ++ tailWord_7734442).sum := by decide
  have hdescent : baseEnd_7734442 < baseStart_7734442 := by decide
  rcases family_descends (prefixWord ++ tailWord_7734442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7734451 : List Nat := [1, 1, 1, 2, 3, 2, 3, 1, 1, 4, 4]
def baseStart_7734451 : Nat := 118140960795 + 7734451 * 2 ^ 59
def prefixEnd_7734451 : Nat := 4983230072969 + 3 ^ 40 * 7734451 * 2
def baseEnd_7734451 : Nat := 3971490961648023658592413

theorem tailTrace_7734451 : CollatzResearch.WordTrace tailWord_7734451 prefixEnd_7734451 3971490961648023658592413 := by
  unfold tailWord_7734451
  simp only [CollatzResearch.WordTrace]
  refine ⟨282098603302412440910579207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188065735534941627273719471 282098603302412440910579207)
  ·
    refine ⟨423147904953618661365868811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 282098603302412440910579207 423147904953618661365868811)
    ·
      refine ⟨634721857430427992048803217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 423147904953618661365868811 634721857430427992048803217)
      ·
        refine ⟨476041393072820994036602413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 634721857430427992048803217 476041393072820994036602413)
        ·
          refine ⟨178515522402307872763725905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 476041393072820994036602413 178515522402307872763725905)
          ·
            refine ⟨133886641801730904572794429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 178515522402307872763725905 133886641801730904572794429)
            ·
              refine ⟨50207490675649089214797911, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 133886641801730904572794429 50207490675649089214797911)
              ·
                refine ⟨75311236013473633822196867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50207490675649089214797911 75311236013473633822196867)
                ·
                  refine ⟨112966854020210450733295301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 75311236013473633822196867 112966854020210450733295301)
                  ·
                    refine ⟨21181285128789459512492869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 112966854020210450733295301 21181285128789459512492869)
                    ·
                      refine ⟨3971490961648023658592413, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21181285128789459512492869 3971490961648023658592413)
                      ·
                        rfl

theorem cell23_7734451_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 3, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 3, 1, 1, 4, 4].length) (baseStart_7734451 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7734451 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7734451 prefixEnd_7734451 := by exact prefixLift 7734451
  have htrace : WordTrace (prefixWord ++ tailWord_7734451) baseStart_7734451 baseEnd_7734451 := by
    simpa [prefixWord, tailWord_7734451, baseEnd_7734451] using wordTrace_append hprefix tailTrace_7734451
  have hstable : (prefixWord ++ tailWord_7734451).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7734451).length < 2 ^ (prefixWord ++ tailWord_7734451).sum := by decide
  have hdescent : baseEnd_7734451 < baseStart_7734451 := by decide
  rcases family_descends (prefixWord ++ tailWord_7734451) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7734455 : List Nat := [1, 1, 3, 1, 4, 1, 4, 1, 1, 4, 2]
def baseStart_7734455 : Nat := 118140960795 + 7734455 * 2 ^ 59
def prefixEnd_7734455 : Nat := 4983230072969 + 3 ^ 40 * 7734455 * 2
def baseEnd_7734455 : Nat := 3971493015570641642942395

theorem tailTrace_7734455 : CollatzResearch.WordTrace tailWord_7734455 prefixEnd_7734455 3971493015570641642942395 := by
  unfold tailWord_7734455
  simp only [CollatzResearch.WordTrace]
  refine ⟨282098749194397949593724819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188065832796265299729149879 282098749194397949593724819)
  ·
    refine ⟨423148123791596924390587229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 282098749194397949593724819 423148123791596924390587229)
    ·
      refine ⟨158680546421848846646470211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 423148123791596924390587229 158680546421848846646470211)
      ·
        refine ⟨238020819632773269969705317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 158680546421848846646470211 238020819632773269969705317)
        ·
          refine ⟨44628903681144988119319747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 238020819632773269969705317 44628903681144988119319747)
          ·
            refine ⟨66943355521717482178979621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44628903681144988119319747 66943355521717482178979621)
            ·
              refine ⟨12551879160322027908558679, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 66943355521717482178979621 12551879160322027908558679)
              ·
                refine ⟨18827818740483041862838019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12551879160322027908558679 18827818740483041862838019)
                ·
                  refine ⟨28241728110724562794257029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18827818740483041862838019 28241728110724562794257029)
                  ·
                    refine ⟨5295324020760855523923193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28241728110724562794257029 5295324020760855523923193)
                    ·
                      refine ⟨3971493015570641642942395, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5295324020760855523923193 3971493015570641642942395)
                      ·
                        rfl

theorem cell23_7734455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 4, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 4, 1, 1, 4, 2].length) (baseStart_7734455 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7734455 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7734455 prefixEnd_7734455 := by exact prefixLift 7734455
  have htrace : WordTrace (prefixWord ++ tailWord_7734455) baseStart_7734455 baseEnd_7734455 := by
    simpa [prefixWord, tailWord_7734455, baseEnd_7734455] using wordTrace_append hprefix tailTrace_7734455
  have hstable : (prefixWord ++ tailWord_7734455).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7734455).length < 2 ^ (prefixWord ++ tailWord_7734455).sum := by decide
  have hdescent : baseEnd_7734455 < baseStart_7734455 := by decide
  rcases family_descends (prefixWord ++ tailWord_7734455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7734461 : List Nat := [1, 4, 1, 2, 1, 1, 3, 1, 9]
def baseStart_7734461 : Nat := 118140960795 + 7734461 * 2 ^ 59
def prefixEnd_7734461 : Nat := 4983230072969 + 3 ^ 40 * 7734461 * 2
def baseEnd_7734461 : Nat := 441277344050507624385263

theorem tailTrace_7734461 : CollatzResearch.WordTrace tailWord_7734461 prefixEnd_7734461 441277344050507624385263 := by
  unfold tailWord_7734461
  simp only [CollatzResearch.WordTrace]
  refine ⟨282098968032376212618443237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188065978688250808412295491 282098968032376212618443237)
  ·
    refine ⟨52893556506070539865958107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 282098968032376212618443237 52893556506070539865958107)
    ·
      refine ⟨79340334759105809798937161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52893556506070539865958107 79340334759105809798937161)
      ·
        refine ⟨59505251069329357349202871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79340334759105809798937161 59505251069329357349202871)
        ·
          refine ⟨89257876603994036023804307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59505251069329357349202871 89257876603994036023804307)
          ·
            refine ⟨133886814905991054035706461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89257876603994036023804307 133886814905991054035706461)
            ·
              refine ⟨50207555589746645263389923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 133886814905991054035706461 50207555589746645263389923)
              ·
                refine ⟨75311333384619967895084885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50207555589746645263389923 75311333384619967895084885)
                ·
                  refine ⟨441277344050507624385263, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 75311333384619967895084885 441277344050507624385263)
                  ·
                    rfl

theorem cell23_7734461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 3, 1, 9].length) (baseStart_7734461 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7734461 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7734461 prefixEnd_7734461 := by exact prefixLift 7734461
  have htrace : WordTrace (prefixWord ++ tailWord_7734461) baseStart_7734461 baseEnd_7734461 := by
    simpa [prefixWord, tailWord_7734461, baseEnd_7734461] using wordTrace_append hprefix tailTrace_7734461
  have hstable : (prefixWord ++ tailWord_7734461).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7734461).length < 2 ^ (prefixWord ++ tailWord_7734461).sum := by decide
  have hdescent : baseEnd_7734461 < baseStart_7734461 := by decide
  rcases family_descends (prefixWord ++ tailWord_7734461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7734470 : List Nat := [6, 1, 2, 2, 2, 1, 2, 1, 1, 2, 3]
def baseStart_7734470 : Nat := 118140960795 + 7734470 * 2 ^ 59
def prefixEnd_7734470 : Nat := 4983230072969 + 3 ^ 40 * 7734470 * 2
def baseEnd_7734470 : Nat := 3971500717780459084254827

theorem tailTrace_7734470 : CollatzResearch.WordTrace tailWord_7734470 prefixEnd_7734470 3971500717780459084254827 := by
  unfold tailWord_7734470
  simp only [CollatzResearch.WordTrace]
  refine ⟨8815603009041987723610027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 188066197526229071437013909 8815603009041987723610027)
  ·
    refine ⟨13223404513562981585415041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8815603009041987723610027 13223404513562981585415041)
    ·
      refine ⟨9917553385172236189061281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13223404513562981585415041 9917553385172236189061281)
      ·
        refine ⟨7438165038879177141795961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9917553385172236189061281 7438165038879177141795961)
        ·
          refine ⟨5578623779159382856346971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7438165038879177141795961 5578623779159382856346971)
          ·
            refine ⟨8367935668739074284520457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5578623779159382856346971 8367935668739074284520457)
            ·
              refine ⟨6275951751554305713390343, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8367935668739074284520457 6275951751554305713390343)
              ·
                refine ⟨9413927627331458570085515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6275951751554305713390343 9413927627331458570085515)
                ·
                  refine ⟨14120891440997187855128273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9413927627331458570085515 14120891440997187855128273)
                  ·
                    refine ⟨10590668580747890891346205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14120891440997187855128273 10590668580747890891346205)
                    ·
                      refine ⟨3971500717780459084254827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10590668580747890891346205 3971500717780459084254827)
                      ·
                        rfl

theorem cell23_7734470_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 2, 1, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 2, 1, 2, 1, 1, 2, 3].length) (baseStart_7734470 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7734470 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7734470 prefixEnd_7734470 := by exact prefixLift 7734470
  have htrace : WordTrace (prefixWord ++ tailWord_7734470) baseStart_7734470 baseEnd_7734470 := by
    simpa [prefixWord, tailWord_7734470, baseEnd_7734470] using wordTrace_append hprefix tailTrace_7734470
  have hstable : (prefixWord ++ tailWord_7734470).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7734470).length < 2 ^ (prefixWord ++ tailWord_7734470).sum := by decide
  have hdescent : baseEnd_7734470 < baseStart_7734470 := by decide
  rcases family_descends (prefixWord ++ tailWord_7734470) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7734518 : List Nat := [5, 1, 1, 1, 1, 1, 1, 2, 3, 2, 5]
def baseStart_7734518 : Nat := 118140960795 + 7734518 * 2 ^ 59
def prefixEnd_7734518 : Nat := 4983230072969 + 3 ^ 40 * 7734518 * 2
def baseEnd_7734518 : Nat := 3971525364851874896454605

theorem tailTrace_7734518 : CollatzResearch.WordTrace tailWord_7734518 prefixEnd_7734518 3971525364851874896454605 := by
  unfold tailWord_7734518
  simp only [CollatzResearch.WordTrace]
  refine ⟨17631315437073106959579263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 188067364662113140902178805 17631315437073106959579263)
  ·
    refine ⟨26446973155609660439368895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17631315437073106959579263 26446973155609660439368895)
    ·
      refine ⟨39670459733414490659053343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26446973155609660439368895 39670459733414490659053343)
      ·
        refine ⟨59505689600121735988580015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39670459733414490659053343 59505689600121735988580015)
        ·
          refine ⟨89258534400182603982870023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59505689600121735988580015 89258534400182603982870023)
          ·
            refine ⟨133887801600273905974305035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89258534400182603982870023 133887801600273905974305035)
            ·
              refine ⟨200831702400410858961457553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 133887801600273905974305035 200831702400410858961457553)
              ·
                refine ⟨150623776800308144221093165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 200831702400410858961457553 150623776800308144221093165)
                ·
                  refine ⟨56483916300115554082909937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 150623776800308144221093165 56483916300115554082909937)
                  ·
                    refine ⟨42362937225086665562182453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 56483916300115554082909937 42362937225086665562182453)
                    ·
                      refine ⟨3971525364851874896454605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42362937225086665562182453 3971525364851874896454605)
                      ·
                        rfl

theorem cell23_7734518_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 1, 2, 3, 2, 5].length) (baseStart_7734518 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7734518 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7734518 prefixEnd_7734518 := by exact prefixLift 7734518
  have htrace : WordTrace (prefixWord ++ tailWord_7734518) baseStart_7734518 baseEnd_7734518 := by
    simpa [prefixWord, tailWord_7734518, baseEnd_7734518] using wordTrace_append hprefix tailTrace_7734518
  have hstable : (prefixWord ++ tailWord_7734518).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7734518).length < 2 ^ (prefixWord ++ tailWord_7734518).sum := by decide
  have hdescent : baseEnd_7734518 < baseStart_7734518 := by decide
  rcases family_descends (prefixWord ++ tailWord_7734518) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7734521 : List Nat := [1, 2, 1, 3, 1, 1, 3, 1, 2, 8]
def baseStart_7734521 : Nat := 118140960795 + 7734521 * 2 ^ 59
def prefixEnd_7734521 : Nat := 4983230072969 + 3 ^ 40 * 7734521 * 2
def baseEnd_7734521 : Nat := 1323842301764612794905697

theorem tailTrace_7734521 : CollatzResearch.WordTrace tailWord_7734521 prefixEnd_7734521 1323842301764612794905697 := by
  unfold tailWord_7734521
  simp only [CollatzResearch.WordTrace]
  refine ⟨282101156412158842865627417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188067437608105895243751611 282101156412158842865627417)
  ·
    refine ⟨211575867309119132149220563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 282101156412158842865627417 211575867309119132149220563)
    ·
      refine ⟨317363800963678698223830845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 211575867309119132149220563 317363800963678698223830845)
      ·
        refine ⟨119011425361379511833936567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 317363800963678698223830845 119011425361379511833936567)
        ·
          refine ⟨178517138042069267750904851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 119011425361379511833936567 178517138042069267750904851)
          ·
            refine ⟨267775707063103901626357277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 178517138042069267750904851 267775707063103901626357277)
            ·
              refine ⟨100415890148663963109883979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 267775707063103901626357277 100415890148663963109883979)
              ·
                refine ⟨150623835222995944664825969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 100415890148663963109883979 150623835222995944664825969)
                ·
                  refine ⟨112967876417246958498619477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 150623835222995944664825969 112967876417246958498619477)
                  ·
                    refine ⟨1323842301764612794905697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 112967876417246958498619477 1323842301764612794905697)
                    ·
                      rfl

theorem cell23_7734521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 3, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 3, 1, 2, 8].length) (baseStart_7734521 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7734521 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7734521 prefixEnd_7734521 := by exact prefixLift 7734521
  have htrace : WordTrace (prefixWord ++ tailWord_7734521) baseStart_7734521 baseEnd_7734521 := by
    simpa [prefixWord, tailWord_7734521, baseEnd_7734521] using wordTrace_append hprefix tailTrace_7734521
  have hstable : (prefixWord ++ tailWord_7734521).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7734521).length < 2 ^ (prefixWord ++ tailWord_7734521).sum := by decide
  have hdescent : baseEnd_7734521 < baseStart_7734521 := by decide
  rcases family_descends (prefixWord ++ tailWord_7734521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7734528 : List Nat := [2, 1, 1, 2, 1, 1, 3, 5, 2, 1, 4]
def baseStart_7734528 : Nat := 118140960795 + 7734528 * 2 ^ 59
def prefixEnd_7734528 : Nat := 4983230072969 + 3 ^ 40 * 7734528 * 2
def baseEnd_7734528 : Nat := 3971530499658419857329559

theorem tailTrace_7734528 : CollatzResearch.WordTrace tailWord_7734528 prefixEnd_7734528 3971530499658419857329559 := by
  unfold tailWord_7734528
  simp only [CollatzResearch.WordTrace]
  refine ⟨141050705861566741530566119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 188067607815422322040754825 141050705861566741530566119)
  ·
    refine ⟨211576058792350112295849179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141050705861566741530566119 211576058792350112295849179)
    ·
      refine ⟨317364088188525168443773769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 211576058792350112295849179 317364088188525168443773769)
      ·
        refine ⟨238023066141393876332830327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 317364088188525168443773769 238023066141393876332830327)
        ·
          refine ⟨357034599212090814499245491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 238023066141393876332830327 357034599212090814499245491)
          ·
            refine ⟨535551898818136221748868237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 357034599212090814499245491 535551898818136221748868237)
            ·
              refine ⟨200831962056801083155825589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 535551898818136221748868237 200831962056801083155825589)
              ·
                refine ⟨18827996442825101545858649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 200831962056801083155825589 18827996442825101545858649)
                ·
                  refine ⟨14120997332118826159393987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18827996442825101545858649 14120997332118826159393987)
                  ·
                    refine ⟨21181495998178239239090981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14120997332118826159393987 21181495998178239239090981)
                    ·
                      refine ⟨3971530499658419857329559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21181495998178239239090981 3971530499658419857329559)
                      ·
                        rfl

theorem cell23_7734528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 3, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 3, 5, 2, 1, 4].length) (baseStart_7734528 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7734528 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7734528 prefixEnd_7734528 := by exact prefixLift 7734528
  have htrace : WordTrace (prefixWord ++ tailWord_7734528) baseStart_7734528 baseEnd_7734528 := by
    simpa [prefixWord, tailWord_7734528, baseEnd_7734528] using wordTrace_append hprefix tailTrace_7734528
  have hstable : (prefixWord ++ tailWord_7734528).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7734528).length < 2 ^ (prefixWord ++ tailWord_7734528).sum := by decide
  have hdescent : baseEnd_7734528 < baseStart_7734528 := by decide
  rcases family_descends (prefixWord ++ tailWord_7734528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7734546 : List Nat := [3, 2, 4, 2, 1, 1, 3, 2, 5]
def baseStart_7734546 : Nat := 118140960795 + 7734546 * 2 ^ 59
def prefixEnd_7734546 : Nat := 4983230072969 + 3 ^ 40 * 7734546 * 2
def baseEnd_7734546 : Nat := 441282193590022309656053

theorem tailTrace_7734546 : CollatzResearch.WordTrace tailWord_7734546 prefixEnd_7734546 441282193590022309656053 := by
  unfold tailWord_7734546
  simp only [CollatzResearch.WordTrace]
  refine ⟨70525517059267068033821873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 188068045491378848090191661 70525517059267068033821873)
  ·
    refine ⟨52894137794450301025366405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70525517059267068033821873 52894137794450301025366405)
    ·
      refine ⟨9917650836459431442256201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 52894137794450301025366405 9917650836459431442256201)
      ·
        refine ⟨7438238127344573581692151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9917650836459431442256201 7438238127344573581692151)
        ·
          refine ⟨11157357191016860372538227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7438238127344573581692151 11157357191016860372538227)
          ·
            refine ⟨16736035786525290558807341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11157357191016860372538227 16736035786525290558807341)
            ·
              refine ⟨6276013419946983959552753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16736035786525290558807341 6276013419946983959552753)
              ·
                refine ⟨4707010064960237969664565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6276013419946983959552753 4707010064960237969664565)
                ·
                  refine ⟨441282193590022309656053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4707010064960237969664565 441282193590022309656053)
                  ·
                    rfl

theorem cell23_7734546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 1, 1, 3, 2, 5].length) (baseStart_7734546 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7734546 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7734546 prefixEnd_7734546 := by exact prefixLift 7734546
  have htrace : WordTrace (prefixWord ++ tailWord_7734546) baseStart_7734546 baseEnd_7734546 := by
    simpa [prefixWord, tailWord_7734546, baseEnd_7734546] using wordTrace_append hprefix tailTrace_7734546
  have hstable : (prefixWord ++ tailWord_7734546).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7734546).length < 2 ^ (prefixWord ++ tailWord_7734546).sum := by decide
  have hdescent : baseEnd_7734546 < baseStart_7734546 := by decide
  rcases family_descends (prefixWord ++ tailWord_7734546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7734612 : List Nat := [2, 4, 1, 1, 2, 1, 2, 3, 3, 1, 3]
def baseStart_7734612 : Nat := 118140960795 + 7734612 * 2 ^ 59
def prefixEnd_7734612 : Nat := 4983230072969 + 3 ^ 40 * 7734612 * 2
def baseEnd_7734612 : Nat := 3971573632033397528679173

theorem tailTrace_7734612 : CollatzResearch.WordTrace tailWord_7734612 prefixEnd_7734612 3971573632033397528679173 := by
  unfold tailWord_7734612
  simp only [CollatzResearch.WordTrace]
  refine ⟨141052237727414582703595045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 188069650303219443604793393 141052237727414582703595045)
  ·
    refine ⟨26447294573890234256924071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 141052237727414582703595045 26447294573890234256924071)
    ·
      refine ⟨39670941860835351385386107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26447294573890234256924071 39670941860835351385386107)
      ·
        refine ⟨59506412791253027078079161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39670941860835351385386107 59506412791253027078079161)
        ·
          refine ⟨44629809593439770308559371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59506412791253027078079161 44629809593439770308559371)
          ·
            refine ⟨66944714390159655462839057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44629809593439770308559371 66944714390159655462839057)
            ·
              refine ⟨50208535792619741597129293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66944714390159655462839057 50208535792619741597129293)
              ·
                refine ⟨18828200922232403098923485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 50208535792619741597129293 18828200922232403098923485)
                ·
                  refine ⟨7060575345837151162096307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18828200922232403098923485 7060575345837151162096307)
                  ·
                    refine ⟨10590863018755726743144461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7060575345837151162096307 10590863018755726743144461)
                    ·
                      refine ⟨3971573632033397528679173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10590863018755726743144461 3971573632033397528679173)
                      ·
                        rfl

theorem cell23_7734612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 2, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 2, 3, 3, 1, 3].length) (baseStart_7734612 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7734612 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7734612 prefixEnd_7734612 := by exact prefixLift 7734612
  have htrace : WordTrace (prefixWord ++ tailWord_7734612) baseStart_7734612 baseEnd_7734612 := by
    simpa [prefixWord, tailWord_7734612, baseEnd_7734612] using wordTrace_append hprefix tailTrace_7734612
  have hstable : (prefixWord ++ tailWord_7734612).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7734612).length < 2 ^ (prefixWord ++ tailWord_7734612).sum := by decide
  have hdescent : baseEnd_7734612 < baseStart_7734612 := by decide
  rcases family_descends (prefixWord ++ tailWord_7734612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7734652 : List Nat := [2, 2, 2, 1, 1, 1, 3, 2, 5, 2, 2]
def baseStart_7734652 : Nat := 118140960795 + 7734652 * 2 ^ 59
def prefixEnd_7734652 : Nat := 4983230072969 + 3 ^ 40 * 7734652 * 2
def baseEnd_7734652 : Nat := 3971594171259577372178989

theorem tailTrace_7734652 : CollatzResearch.WordTrace tailWord_7734652 prefixEnd_7734652 3971594171259577372178989 := by
  unfold tailWord_7734652
  simp only [CollatzResearch.WordTrace]
  refine ⟨141052967187342126119323105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 188070622916456168159097473 141052967187342126119323105)
  ·
    refine ⟨105789725390506594589492329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 141052967187342126119323105 105789725390506594589492329)
    ·
      refine ⟨79342294042879945942119247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 105789725390506594589492329 79342294042879945942119247)
      ·
        refine ⟨119013441064319918913178871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79342294042879945942119247 119013441064319918913178871)
        ·
          refine ⟨178520161596479878369768307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 119013441064319918913178871 178520161596479878369768307)
          ·
            refine ⟨267780242394719817554652461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 178520161596479878369768307 267780242394719817554652461)
            ·
              refine ⟨100417590898019931582994673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 267780242394719817554652461 100417590898019931582994673)
              ·
                refine ⟨75313193173514948687246005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 100417590898019931582994673 75313193173514948687246005)
                ·
                  refine ⟨7060611860017026439429313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 75313193173514948687246005 7060611860017026439429313)
                  ·
                    refine ⟨5295458895012769829571985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7060611860017026439429313 5295458895012769829571985)
                    ·
                      refine ⟨3971594171259577372178989, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5295458895012769829571985 3971594171259577372178989)
                      ·
                        rfl

theorem cell23_7734652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 3, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 3, 2, 5, 2, 2].length) (baseStart_7734652 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7734652 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7734652 prefixEnd_7734652 := by exact prefixLift 7734652
  have htrace : WordTrace (prefixWord ++ tailWord_7734652) baseStart_7734652 baseEnd_7734652 := by
    simpa [prefixWord, tailWord_7734652, baseEnd_7734652] using wordTrace_append hprefix tailTrace_7734652
  have hstable : (prefixWord ++ tailWord_7734652).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7734652).length < 2 ^ (prefixWord ++ tailWord_7734652).sum := by decide
  have hdescent : baseEnd_7734652 < baseStart_7734652 := by decide
  rcases family_descends (prefixWord ++ tailWord_7734652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7734686 : List Nat := [4, 3, 1, 2, 2, 1, 2, 2, 1, 1, 4]
def baseStart_7734686 : Nat := 118140960795 + 7734686 * 2 ^ 59
def prefixEnd_7734686 : Nat := 4983230072969 + 3 ^ 40 * 7734686 * 2
def baseEnd_7734686 : Nat := 3971611629601830239153833

theorem tailTrace_7734686 : CollatzResearch.WordTrace tailWord_7734686 prefixEnd_7734686 3971611629601830239153833 := by
  unfold tailWord_7734686
  simp only [CollatzResearch.WordTrace]
  refine ⟨35263396807070134505672989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 188071449637707384030255941 35263396807070134505672989)
  ·
    refine ⟨13223773802651300439627371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35263396807070134505672989 13223773802651300439627371)
    ·
      refine ⟨19835660703976950659441057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13223773802651300439627371 19835660703976950659441057)
      ·
        refine ⟨14876745527982712994580793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19835660703976950659441057 14876745527982712994580793)
        ·
          refine ⟨11157559145987034745935595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14876745527982712994580793 11157559145987034745935595)
          ·
            refine ⟨16736338718980552118903393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11157559145987034745935595 16736338718980552118903393)
            ·
              refine ⟨12552254039235414089177545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16736338718980552118903393 12552254039235414089177545)
              ·
                refine ⟨9414190529426560566883159, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12552254039235414089177545 9414190529426560566883159)
                ·
                  refine ⟨14121285794139840850324739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9414190529426560566883159 14121285794139840850324739)
                  ·
                    refine ⟨21181928691209761275487109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14121285794139840850324739 21181928691209761275487109)
                    ·
                      refine ⟨3971611629601830239153833, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21181928691209761275487109 3971611629601830239153833)
                      ·
                        rfl

theorem cell23_7734686_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 2, 1, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 2, 1, 2, 2, 1, 1, 4].length) (baseStart_7734686 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7734686 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7734686 prefixEnd_7734686 := by exact prefixLift 7734686
  have htrace : WordTrace (prefixWord ++ tailWord_7734686) baseStart_7734686 baseEnd_7734686 := by
    simpa [prefixWord, tailWord_7734686, baseEnd_7734686] using wordTrace_append hprefix tailTrace_7734686
  have hstable : (prefixWord ++ tailWord_7734686).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7734686).length < 2 ^ (prefixWord ++ tailWord_7734686).sum := by decide
  have hdescent : baseEnd_7734686 < baseStart_7734686 := by decide
  rcases family_descends (prefixWord ++ tailWord_7734686) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7734745 : List Nat := [1, 2, 1, 2, 4, 2, 1, 2, 2, 1, 5]
def baseStart_7734745 : Nat := 118140960795 + 7734745 * 2 ^ 59
def prefixEnd_7734745 : Nat := 4983230072969 + 3 ^ 40 * 7734745 * 2
def baseEnd_7734745 : Nat := 3971641924960445508316061

theorem tailTrace_7734745 : CollatzResearch.WordTrace tailWord_7734745 prefixEnd_7734745 3971641924960445508316061 := by
  unfold tailWord_7734745
  simp only [CollatzResearch.WordTrace]
  refine ⟨282109326363347329121781689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188072884242231552747854459 282109326363347329121781689)
  ·
    refine ⟨211581994772510496841336267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 282109326363347329121781689 211581994772510496841336267)
    ·
      refine ⟨317372992158765745262004401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 211581994772510496841336267 317372992158765745262004401)
      ·
        refine ⟨238029744119074308946503301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 317372992158765745262004401 238029744119074308946503301)
        ·
          refine ⟨44630577022326432927469369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 238029744119074308946503301 44630577022326432927469369)
          ·
            refine ⟨33472932766744824695602027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44630577022326432927469369 33472932766744824695602027)
            ·
              refine ⟨50209399150117237043403041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33472932766744824695602027 50209399150117237043403041)
              ·
                refine ⟨37657049362587927782552281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50209399150117237043403041 37657049362587927782552281)
                ·
                  refine ⟨28242787021940945836914211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37657049362587927782552281 28242787021940945836914211)
                  ·
                    refine ⟨42364180532911418755371317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28242787021940945836914211 42364180532911418755371317)
                    ·
                      refine ⟨3971641924960445508316061, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42364180532911418755371317 3971641924960445508316061)
                      ·
                        rfl

theorem cell23_7734745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 1, 2, 2, 1, 5].length) (baseStart_7734745 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7734745 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7734745 prefixEnd_7734745 := by exact prefixLift 7734745
  have htrace : WordTrace (prefixWord ++ tailWord_7734745) baseStart_7734745 baseEnd_7734745 := by
    simpa [prefixWord, tailWord_7734745, baseEnd_7734745] using wordTrace_append hprefix tailTrace_7734745
  have hstable : (prefixWord ++ tailWord_7734745).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7734745).length < 2 ^ (prefixWord ++ tailWord_7734745).sum := by decide
  have hdescent : baseEnd_7734745 < baseStart_7734745 := by decide
  rcases family_descends (prefixWord ++ tailWord_7734745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7734746 : List Nat := [3, 1, 1, 2, 3, 4, 1, 2, 1, 3, 2]
def baseStart_7734746 : Nat := 118140960795 + 7734746 * 2 ^ 59
def prefixEnd_7734746 : Nat := 4983230072969 + 3 ^ 40 * 7734746 * 2
def baseEnd_7734746 : Nat := 3971642438441100004403557

theorem tailTrace_7734746 : CollatzResearch.WordTrace tailWord_7734746 prefixEnd_7734746 3971642438441100004403557 := by
  unfold tailWord_7734746
  simp only [CollatzResearch.WordTrace]
  refine ⟨70527340709085926573142023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 188072908557562470861712061 70527340709085926573142023)
  ·
    refine ⟨105791011063628889859713035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70527340709085926573142023 105791011063628889859713035)
    ·
      refine ⟨158686516595443334789569553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105791011063628889859713035 158686516595443334789569553)
      ·
        refine ⟨119014887446582501092177165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 158686516595443334789569553 119014887446582501092177165)
        ·
          refine ⟨44630582792468437909566437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 119014887446582501092177165 44630582792468437909566437)
          ·
            refine ⟨8368234273587832108043707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 44630582792468437909566437 8368234273587832108043707)
            ·
              refine ⟨12552351410381748162065561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8368234273587832108043707 12552351410381748162065561)
              ·
                refine ⟨9414263557786311121549171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12552351410381748162065561 9414263557786311121549171)
                ·
                  refine ⟨14121395336679466682323757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9414263557786311121549171 14121395336679466682323757)
                  ·
                    refine ⟨5295523251254800005871409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14121395336679466682323757 5295523251254800005871409)
                    ·
                      refine ⟨3971642438441100004403557, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5295523251254800005871409 3971642438441100004403557)
                      ·
                        rfl

theorem cell23_7734746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 4, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 4, 1, 2, 1, 3, 2].length) (baseStart_7734746 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7734746 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7734746 prefixEnd_7734746 := by exact prefixLift 7734746
  have htrace : WordTrace (prefixWord ++ tailWord_7734746) baseStart_7734746 baseEnd_7734746 := by
    simpa [prefixWord, tailWord_7734746, baseEnd_7734746] using wordTrace_append hprefix tailTrace_7734746
  have hstable : (prefixWord ++ tailWord_7734746).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7734746).length < 2 ^ (prefixWord ++ tailWord_7734746).sum := by decide
  have hdescent : baseEnd_7734746 < baseStart_7734746 := by decide
  rcases family_descends (prefixWord ++ tailWord_7734746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7734759 : List Nat := [1, 1, 5, 2, 1, 3, 1, 2, 1, 4, 2]
def baseStart_7734759 : Nat := 118140960795 + 7734759 * 2 ^ 59
def prefixEnd_7734759 : Nat := 4983230072969 + 3 ^ 40 * 7734759 * 2
def baseEnd_7734759 : Nat := 3971649113689608453540997

theorem tailTrace_7734759 : CollatzResearch.WordTrace tailWord_7734759 prefixEnd_7734759 3971649113689608453540997 := by
  unfold tailWord_7734759
  simp only [CollatzResearch.WordTrace]
  refine ⟨282109836985296609512791331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188073224656864406341860887 282109836985296609512791331)
  ·
    refine ⟨423164755477944914269186997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 282109836985296609512791331 423164755477944914269186997)
    ·
      refine ⟨39671695826057335712736281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 423164755477944914269186997 39671695826057335712736281)
      ·
        refine ⟨29753771869543001784552211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39671695826057335712736281 29753771869543001784552211)
        ·
          refine ⟨44630657804314502676828317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29753771869543001784552211 44630657804314502676828317)
          ·
            refine ⟨16736496676617938503810619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44630657804314502676828317 16736496676617938503810619)
            ·
              refine ⟨25104745014926907755715929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16736496676617938503810619 25104745014926907755715929)
              ·
                refine ⟨18828558761195180816786947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25104745014926907755715929 18828558761195180816786947)
                ·
                  refine ⟨28242838141792771225180421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18828558761195180816786947 28242838141792771225180421)
                  ·
                    refine ⟨5295532151586144604721329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28242838141792771225180421 5295532151586144604721329)
                    ·
                      refine ⟨3971649113689608453540997, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5295532151586144604721329 3971649113689608453540997)
                      ·
                        rfl

theorem cell23_7734759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 3, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 3, 1, 2, 1, 4, 2].length) (baseStart_7734759 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7734759 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7734759 prefixEnd_7734759 := by exact prefixLift 7734759
  have htrace : WordTrace (prefixWord ++ tailWord_7734759) baseStart_7734759 baseEnd_7734759 := by
    simpa [prefixWord, tailWord_7734759, baseEnd_7734759] using wordTrace_append hprefix tailTrace_7734759
  have hstable : (prefixWord ++ tailWord_7734759).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7734759).length < 2 ^ (prefixWord ++ tailWord_7734759).sum := by decide
  have hdescent : baseEnd_7734759 < baseStart_7734759 := by decide
  rcases family_descends (prefixWord ++ tailWord_7734759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7734776 : List Nat := [2, 1, 2, 1, 1, 6, 2, 2, 2, 2, 2]
def baseStart_7734776 : Nat := 118140960795 + 7734776 * 2 ^ 59
def prefixEnd_7734776 : Nat := 4983230072969 + 3 ^ 40 * 7734776 * 2
def baseEnd_7734776 : Nat := 3971657842860734887028419

theorem tailTrace_7734776 : CollatzResearch.WordTrace tailWord_7734776 prefixEnd_7734776 3971657842860734887028419 := by
  unfold tailWord_7734776
  simp only [CollatzResearch.WordTrace]
  refine ⟨141055228513117510708080091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 188073638017490014277440121 141055228513117510708080091)
  ·
    refine ⟨211582842769676266062120137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141055228513117510708080091 211582842769676266062120137)
    ·
      refine ⟨158687132077257199546590103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 211582842769676266062120137 158687132077257199546590103)
      ·
        refine ⟨238030698115885799319885155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 158687132077257199546590103 238030698115885799319885155)
        ·
          refine ⟨357046047173828698979827733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 238030698115885799319885155 357046047173828698979827733)
          ·
            refine ⟨16736533461273220264679425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 357046047173828698979827733 16736533461273220264679425)
            ·
              refine ⟨12552400095954915198509569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16736533461273220264679425 12552400095954915198509569)
              ·
                refine ⟨9414300071966186398882177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12552400095954915198509569 9414300071966186398882177)
                ·
                  refine ⟨7060725053974639799161633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9414300071966186398882177 7060725053974639799161633)
                  ·
                    refine ⟨5295543790480979849371225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7060725053974639799161633 5295543790480979849371225)
                    ·
                      refine ⟨3971657842860734887028419, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5295543790480979849371225 3971657842860734887028419)
                      ·
                        rfl

theorem cell23_7734776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 6, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 6, 2, 2, 2, 2, 2].length) (baseStart_7734776 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7734776 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7734776 prefixEnd_7734776 := by exact prefixLift 7734776
  have htrace : WordTrace (prefixWord ++ tailWord_7734776) baseStart_7734776 baseEnd_7734776 := by
    simpa [prefixWord, tailWord_7734776, baseEnd_7734776] using wordTrace_append hprefix tailTrace_7734776
  have hstable : (prefixWord ++ tailWord_7734776).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7734776).length < 2 ^ (prefixWord ++ tailWord_7734776).sum := by decide
  have hdescent : baseEnd_7734776 < baseStart_7734776 := by decide
  rcases family_descends (prefixWord ++ tailWord_7734776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7734814 : List Nat := [4, 3, 3, 1, 1, 2, 2, 1, 1, 3, 2]
def baseStart_7734814 : Nat := 118140960795 + 7734814 * 2 ^ 59
def prefixEnd_7734814 : Nat := 4983230072969 + 3 ^ 40 * 7734814 * 2
def baseEnd_7734814 : Nat := 3971677355125605738353245

theorem tailTrace_7734814 : CollatzResearch.WordTrace tailWord_7734814 prefixEnd_7734814 3971677355125605738353245 := by
  unfold tailWord_7734814
  simp only [CollatzResearch.WordTrace]
  refine ⟨35263980375012169238255437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 188074562000064902604028997 35263980375012169238255437)
  ·
    refine ⟨13223992640629563464345789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35263980375012169238255437 13223992640629563464345789)
    ·
      refine ⟨4958997240236086299129671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13223992640629563464345789 4958997240236086299129671)
      ·
        refine ⟨7438495860354129448694507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4958997240236086299129671 7438495860354129448694507)
        ·
          refine ⟨11157743790531194173041761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7438495860354129448694507 11157743790531194173041761)
          ·
            refine ⟨8368307842898395629781321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11157743790531194173041761 8368307842898395629781321)
            ·
              refine ⟨6276230882173796722335991, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8368307842898395629781321 6276230882173796722335991)
              ·
                refine ⟨9414346323260695083503987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6276230882173796722335991 9414346323260695083503987)
                ·
                  refine ⟨14121519484891042625255981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9414346323260695083503987 14121519484891042625255981)
                  ·
                    refine ⟨5295569806834140984470993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14121519484891042625255981 5295569806834140984470993)
                    ·
                      refine ⟨3971677355125605738353245, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5295569806834140984470993 3971677355125605738353245)
                      ·
                        rfl

theorem cell23_7734814_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 1, 2, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 1, 2, 2, 1, 1, 3, 2].length) (baseStart_7734814 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7734814 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7734814 prefixEnd_7734814 := by exact prefixLift 7734814
  have htrace : WordTrace (prefixWord ++ tailWord_7734814) baseStart_7734814 baseEnd_7734814 := by
    simpa [prefixWord, tailWord_7734814, baseEnd_7734814] using wordTrace_append hprefix tailTrace_7734814
  have hstable : (prefixWord ++ tailWord_7734814).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7734814).length < 2 ^ (prefixWord ++ tailWord_7734814).sum := by decide
  have hdescent : baseEnd_7734814 < baseStart_7734814 := by decide
  rcases family_descends (prefixWord ++ tailWord_7734814) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7734849 : List Nat := [1, 2, 5, 1, 1, 1, 1, 3, 2, 4, 2]
def baseStart_7734849 : Nat := 118140960795 + 7734849 * 2 ^ 59
def prefixEnd_7734849 : Nat := 4983230072969 + 3 ^ 40 * 7734849 * 2
def baseEnd_7734849 : Nat := 3971695326948513101415583

theorem tailTrace_7734849 : CollatzResearch.WordTrace tailWord_7734849 prefixEnd_7734849 3971695326948513101415583 := by
  unfold tailWord_7734849
  simp only [CollatzResearch.WordTrace]
  refine ⟨282113119554970554883567601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188075413036647036589045067 282113119554970554883567601)
  ·
    refine ⟨211584839666227916162675701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 282113119554970554883567601 211584839666227916162675701)
    ·
      refine ⟨19836078718708867140250847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 211584839666227916162675701 19836078718708867140250847)
      ·
        refine ⟨29754118078063300710376271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19836078718708867140250847 29754118078063300710376271)
        ·
          refine ⟨44631177117094951065564407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29754118078063300710376271 44631177117094951065564407)
          ·
            refine ⟨66946765675642426598346611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44631177117094951065564407 66946765675642426598346611)
            ·
              refine ⟨100420148513463639897519917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66946765675642426598346611 100420148513463639897519917)
              ·
                refine ⟨37657555692548864961569969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 100420148513463639897519917 37657555692548864961569969)
                ·
                  refine ⟨28243166769411648721177477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37657555692548864961569969 28243166769411648721177477)
                  ·
                    refine ⟨5295593769264684135220777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28243166769411648721177477 5295593769264684135220777)
                    ·
                      refine ⟨3971695326948513101415583, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5295593769264684135220777 3971695326948513101415583)
                      ·
                        rfl

theorem cell23_7734849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 1, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 1, 3, 2, 4, 2].length) (baseStart_7734849 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7734849 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7734849 prefixEnd_7734849 := by exact prefixLift 7734849
  have htrace : WordTrace (prefixWord ++ tailWord_7734849) baseStart_7734849 baseEnd_7734849 := by
    simpa [prefixWord, tailWord_7734849, baseEnd_7734849] using wordTrace_append hprefix tailTrace_7734849
  have hstable : (prefixWord ++ tailWord_7734849).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7734849).length < 2 ^ (prefixWord ++ tailWord_7734849).sum := by decide
  have hdescent : baseEnd_7734849 < baseStart_7734849 := by decide
  rcases family_descends (prefixWord ++ tailWord_7734849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7734893 : List Nat := [1, 5, 1, 1, 5, 1, 1, 1, 3, 4]
def baseStart_7734893 : Nat := 118140960795 + 7734893 * 2 ^ 59
def prefixEnd_7734893 : Nat := 4983230072969 + 3 ^ 40 * 7734893 * 2
def baseEnd_7734893 : Nat := 1323905973365770309755127

theorem tailTrace_7734893 : CollatzResearch.WordTrace tailWord_7734893 prefixEnd_7734893 1323905973365770309755127 := by
  unfold tailWord_7734893
  simp only [CollatzResearch.WordTrace]
  refine ⟨282114724366811150398169333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188076482911207433598779555 282114724366811150398169333)
  ·
    refine ⟨26448255409388545349828375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 282114724366811150398169333 26448255409388545349828375)
    ·
      refine ⟨39672383114082818024742563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26448255409388545349828375 39672383114082818024742563)
      ·
        refine ⟨59508574671124227037113845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39672383114082818024742563 59508574671124227037113845)
        ·
          refine ⟨5578928875417896284729423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 59508574671124227037113845 5578928875417896284729423)
          ·
            refine ⟨8368393313126844427094135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5578928875417896284729423 8368393313126844427094135)
            ·
              refine ⟨12552589969690266640641203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8368393313126844427094135 12552589969690266640641203)
              ·
                refine ⟨18828884954535399960961805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12552589969690266640641203 18828884954535399960961805)
                ·
                  refine ⟨7060831857950774985360677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18828884954535399960961805 7060831857950774985360677)
                  ·
                    refine ⟨1323905973365770309755127, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7060831857950774985360677 1323905973365770309755127)
                    ·
                      rfl

theorem cell23_7734893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 5, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 5, 1, 1, 1, 3, 4].length) (baseStart_7734893 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7734893 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7734893 prefixEnd_7734893 := by exact prefixLift 7734893
  have htrace : WordTrace (prefixWord ++ tailWord_7734893) baseStart_7734893 baseEnd_7734893 := by
    simpa [prefixWord, tailWord_7734893, baseEnd_7734893] using wordTrace_append hprefix tailTrace_7734893
  have hstable : (prefixWord ++ tailWord_7734893).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7734893).length < 2 ^ (prefixWord ++ tailWord_7734893).sum := by decide
  have hdescent : baseEnd_7734893 < baseStart_7734893 := by decide
  rcases family_descends (prefixWord ++ tailWord_7734893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7734895 : List Nat := [1, 1, 2, 1, 3, 2, 1, 2, 2, 1, 7]
def baseStart_7734895 : Nat := 118140960795 + 7734895 * 2 ^ 59
def prefixEnd_7734895 : Nat := 4983230072969 + 3 ^ 40 * 7734895 * 2
def baseEnd_7734895 : Nat := 3971718947058619921440371

theorem tailTrace_7734895 : CollatzResearch.WordTrace tailWord_7734895 prefixEnd_7734895 3971718947058619921440371 := by
  unfold tailWord_7734895
  simp only [CollatzResearch.WordTrace]
  refine ⟨282114797312803904739742139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188076531541869269826494759 282114797312803904739742139)
  ·
    refine ⟨423172195969205857109613209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 282114797312803904739742139 423172195969205857109613209)
    ·
      refine ⟨317379146976904392832209907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 423172195969205857109613209 317379146976904392832209907)
      ·
        refine ⟨476068720465356589248314861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 317379146976904392832209907 476068720465356589248314861)
        ·
          refine ⟨178525770174508720968118073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 476068720465356589248314861 178525770174508720968118073)
          ·
            refine ⟨133894327630881540726088555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 178525770174508720968118073 133894327630881540726088555)
            ·
              refine ⟨200841491446322311089132833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 133894327630881540726088555 200841491446322311089132833)
              ·
                refine ⟨150631118584741733316849625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 200841491446322311089132833 150631118584741733316849625)
                ·
                  refine ⟨112973338938556299987637219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 150631118584741733316849625 112973338938556299987637219)
                  ·
                    refine ⟨169460008407834449981455829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 112973338938556299987637219 169460008407834449981455829)
                    ·
                      refine ⟨3971718947058619921440371, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 169460008407834449981455829 3971718947058619921440371)
                      ·
                        rfl

theorem cell23_7734895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 1, 2, 2, 1, 7].length) (baseStart_7734895 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7734895 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7734895 prefixEnd_7734895 := by exact prefixLift 7734895
  have htrace : WordTrace (prefixWord ++ tailWord_7734895) baseStart_7734895 baseEnd_7734895 := by
    simpa [prefixWord, tailWord_7734895, baseEnd_7734895] using wordTrace_append hprefix tailTrace_7734895
  have hstable : (prefixWord ++ tailWord_7734895).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7734895).length < 2 ^ (prefixWord ++ tailWord_7734895).sum := by decide
  have hdescent : baseEnd_7734895 < baseStart_7734895 := by decide
  rcases family_descends (prefixWord ++ tailWord_7734895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7734919 : List Nat := [1, 1, 4, 2, 1, 3, 3, 2, 1, 5]
def baseStart_7734919 : Nat := 118140960795 + 7734919 * 2 ^ 59
def prefixEnd_7734919 : Nat := 4983230072969 + 3 ^ 40 * 7734919 * 2
def baseEnd_7734919 : Nat := 1323910423531442609180087

theorem tailTrace_7734919 : CollatzResearch.WordTrace tailWord_7734919 prefixEnd_7734919 1323910423531442609180087 := by
  unfold tailWord_7734919
  simp only [CollatzResearch.WordTrace]
  refine ⟨282115672664716956838615811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188077115109811304559077207 282115672664716956838615811)
  ·
    refine ⟨423173508997075435257923717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 282115672664716956838615811 423173508997075435257923717)
    ·
      refine ⟨79345032936951644110860697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 423173508997075435257923717 79345032936951644110860697)
      ·
        refine ⟨59508774702713733083145523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79345032936951644110860697 59508774702713733083145523)
        ·
          refine ⟨89263162054070599624718285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59508774702713733083145523 89263162054070599624718285)
          ·
            refine ⟨33473685770276474859269357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 89263162054070599624718285 33473685770276474859269357)
            ·
              refine ⟨12552632163853678072226009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33473685770276474859269357 12552632163853678072226009)
              ·
                refine ⟨9414474122890258554169507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12552632163853678072226009 9414474122890258554169507)
                ·
                  refine ⟨14121711184335387831254261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9414474122890258554169507 14121711184335387831254261)
                  ·
                    refine ⟨1323910423531442609180087, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14121711184335387831254261 1323910423531442609180087)
                    ·
                      rfl

theorem cell23_7734919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 3, 2, 1, 5].length) (baseStart_7734919 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7734919 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7734919 prefixEnd_7734919 := by exact prefixLift 7734919
  have htrace : WordTrace (prefixWord ++ tailWord_7734919) baseStart_7734919 baseEnd_7734919 := by
    simpa [prefixWord, tailWord_7734919, baseEnd_7734919] using wordTrace_append hprefix tailTrace_7734919
  have hstable : (prefixWord ++ tailWord_7734919).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7734919).length < 2 ^ (prefixWord ++ tailWord_7734919).sum := by decide
  have hdescent : baseEnd_7734919 < baseStart_7734919 := by decide
  rcases family_descends (prefixWord ++ tailWord_7734919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7734926 : List Nat := [4, 1, 1, 3, 1, 2, 1, 3, 2, 3, 2]
def baseStart_7734926 : Nat := 118140960795 + 7734926 * 2 ^ 59
def prefixEnd_7734926 : Nat := 4983230072969 + 3 ^ 40 * 7734926 * 2
def baseEnd_7734926 : Nat := 3971734864958909300152729

theorem tailTrace_7734926 : CollatzResearch.WordTrace tailWord_7734926 prefixEnd_7734926 3971734864958909300152729 := by
  unfold tailWord_7734926
  simp only [CollatzResearch.WordTrace]
  refine ⟨35264490996961449629265079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 188077285317127731356080421 35264490996961449629265079)
  ·
    refine ⟨52896736495442174443897619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35264490996961449629265079 52896736495442174443897619)
    ·
      refine ⟨79345104743163261665846429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52896736495442174443897619 79345104743163261665846429)
      ·
        refine ⟨29754414278686223124692411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 79345104743163261665846429 29754414278686223124692411)
        ·
          refine ⟨44631621418029334687038617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29754414278686223124692411 44631621418029334687038617)
          ·
            refine ⟨33473716063522001015278963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44631621418029334687038617 33473716063522001015278963)
            ·
              refine ⟨50210574095283001522918445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33473716063522001015278963 50210574095283001522918445)
              ·
                refine ⟨18828965285731125571094417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 50210574095283001522918445 18828965285731125571094417)
                ·
                  refine ⟨14121723964298344178320813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18828965285731125571094417 14121723964298344178320813)
                  ·
                    refine ⟨5295646486611879066870305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14121723964298344178320813 5295646486611879066870305)
                    ·
                      refine ⟨3971734864958909300152729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5295646486611879066870305 3971734864958909300152729)
                      ·
                        rfl

theorem cell23_7734926_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 1, 3, 2, 3, 2].length) (baseStart_7734926 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7734926 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7734926 prefixEnd_7734926 := by exact prefixLift 7734926
  have htrace : WordTrace (prefixWord ++ tailWord_7734926) baseStart_7734926 baseEnd_7734926 := by
    simpa [prefixWord, tailWord_7734926, baseEnd_7734926] using wordTrace_append hprefix tailTrace_7734926
  have hstable : (prefixWord ++ tailWord_7734926).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7734926).length < 2 ^ (prefixWord ++ tailWord_7734926).sum := by decide
  have hdescent : baseEnd_7734926 < baseStart_7734926 := by decide
  rcases family_descends (prefixWord ++ tailWord_7734926) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7734936 : List Nat := [2, 1, 2, 4, 1, 3, 3, 1, 1, 5]
def baseStart_7734936 : Nat := 118140960795 + 7734936 * 2 ^ 59
def prefixEnd_7734936 : Nat := 4983230072969 + 3 ^ 40 * 7734936 * 2
def baseEnd_7734936 : Nat := 1323913333255151420342561

theorem tailTrace_7734936 : CollatzResearch.WordTrace tailWord_7734936 prefixEnd_7734936 1323913333255151420342561 := by
  unfold tailWord_7734936
  simp only [CollatzResearch.WordTrace]
  refine ⟨141058146352827684370992331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 188077528470436912494656441 141058146352827684370992331)
  ·
    refine ⟨211587219529241526556488497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141058146352827684370992331 211587219529241526556488497)
    ·
      refine ⟨158690414646931144917366373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 211587219529241526556488497 158690414646931144917366373)
      ·
        refine ⟨29754452746299589672006195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 158690414646931144917366373 29754452746299589672006195)
        ·
          refine ⟨44631679119449384508009293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29754452746299589672006195 44631679119449384508009293)
          ·
            refine ⟨16736879669793519190503485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44631679119449384508009293 16736879669793519190503485)
            ·
              refine ⟨6276329876172569696438807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16736879669793519190503485 6276329876172569696438807)
              ·
                refine ⟨9414494814258854544658211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6276329876172569696438807 9414494814258854544658211)
                ·
                  refine ⟨14121742221388281816987317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9414494814258854544658211 14121742221388281816987317)
                  ·
                    refine ⟨1323913333255151420342561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14121742221388281816987317 1323913333255151420342561)
                    ·
                      rfl

theorem cell23_7734936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 3, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 3, 3, 1, 1, 5].length) (baseStart_7734936 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7734936 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7734936 prefixEnd_7734936 := by exact prefixLift 7734936
  have htrace : WordTrace (prefixWord ++ tailWord_7734936) baseStart_7734936 baseEnd_7734936 := by
    simpa [prefixWord, tailWord_7734936, baseEnd_7734936] using wordTrace_append hprefix tailTrace_7734936
  have hstable : (prefixWord ++ tailWord_7734936).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7734936).length < 2 ^ (prefixWord ++ tailWord_7734936).sum := by decide
  have hdescent : baseEnd_7734936 < baseStart_7734936 := by decide
  rcases family_descends (prefixWord ++ tailWord_7734936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7734949 : List Nat := [1, 3, 1, 2, 1, 2, 3, 4, 2, 4]
def baseStart_7734949 : Nat := 118140960795 + 7734949 * 2 ^ 59
def prefixEnd_7734949 : Nat := 4983230072969 + 3 ^ 40 * 7734949 * 2
def baseEnd_7734949 : Nat := 1323915558337987570055041

theorem tailTrace_7734949 : CollatzResearch.WordTrace tailWord_7734949 prefixEnd_7734949 1323915558337987570055041 := by
  unfold tailWord_7734949
  simp only [CollatzResearch.WordTrace]
  refine ⟨282116766854608271962207901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188077844569738847974805267 282116766854608271962207901)
  ·
    refine ⟨105793787570478101985827963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 282116766854608271962207901 105793787570478101985827963)
    ·
      refine ⟨158690681355717152978741945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105793787570478101985827963 158690681355717152978741945)
      ·
        refine ⟨119018011016787864734056459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 158690681355717152978741945 119018011016787864734056459)
        ·
          refine ⟨178527016525181797101084689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 119018011016787864734056459 178527016525181797101084689)
          ·
            refine ⟨133895262393886347825813517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 178527016525181797101084689 133895262393886347825813517)
            ·
              refine ⟨50210723397707380434680069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 133895262393886347825813517 50210723397707380434680069)
              ·
                refine ⟨9414510637070133831502513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 50210723397707380434680069 9414510637070133831502513)
                ·
                  refine ⟨7060882977802600373626885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9414510637070133831502513 7060882977802600373626885)
                  ·
                    refine ⟨1323915558337987570055041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7060882977802600373626885 1323915558337987570055041)
                    ·
                      rfl

theorem cell23_7734949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 3, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 3, 4, 2, 4].length) (baseStart_7734949 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7734949 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7734949 prefixEnd_7734949 := by exact prefixLift 7734949
  have htrace : WordTrace (prefixWord ++ tailWord_7734949) baseStart_7734949 baseEnd_7734949 := by
    simpa [prefixWord, tailWord_7734949, baseEnd_7734949] using wordTrace_append hprefix tailTrace_7734949
  have hstable : (prefixWord ++ tailWord_7734949).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7734949).length < 2 ^ (prefixWord ++ tailWord_7734949).sum := by decide
  have hdescent : baseEnd_7734949 < baseStart_7734949 := by decide
  rcases family_descends (prefixWord ++ tailWord_7734949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7734962 : List Nat := [3, 2, 1, 1, 1, 2, 5, 8]
def baseStart_7734962 : Nat := 118140960795 + 7734962 * 2 ^ 59
def prefixEnd_7734962 : Nat := 4983230072969 + 3 ^ 40 * 7734962 * 2
def baseEnd_7734962 : Nat := 147101975935647079974169

theorem tailTrace_7734962 : CollatzResearch.WordTrace tailWord_7734962 prefixEnd_7734962 147101975935647079974169 := by
  unfold tailWord_7734962
  simp only [CollatzResearch.WordTrace]
  refine ⟨70529310250890293795607785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 188078160669040783454954093 70529310250890293795607785)
  ·
    refine ⟨52896982688167720346705839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70529310250890293795607785 52896982688167720346705839)
    ·
      refine ⟨79345474032251580520058759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52896982688167720346705839 79345474032251580520058759)
      ·
        refine ⟨119018211048377370780088139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79345474032251580520058759 119018211048377370780088139)
        ·
          refine ⟨178527316572566056170132209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 119018211048377370780088139 178527316572566056170132209)
          ·
            refine ⟨133895487429424542127599157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 178527316572566056170132209 133895487429424542127599157)
            ·
              refine ⟨12552701946508550824462421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 133895487429424542127599157 12552701946508550824462421)
              ·
                refine ⟨147101975935647079974169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 12552701946508550824462421 147101975935647079974169)
                ·
                  rfl

theorem cell23_7734962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 5, 8].length) (baseStart_7734962 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7734962 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7734962 prefixEnd_7734962 := by exact prefixLift 7734962
  have htrace : WordTrace (prefixWord ++ tailWord_7734962) baseStart_7734962 baseEnd_7734962 := by
    simpa [prefixWord, tailWord_7734962, baseEnd_7734962] using wordTrace_append hprefix tailTrace_7734962
  have hstable : (prefixWord ++ tailWord_7734962).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7734962).length < 2 ^ (prefixWord ++ tailWord_7734962).sum := by decide
  have hdescent : baseEnd_7734962 < baseStart_7734962 := by decide
  rcases family_descends (prefixWord ++ tailWord_7734962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7734966 : List Nat := [5, 1, 3, 1, 1, 1, 1, 3, 1, 6]
def baseStart_7734966 : Nat := 118140960795 + 7734966 * 2 ^ 59
def prefixEnd_7734966 : Nat := 4983230072969 + 3 ^ 40 * 7734966 * 2
def baseEnd_7734966 : Nat := 1323918468061696381217515

theorem tailTrace_7734966 : CollatzResearch.WordTrace tailWord_7734966 prefixEnd_7734966 1323918468061696381217515 := by
  unfold tailWord_7734966
  simp only [CollatzResearch.WordTrace]
  refine ⟨17632336680971667741598547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 188078257930364455910384501 17632336680971667741598547)
  ·
    refine ⟨26448505021457501612397821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17632336680971667741598547 26448505021457501612397821)
    ·
      refine ⟨9918189383046563104649183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26448505021457501612397821 9918189383046563104649183)
      ·
        refine ⟨14877284074569844656973775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9918189383046563104649183 14877284074569844656973775)
        ·
          refine ⟨22315926111854766985460663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14877284074569844656973775 22315926111854766985460663)
          ·
            refine ⟨33473889167782150478190995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22315926111854766985460663 33473889167782150478190995)
            ·
              refine ⟨50210833751673225717286493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33473889167782150478190995 50210833751673225717286493)
              ·
                refine ⟨18829062656877459643982435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 50210833751673225717286493 18829062656877459643982435)
                ·
                  refine ⟨28243593985316189465973653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18829062656877459643982435 28243593985316189465973653)
                  ·
                    refine ⟨1323918468061696381217515, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28243593985316189465973653 1323918468061696381217515)
                    ·
                      rfl

theorem cell23_7734966_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 1, 3, 1, 6].length) (baseStart_7734966 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7734966 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7734966 prefixEnd_7734966 := by exact prefixLift 7734966
  have htrace : WordTrace (prefixWord ++ tailWord_7734966) baseStart_7734966 baseEnd_7734966 := by
    simpa [prefixWord, tailWord_7734966, baseEnd_7734966] using wordTrace_append hprefix tailTrace_7734966
  have hstable : (prefixWord ++ tailWord_7734966).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7734966).length < 2 ^ (prefixWord ++ tailWord_7734966).sum := by decide
  have hdescent : baseEnd_7734966 < baseStart_7734966 := by decide
  rcases family_descends (prefixWord ++ tailWord_7734966) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7734990 : List Nat := [4, 1, 1, 1, 3, 1, 4, 3, 1, 2, 2]
def baseStart_7734990 : Nat := 118140960795 + 7734990 * 2 ^ 59
def prefixEnd_7734990 : Nat := 4983230072969 + 3 ^ 40 * 7734990 * 2
def baseEnd_7734990 : Nat := 3971767727720797049752435

theorem tailTrace_7734990 : CollatzResearch.WordTrace tailWord_7734990 prefixEnd_7734990 3971767727720797049752435 := by
  unfold tailWord_7734990
  simp only [CollatzResearch.WordTrace]
  refine ⟨35264782780932466995556303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 188078841498306490642966949 35264782780932466995556303)
  ·
    refine ⟨52897174171398700493334455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35264782780932466995556303 52897174171398700493334455)
    ·
      refine ⟨79345761257098050740001683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52897174171398700493334455 79345761257098050740001683)
      ·
        refine ⟨119018641885647076110002525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79345761257098050740001683 119018641885647076110002525)
        ·
          refine ⟨44631990707117653541250947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 119018641885647076110002525 44631990707117653541250947)
          ·
            refine ⟨66947986060676480311876421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44631990707117653541250947 66947986060676480311876421)
            ·
              refine ⟨12552747386376840058476829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 66947986060676480311876421 12552747386376840058476829)
              ·
                refine ⟨4707280269891315021928811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12552747386376840058476829 4707280269891315021928811)
                ·
                  refine ⟨7060920404836972532893217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4707280269891315021928811 7060920404836972532893217)
                  ·
                    refine ⟨5295690303627729399669913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7060920404836972532893217 5295690303627729399669913)
                    ·
                      refine ⟨3971767727720797049752435, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5295690303627729399669913 3971767727720797049752435)
                      ·
                        rfl

theorem cell23_7734990_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 4, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 4, 3, 1, 2, 2].length) (baseStart_7734990 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7734990 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7734990 prefixEnd_7734990 := by exact prefixLift 7734990
  have htrace : WordTrace (prefixWord ++ tailWord_7734990) baseStart_7734990 baseEnd_7734990 := by
    simpa [prefixWord, tailWord_7734990, baseEnd_7734990] using wordTrace_append hprefix tailTrace_7734990
  have hstable : (prefixWord ++ tailWord_7734990).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7734990).length < 2 ^ (prefixWord ++ tailWord_7734990).sum := by decide
  have hdescent : baseEnd_7734990 < baseStart_7734990 := by decide
  rcases family_descends (prefixWord ++ tailWord_7734990) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7734993 : List Nat := [1, 2, 2, 1, 2, 6, 2, 1, 1, 2, 3]
def baseStart_7734993 : Nat := 118140960795 + 7734993 * 2 ^ 59
def prefixEnd_7734993 : Nat := 4983230072969 + 3 ^ 40 * 7734993 * 2
def baseEnd_7734993 : Nat := 3971769268162760538014921

theorem tailTrace_7734993 : CollatzResearch.WordTrace tailWord_7734993 prefixEnd_7734993 3971769268162760538014921 := by
  unfold tailWord_7734993
  simp only [CollatzResearch.WordTrace]
  refine ⟨282118371666448867476809633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188078914444299244984539755 282118371666448867476809633)
  ·
    refine ⟨211588778749836650607607225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 282118371666448867476809633 211588778749836650607607225)
    ·
      refine ⟨158691584062377487955705419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 211588778749836650607607225 158691584062377487955705419)
      ·
        refine ⟨238037376093566231933558129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 158691584062377487955705419 238037376093566231933558129)
        ·
          refine ⟨178528032070174673950168597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 238037376093566231933558129 178528032070174673950168597)
          ·
            refine ⟨8368501503289437841414153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 178528032070174673950168597 8368501503289437841414153)
            ·
              refine ⟨6276376127467078381060615, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8368501503289437841414153 6276376127467078381060615)
              ·
                refine ⟨9414564191200617571590923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6276376127467078381060615 9414564191200617571590923)
                ·
                  refine ⟨14121846286800926357386385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9414564191200617571590923 14121846286800926357386385)
                  ·
                    refine ⟨10591384715100694768039789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14121846286800926357386385 10591384715100694768039789)
                    ·
                      refine ⟨3971769268162760538014921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10591384715100694768039789 3971769268162760538014921)
                      ·
                        rfl

theorem cell23_7734993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 6, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 6, 2, 1, 1, 2, 3].length) (baseStart_7734993 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7734993 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7734993 prefixEnd_7734993 := by exact prefixLift 7734993
  have htrace : WordTrace (prefixWord ++ tailWord_7734993) baseStart_7734993 baseEnd_7734993 := by
    simpa [prefixWord, tailWord_7734993, baseEnd_7734993] using wordTrace_append hprefix tailTrace_7734993
  have hstable : (prefixWord ++ tailWord_7734993).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7734993).length < 2 ^ (prefixWord ++ tailWord_7734993).sum := by decide
  have hdescent : baseEnd_7734993 < baseStart_7734993 := by decide
  rcases family_descends (prefixWord ++ tailWord_7734993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7735023 : List Nat := [1, 1, 2, 1, 5, 1, 5, 1, 2, 1, 3]
def baseStart_7735023 : Nat := 118140960795 + 7735023 * 2 ^ 59
def prefixEnd_7735023 : Nat := 4983230072969 + 3 ^ 40 * 7735023 * 2
def baseEnd_7735023 : Nat := 3971784672582395420639783

theorem tailTrace_7735023 : CollatzResearch.WordTrace tailWord_7735023 prefixEnd_7735023 3971784672582395420639783 := by
  unfold tailWord_7735023
  simp only [CollatzResearch.WordTrace]
  refine ⟨282119465856340182600401723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188079643904226788400267815 282119465856340182600401723)
  ·
    refine ⟨423179198784510273900602585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 282119465856340182600401723 423179198784510273900602585)
    ·
      refine ⟨317384399088382705425451939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 423179198784510273900602585 317384399088382705425451939)
      ·
        refine ⟨476076598632574058138177909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 317384399088382705425451939 476076598632574058138177909)
        ·
          refine ⟨44632181121803817950454179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 476076598632574058138177909 44632181121803817950454179)
          ·
            refine ⟨66948271682705726925681269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44632181121803817950454179 66948271682705726925681269)
            ·
              refine ⟨6276400470253661899282619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 66948271682705726925681269 6276400470253661899282619)
              ·
                refine ⟨9414600705380492848923929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6276400470253661899282619 9414600705380492848923929)
                ·
                  refine ⟨7060950529035369636692947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9414600705380492848923929 7060950529035369636692947)
                  ·
                    refine ⟨10591425793553054455039421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7060950529035369636692947 10591425793553054455039421)
                    ·
                      refine ⟨3971784672582395420639783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10591425793553054455039421 3971784672582395420639783)
                      ·
                        rfl

theorem cell23_7735023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 5, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 5, 1, 2, 1, 3].length) (baseStart_7735023 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7735023 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7735023 prefixEnd_7735023 := by exact prefixLift 7735023
  have htrace : WordTrace (prefixWord ++ tailWord_7735023) baseStart_7735023 baseEnd_7735023 := by
    simpa [prefixWord, tailWord_7735023, baseEnd_7735023] using wordTrace_append hprefix tailTrace_7735023
  have hstable : (prefixWord ++ tailWord_7735023).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7735023).length < 2 ^ (prefixWord ++ tailWord_7735023).sum := by decide
  have hdescent : baseEnd_7735023 < baseStart_7735023 := by decide
  rcases family_descends (prefixWord ++ tailWord_7735023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7735052 : List Nat := [2, 2, 1, 2, 2, 1, 2, 2, 9]
def baseStart_7735052 : Nat := 118140960795 + 7735052 * 2 ^ 59
def prefixEnd_7735052 : Nat := 4983230072969 + 3 ^ 40 * 7735052 * 2
def baseEnd_7735052 : Nat := 441311062613486200797461

theorem tailTrace_7735052 : CollatzResearch.WordTrace tailWord_7735052 prefixEnd_7735052 441311062613486200797461 := by
  unfold tailWord_7735052
  simp only [CollatzResearch.WordTrace]
  refine ⟨141060261786617560276603705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 188080349048823413702138273 141060261786617560276603705)
  ·
    refine ⟨105795196339963170207452779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 141060261786617560276603705 105795196339963170207452779)
    ·
      refine ⟨158692794509944755311179169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105795196339963170207452779 158692794509944755311179169)
      ·
        refine ⟨119019595882458566483384377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 158692794509944755311179169 119019595882458566483384377)
        ·
          refine ⟨89264696911843924862538283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 119019595882458566483384377 89264696911843924862538283)
          ·
            refine ⟨133897045367765887293807425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89264696911843924862538283 133897045367765887293807425)
            ·
              refine ⟨100422784025824415470355569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 133897045367765887293807425 100422784025824415470355569)
              ·
                refine ⟨75317088019368311602766677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 100422784025824415470355569 75317088019368311602766677)
                ·
                  refine ⟨441311062613486200797461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 75317088019368311602766677 441311062613486200797461)
                  ·
                    rfl

theorem cell23_7735052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 2, 2, 9].length) (baseStart_7735052 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7735052 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7735052 prefixEnd_7735052 := by exact prefixLift 7735052
  have htrace : WordTrace (prefixWord ++ tailWord_7735052) baseStart_7735052 baseEnd_7735052 := by
    simpa [prefixWord, tailWord_7735052, baseEnd_7735052] using wordTrace_append hprefix tailTrace_7735052
  have hstable : (prefixWord ++ tailWord_7735052).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7735052).length < 2 ^ (prefixWord ++ tailWord_7735052).sum := by decide
  have hdescent : baseEnd_7735052 < baseStart_7735052 := by decide
  rcases family_descends (prefixWord ++ tailWord_7735052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7735063 : List Nat := [1, 1, 3, 4, 2, 1, 2, 1, 4, 2, 2]
def baseStart_7735063 : Nat := 118140960795 + 7735063 * 2 ^ 59
def prefixEnd_7735063 : Nat := 4983230072969 + 3 ^ 40 * 7735063 * 2
def baseEnd_7735063 : Nat := 3971805211808575264139599

theorem tailTrace_7735063 : CollatzResearch.WordTrace tailWord_7735063 prefixEnd_7735063 3971805211808575264139599 := by
  unfold tailWord_7735063
  simp only [CollatzResearch.WordTrace]
  refine ⟨282120924776195269431857843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188080616517463512954571895 282120924776195269431857843)
  ·
    refine ⟨423181387164292904147786765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 282120924776195269431857843 423181387164292904147786765)
    ·
      refine ⟨158693020186609839055420037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 423181387164292904147786765 158693020186609839055420037)
      ·
        refine ⟨29754941284989344822891257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 158693020186609839055420037 29754941284989344822891257)
        ·
          refine ⟨22316205963742008617168443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29754941284989344822891257 22316205963742008617168443)
          ·
            refine ⟨33474308945613012925752665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22316205963742008617168443 33474308945613012925752665)
            ·
              refine ⟨25105731709209759694314499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33474308945613012925752665 25105731709209759694314499)
              ·
                refine ⟨37658597563814639541471749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25105731709209759694314499 37658597563814639541471749)
                ·
                  refine ⟨7060987043215244914025953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 37658597563814639541471749 7060987043215244914025953)
                  ·
                    refine ⟨5295740282411433685519465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7060987043215244914025953 5295740282411433685519465)
                    ·
                      refine ⟨3971805211808575264139599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5295740282411433685519465 3971805211808575264139599)
                      ·
                        rfl

theorem cell23_7735063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 2, 1, 4, 2, 2].length) (baseStart_7735063 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7735063 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7735063 prefixEnd_7735063 := by exact prefixLift 7735063
  have htrace : WordTrace (prefixWord ++ tailWord_7735063) baseStart_7735063 baseEnd_7735063 := by
    simpa [prefixWord, tailWord_7735063, baseEnd_7735063] using wordTrace_append hprefix tailTrace_7735063
  have hstable : (prefixWord ++ tailWord_7735063).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7735063).length < 2 ^ (prefixWord ++ tailWord_7735063).sum := by decide
  have hdescent : baseEnd_7735063 < baseStart_7735063 := by decide
  rcases family_descends (prefixWord ++ tailWord_7735063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7735080 : List Nat := [2, 1, 5, 1, 1, 3, 1, 3, 2, 2, 2]
def baseStart_7735080 : Nat := 118140960795 + 7735080 * 2 ^ 59
def prefixEnd_7735080 : Nat := 4983230072969 + 3 ^ 40 * 7735080 * 2
def baseEnd_7735080 : Nat := 3971813940979701697627021

theorem tailTrace_7735080 : CollatzResearch.WordTrace tailWord_7735080 prefixEnd_7735080 3971813940979701697627021 := by
  unfold tailWord_7735080
  simp only [CollatzResearch.WordTrace]
  refine ⟨141060772408566840667613347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 188081029878089120890151129 141060772408566840667613347)
  ·
    refine ⟨211591158612850261001420021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141060772408566840667613347 211591158612850261001420021)
    ·
      refine ⟨19836671119954711968883127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 211591158612850261001420021 19836671119954711968883127)
      ·
        refine ⟨29755006679932067953324691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19836671119954711968883127 29755006679932067953324691)
        ·
          refine ⟨44632510019898101929987037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29755006679932067953324691 44632510019898101929987037)
          ·
            refine ⟨16737191257461788223745139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44632510019898101929987037 16737191257461788223745139)
            ·
              refine ⟨25105786886192682335617709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16737191257461788223745139 25105786886192682335617709)
              ·
                refine ⟨9414670082322255875856641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25105786886192682335617709 9414670082322255875856641)
                ·
                  refine ⟨7061002561741691906892481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9414670082322255875856641 7061002561741691906892481)
                  ·
                    refine ⟨5295751921306268930169361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7061002561741691906892481 5295751921306268930169361)
                    ·
                      refine ⟨3971813940979701697627021, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5295751921306268930169361 3971813940979701697627021)
                      ·
                        rfl

theorem cell23_7735080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 3, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 3, 1, 3, 2, 2, 2].length) (baseStart_7735080 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7735080 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7735080 prefixEnd_7735080 := by exact prefixLift 7735080
  have htrace : WordTrace (prefixWord ++ tailWord_7735080) baseStart_7735080 baseEnd_7735080 := by
    simpa [prefixWord, tailWord_7735080, baseEnd_7735080] using wordTrace_append hprefix tailTrace_7735080
  have hstable : (prefixWord ++ tailWord_7735080).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7735080).length < 2 ^ (prefixWord ++ tailWord_7735080).sum := by decide
  have hdescent : baseEnd_7735080 < baseStart_7735080 := by decide
  rcases family_descends (prefixWord ++ tailWord_7735080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7735136 : List Nat := [2, 1, 1, 3, 3, 2, 1, 1, 1, 6, 2]
def baseStart_7735136 : Nat := 118140960795 + 7735136 * 2 ^ 59
def prefixEnd_7735136 : Nat := 4983230072969 + 3 ^ 40 * 7735136 * 2
def baseEnd_7735136 : Nat := 3971842695896353478526763

theorem tailTrace_7735136 : CollatzResearch.WordTrace tailWord_7735136 prefixEnd_7735136 3971842695896353478526763 := by
  unfold tailWord_7735136
  simp only [CollatzResearch.WordTrace]
  refine ⟨141061793652465401449632631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 188082391536620535266176841 141061793652465401449632631)
  ·
    refine ⟨211592690478698102174448947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141061793652465401449632631 211592690478698102174448947)
    ·
      refine ⟨317389035718047153261673421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 211592690478698102174448947 317389035718047153261673421)
      ·
        refine ⟨119020888394267682473127533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 317389035718047153261673421 119020888394267682473127533)
        ·
          refine ⟨44632833147850380927422825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 119020888394267682473127533 44632833147850380927422825)
          ·
            refine ⟨33474624860887785695567119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44632833147850380927422825 33474624860887785695567119)
            ·
              refine ⟨50211937291331678543350679, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33474624860887785695567119 50211937291331678543350679)
              ·
                refine ⟨75317905936997517815026019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50211937291331678543350679 75317905936997517815026019)
                ·
                  refine ⟨112976858905496276722539029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 75317905936997517815026019 112976858905496276722539029)
                  ·
                    refine ⟨5295790261195137971369017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 112976858905496276722539029 5295790261195137971369017)
                    ·
                      refine ⟨3971842695896353478526763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5295790261195137971369017 3971842695896353478526763)
                      ·
                        rfl

theorem cell23_7735136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 1, 1, 1, 6, 2].length) (baseStart_7735136 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7735136 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7735136 prefixEnd_7735136 := by exact prefixLift 7735136
  have htrace : WordTrace (prefixWord ++ tailWord_7735136) baseStart_7735136 baseEnd_7735136 := by
    simpa [prefixWord, tailWord_7735136, baseEnd_7735136] using wordTrace_append hprefix tailTrace_7735136
  have hstable : (prefixWord ++ tailWord_7735136).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7735136).length < 2 ^ (prefixWord ++ tailWord_7735136).sum := by decide
  have hdescent : baseEnd_7735136 < baseStart_7735136 := by decide
  rcases family_descends (prefixWord ++ tailWord_7735136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7735176 : List Nat := [2, 1, 3, 3, 3, 1, 1, 1, 8]
def baseStart_7735176 : Nat := 118140960795 + 7735176 * 2 ^ 59
def prefixEnd_7735176 : Nat := 4983230072969 + 3 ^ 40 * 7735176 * 2
def baseEnd_7735176 : Nat := 441318137235837035780731

theorem tailTrace_7735176 : CollatzResearch.WordTrace tailWord_7735176 prefixEnd_7735176 441318137235837035780731 := by
  unfold tailWord_7735176
  simp only [CollatzResearch.WordTrace]
  refine ⟨141062523112392944865360691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 188083364149857259820480921 141062523112392944865360691)
  ·
    refine ⟨211593784668589417298041037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141062523112392944865360691 211593784668589417298041037)
    ·
      refine ⟨79347669250721031486765389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 211593784668589417298041037 79347669250721031486765389)
      ·
        refine ⟨29755375969020386807537021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 79347669250721031486765389 29755375969020386807537021)
        ·
          refine ⟨11158265988382645052826383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29755375969020386807537021 11158265988382645052826383)
          ·
            refine ⟨16737398982573967579239575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11158265988382645052826383 16737398982573967579239575)
            ·
              refine ⟨25106098473860951368859363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16737398982573967579239575 25106098473860951368859363)
              ·
                refine ⟨37659147710791427053289045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25106098473860951368859363 37659147710791427053289045)
                ·
                  refine ⟨441318137235837035780731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 37659147710791427053289045 441318137235837035780731)
                  ·
                    rfl

theorem cell23_7735176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 3, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 3, 1, 1, 1, 8].length) (baseStart_7735176 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7735176 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7735176 prefixEnd_7735176 := by exact prefixLift 7735176
  have htrace : WordTrace (prefixWord ++ tailWord_7735176) baseStart_7735176 baseEnd_7735176 := by
    simpa [prefixWord, tailWord_7735176, baseEnd_7735176] using wordTrace_append hprefix tailTrace_7735176
  have hstable : (prefixWord ++ tailWord_7735176).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7735176).length < 2 ^ (prefixWord ++ tailWord_7735176).sum := by decide
  have hdescent : baseEnd_7735176 < baseStart_7735176 := by decide
  rcases family_descends (prefixWord ++ tailWord_7735176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7735219 : List Nat := [1, 1, 1, 2, 3, 1, 4, 1, 3, 6]
def baseStart_7735219 : Nat := 118140960795 + 7735219 * 2 ^ 59
def prefixEnd_7735219 : Nat := 4983230072969 + 3 ^ 40 * 7735219 * 2
def baseEnd_7735219 : Nat := 1323961771596892217929627

theorem tailTrace_7735219 : CollatzResearch.WordTrace tailWord_7735219 prefixEnd_7735219 1323961771596892217929627 := by
  unfold tailWord_7735219
  simp only [CollatzResearch.WordTrace]
  refine ⟨282126614563630108074536711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188084409709086738716357807 282126614563630108074536711)
  ·
    refine ⟨423189921845445162111805067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 282126614563630108074536711 423189921845445162111805067)
    ·
      refine ⟨634784882768167743167707601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 423189921845445162111805067 634784882768167743167707601)
      ·
        refine ⟨476088662076125807375780701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 634784882768167743167707601 476088662076125807375780701)
        ·
          refine ⟨178533248278547177765917763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 476088662076125807375780701 178533248278547177765917763)
          ·
            refine ⟨267799872417820766648876645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 178533248278547177765917763 267799872417820766648876645)
            ·
              refine ⟨50212476078341393746664371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 267799872417820766648876645 50212476078341393746664371)
              ·
                refine ⟨75318714117512090619996557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50212476078341393746664371 75318714117512090619996557)
                ·
                  refine ⟨28244517794067033982498709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 75318714117512090619996557 28244517794067033982498709)
                  ·
                    refine ⟨1323961771596892217929627, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28244517794067033982498709 1323961771596892217929627)
                    ·
                      rfl

theorem cell23_7735219_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 4, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 4, 1, 3, 6].length) (baseStart_7735219 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7735219 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7735219 prefixEnd_7735219 := by exact prefixLift 7735219
  have htrace : WordTrace (prefixWord ++ tailWord_7735219) baseStart_7735219 baseEnd_7735219 := by
    simpa [prefixWord, tailWord_7735219, baseEnd_7735219] using wordTrace_append hprefix tailTrace_7735219
  have hstable : (prefixWord ++ tailWord_7735219).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7735219).length < 2 ^ (prefixWord ++ tailWord_7735219).sum := by decide
  have hdescent : baseEnd_7735219 < baseStart_7735219 := by decide
  rcases family_descends (prefixWord ++ tailWord_7735219) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7735230 : List Nat := [4, 2, 1, 1, 1, 4, 1, 2, 2, 3, 2]
def baseStart_7735230 : Nat := 118140960795 + 7735230 * 2 ^ 59
def prefixEnd_7735230 : Nat := 4983230072969 + 3 ^ 40 * 7735230 * 2
def baseEnd_7735230 : Nat := 3971890963077876110751331

theorem tailTrace_7735230 : CollatzResearch.WordTrace tailWord_7735230 prefixEnd_7735230 3971890963077876110751331 := by
  unfold tailWord_7735230
  simp only [CollatzResearch.WordTrace]
  refine ⟨35265876970823782119148393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 188084677177726837968791429 35265876970823782119148393)
  ·
    refine ⟨26449407728117836589361295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35265876970823782119148393 26449407728117836589361295)
    ·
      refine ⟨39674111592176754884041943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26449407728117836589361295 39674111592176754884041943)
      ·
        refine ⟨59511167388265132326062915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39674111592176754884041943 59511167388265132326062915)
        ·
          refine ⟨89266751082397698489094373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59511167388265132326062915 89266751082397698489094373)
          ·
            refine ⟨16737515827949568466705195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 89266751082397698489094373 16737515827949568466705195)
            ·
              refine ⟨25106273741924352700057793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16737515827949568466705195 25106273741924352700057793)
              ·
                refine ⟨18829705306443264525043345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25106273741924352700057793 18829705306443264525043345)
                ·
                  refine ⟨14122278979832448393782509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18829705306443264525043345 14122278979832448393782509)
                  ·
                    refine ⟨5295854617437168147668441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14122278979832448393782509 5295854617437168147668441)
                    ·
                      refine ⟨3971890963077876110751331, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5295854617437168147668441 3971890963077876110751331)
                      ·
                        rfl

theorem cell23_7735230_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 4, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 4, 1, 2, 2, 3, 2].length) (baseStart_7735230 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7735230 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7735230 prefixEnd_7735230 := by exact prefixLift 7735230
  have htrace : WordTrace (prefixWord ++ tailWord_7735230) baseStart_7735230 baseEnd_7735230 := by
    simpa [prefixWord, tailWord_7735230, baseEnd_7735230] using wordTrace_append hprefix tailTrace_7735230
  have hstable : (prefixWord ++ tailWord_7735230).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7735230).length < 2 ^ (prefixWord ++ tailWord_7735230).sum := by decide
  have hdescent : baseEnd_7735230 < baseStart_7735230 := by decide
  rcases family_descends (prefixWord ++ tailWord_7735230) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7735246 : List Nat := [4, 1, 1, 1, 2, 2, 1, 4, 1, 1, 5]
def baseStart_7735246 : Nat := 118140960795 + 7735246 * 2 ^ 59
def prefixEnd_7735246 : Nat := 4983230072969 + 3 ^ 40 * 7735246 * 2
def baseEnd_7735246 : Nat := 3971899178768348048151257

theorem tailTrace_7735246 : CollatzResearch.WordTrace tailWord_7735246 prefixEnd_7735246 3971899178768348048151257 := by
  unfold tailWord_7735246
  simp only [CollatzResearch.WordTrace]
  refine ⟨35265949916816536460721199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 188085066223021527790513061 35265949916816536460721199)
  ·
    refine ⟨52898924875224804691081799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35265949916816536460721199 52898924875224804691081799)
    ·
      refine ⟨79348387312837207036622699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52898924875224804691081799 79348387312837207036622699)
      ·
        refine ⟨119022580969255810554934049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79348387312837207036622699 119022580969255810554934049)
        ·
          refine ⟨89266935726941857916200537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 119022580969255810554934049 89266935726941857916200537)
          ·
            refine ⟨66950201795206393437150403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 89266935726941857916200537 66950201795206393437150403)
            ·
              refine ⟨100425302692809590155725605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66950201795206393437150403 100425302692809590155725605)
              ·
                refine ⟨18829744254901798154198551, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 100425302692809590155725605 18829744254901798154198551)
                ·
                  refine ⟨28244616382352697231297827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18829744254901798154198551 28244616382352697231297827)
                  ·
                    refine ⟨42366924573529045846946741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28244616382352697231297827 42366924573529045846946741)
                    ·
                      refine ⟨3971899178768348048151257, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42366924573529045846946741 3971899178768348048151257)
                      ·
                        rfl

theorem cell23_7735246_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 1, 4, 1, 1, 5].length) (baseStart_7735246 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7735246 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7735246 prefixEnd_7735246 := by exact prefixLift 7735246
  have htrace : WordTrace (prefixWord ++ tailWord_7735246) baseStart_7735246 baseEnd_7735246 := by
    simpa [prefixWord, tailWord_7735246, baseEnd_7735246] using wordTrace_append hprefix tailTrace_7735246
  have hstable : (prefixWord ++ tailWord_7735246).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7735246).length < 2 ^ (prefixWord ++ tailWord_7735246).sum := by decide
  have hdescent : baseEnd_7735246 < baseStart_7735246 := by decide
  rcases family_descends (prefixWord ++ tailWord_7735246) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7735256 : List Nat := [2, 1, 2, 2, 2, 2, 2, 3, 1, 2, 4]
def baseStart_7735256 : Nat := 118140960795 + 7735256 * 2 ^ 59
def prefixEnd_7735256 : Nat := 4983230072969 + 3 ^ 40 * 7735256 * 2
def baseEnd_7735256 : Nat := 3971904313574893009026211

theorem tailTrace_7735256 : CollatzResearch.WordTrace tailWord_7735256 prefixEnd_7735256 3971904313574893009026211 := by
  unfold tailWord_7735256
  simp only [CollatzResearch.WordTrace]
  refine ⟨141063982032248031696816811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 188085309376330708929089081 141063982032248031696816811)
  ·
    refine ⟨211595973048372047545225217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141063982032248031696816811 211595973048372047545225217)
    ·
      refine ⟨158696979786279035658918913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 211595973048372047545225217 158696979786279035658918913)
      ·
        refine ⟨119022734839709276744189185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 158696979786279035658918913 119022734839709276744189185)
        ·
          refine ⟨89267051129781957558141889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 119022734839709276744189185 89267051129781957558141889)
          ·
            refine ⟨66950288347336468168606417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 89267051129781957558141889 66950288347336468168606417)
            ·
              refine ⟨50212716260502351126454813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66950288347336468168606417 50212716260502351126454813)
              ·
                refine ⟨18829768597688381672420555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 50212716260502351126454813 18829768597688381672420555)
                ·
                  refine ⟨28244652896532572508630833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18829768597688381672420555 28244652896532572508630833)
                  ·
                    refine ⟨21183489672399429381473125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28244652896532572508630833 21183489672399429381473125)
                    ·
                      refine ⟨3971904313574893009026211, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21183489672399429381473125 3971904313574893009026211)
                      ·
                        rfl

theorem cell23_7735256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 2, 3, 1, 2, 4].length) (baseStart_7735256 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7735256 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7735256 prefixEnd_7735256 := by exact prefixLift 7735256
  have htrace : WordTrace (prefixWord ++ tailWord_7735256) baseStart_7735256 baseEnd_7735256 := by
    simpa [prefixWord, tailWord_7735256, baseEnd_7735256] using wordTrace_append hprefix tailTrace_7735256
  have hstable : (prefixWord ++ tailWord_7735256).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7735256).length < 2 ^ (prefixWord ++ tailWord_7735256).sum := by decide
  have hdescent : baseEnd_7735256 < baseStart_7735256 := by decide
  rcases family_descends (prefixWord ++ tailWord_7735256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7735263 : List Nat := [1, 1, 2, 3, 4, 2, 1, 1, 3, 2, 3]
def baseStart_7735263 : Nat := 118140960795 + 7735263 * 2 ^ 59
def prefixEnd_7735263 : Nat := 4983230072969 + 3 ^ 40 * 7735263 * 2
def baseEnd_7735263 : Nat := 3971907907939474481638679

theorem tailTrace_7735263 : CollatzResearch.WordTrace tailWord_7735263 prefixEnd_7735263 3971907907939474481638679 := by
  unfold tailWord_7735263
  simp only [CollatzResearch.WordTrace]
  refine ⟨282128219375470703589138443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188085479583647135726092295 282128219375470703589138443)
  ·
    refine ⟨423192329063206055383707665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 282128219375470703589138443 423192329063206055383707665)
    ·
      refine ⟨317394246797404541537780749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 423192329063206055383707665 317394246797404541537780749)
      ·
        refine ⟨119022842549026703076667781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 317394246797404541537780749 119022842549026703076667781)
        ·
          refine ⟨22316782977942506826875209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 119022842549026703076667781 22316782977942506826875209)
          ·
            refine ⟨16737587233456880120156407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22316782977942506826875209 16737587233456880120156407)
            ·
              refine ⟨25106380850185320180234611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16737587233456880120156407 25106380850185320180234611)
              ·
                refine ⟨37659571275277980270351917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25106380850185320180234611 37659571275277980270351917)
                ·
                  refine ⟨14122339228229242601381969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37659571275277980270351917 14122339228229242601381969)
                  ·
                    refine ⟨10591754421171931951036477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14122339228229242601381969 10591754421171931951036477)
                    ·
                      refine ⟨3971907907939474481638679, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10591754421171931951036477 3971907907939474481638679)
                      ·
                        rfl

theorem cell23_7735263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 2, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 2, 1, 1, 3, 2, 3].length) (baseStart_7735263 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7735263 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7735263 prefixEnd_7735263 := by exact prefixLift 7735263
  have htrace : WordTrace (prefixWord ++ tailWord_7735263) baseStart_7735263 baseEnd_7735263 := by
    simpa [prefixWord, tailWord_7735263, baseEnd_7735263] using wordTrace_append hprefix tailTrace_7735263
  have hstable : (prefixWord ++ tailWord_7735263).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7735263).length < 2 ^ (prefixWord ++ tailWord_7735263).sum := by decide
  have hdescent : baseEnd_7735263 < baseStart_7735263 := by decide
  rcases family_descends (prefixWord ++ tailWord_7735263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7735293 : List Nat := [1, 4, 1, 1, 1, 2, 2, 3, 4, 1, 3]
def baseStart_7735293 : Nat := 118140960795 + 7735293 * 2 ^ 59
def prefixEnd_7735293 : Nat := 4983230072969 + 3 ^ 40 * 7735293 * 2
def baseEnd_7735293 : Nat := 3971923312359109364263541

theorem tailTrace_7735293 : CollatzResearch.WordTrace tailWord_7735293 prefixEnd_7735293 3971923312359109364263541 := by
  unfold tailWord_7735293
  simp only [CollatzResearch.WordTrace]
  refine ⟨282129313565362018712730533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188086209043574679141820355 282129313565362018712730533)
  ·
    refine ⟨52899246293505378508636975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 282129313565362018712730533 52899246293505378508636975)
    ·
      refine ⟨79348869440258067762955463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52899246293505378508636975 79348869440258067762955463)
      ·
        refine ⟨119023304160387101644433195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79348869440258067762955463 119023304160387101644433195)
        ·
          refine ⟨178534956240580652466649793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 119023304160387101644433195 178534956240580652466649793)
          ·
            refine ⟨133901217180435489349987345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 178534956240580652466649793 133901217180435489349987345)
            ·
              refine ⟨100425912885326617012490509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 133901217180435489349987345 100425912885326617012490509)
              ·
                refine ⟨37659717331997481379683941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 100425912885326617012490509 37659717331997481379683941)
                ·
                  refine ⟨7061196999749527758690739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 37659717331997481379683941 7061196999749527758690739)
                  ·
                    refine ⟨10591795499624291638036109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7061196999749527758690739 10591795499624291638036109)
                    ·
                      refine ⟨3971923312359109364263541, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10591795499624291638036109 3971923312359109364263541)
                      ·
                        rfl

theorem cell23_7735293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 2, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 2, 3, 4, 1, 3].length) (baseStart_7735293 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7735293 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7735293 prefixEnd_7735293 := by exact prefixLift 7735293
  have htrace : WordTrace (prefixWord ++ tailWord_7735293) baseStart_7735293 baseEnd_7735293 := by
    simpa [prefixWord, tailWord_7735293, baseEnd_7735293] using wordTrace_append hprefix tailTrace_7735293
  have hstable : (prefixWord ++ tailWord_7735293).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7735293).length < 2 ^ (prefixWord ++ tailWord_7735293).sum := by decide
  have hdescent : baseEnd_7735293 < baseStart_7735293 := by decide
  rcases family_descends (prefixWord ++ tailWord_7735293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7735300 : List Nat := [2, 3, 2, 4, 1, 2, 1, 8]
def baseStart_7735300 : Nat := 118140960795 + 7735300 * 2 ^ 59
def prefixEnd_7735300 : Nat := 4983230072969 + 3 ^ 40 * 7735300 * 2
def baseEnd_7735300 : Nat := 147108403952729290254667

theorem tailTrace_7735300 : CollatzResearch.WordTrace tailWord_7735300 prefixEnd_7735300 147108403952729290254667 := by
  unfold tailWord_7735300
  simp only [CollatzResearch.WordTrace]
  refine ⟨141064784438168329454117677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 188086379250891105938823569 141064784438168329454117677)
  ·
    refine ⟨52899294164313123545294129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 141064784438168329454117677 52899294164313123545294129)
    ·
      refine ⟨39674470623234842658970597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52899294164313123545294129 39674470623234842658970597)
      ·
        refine ⟨7438963241856532998556987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 39674470623234842658970597 7438963241856532998556987)
        ·
          refine ⟨11158444862784799497835481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7438963241856532998556987 11158444862784799497835481)
          ·
            refine ⟨8368833647088599623376611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11158444862784799497835481 8368833647088599623376611)
            ·
              refine ⟨12553250470632899435064917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8368833647088599623376611 12553250470632899435064917)
              ·
                refine ⟨147108403952729290254667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 12553250470632899435064917 147108403952729290254667)
                ·
                  rfl

theorem cell23_7735300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 1, 2, 1, 8].length) (baseStart_7735300 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7735300 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7735300 prefixEnd_7735300 := by exact prefixLift 7735300
  have htrace : WordTrace (prefixWord ++ tailWord_7735300) baseStart_7735300 baseEnd_7735300 := by
    simpa [prefixWord, tailWord_7735300, baseEnd_7735300] using wordTrace_append hprefix tailTrace_7735300
  have hstable : (prefixWord ++ tailWord_7735300).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7735300).length < 2 ^ (prefixWord ++ tailWord_7735300).sum := by decide
  have hdescent : baseEnd_7735300 < baseStart_7735300 := by decide
  rcases family_descends (prefixWord ++ tailWord_7735300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7735310 : List Nat := [4, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3]
def baseStart_7735310 : Nat := 118140960795 + 7735310 * 2 ^ 59
def prefixEnd_7735310 : Nat := 4983230072969 + 3 ^ 40 * 7735310 * 2
def baseEnd_7735310 : Nat := 3971932041530235797750963

theorem tailTrace_7735310 : CollatzResearch.WordTrace tailWord_7735310 prefixEnd_7735310 3971932041530235797750963 := by
  unfold tailWord_7735310
  simp only [CollatzResearch.WordTrace]
  refine ⟨35266241700787553827012423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 188086622404200287077399589 35266241700787553827012423)
  ·
    refine ⟨52899362551181330740518635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35266241700787553827012423 52899362551181330740518635)
    ·
      refine ⟨79349043826771996110777953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52899362551181330740518635 79349043826771996110777953)
      ·
        refine ⟨59511782870078997083083465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79349043826771996110777953 59511782870078997083083465)
        ·
          refine ⟨44633837152559247812312599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59511782870078997083083465 44633837152559247812312599)
          ·
            refine ⟨66950755728838871718468899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44633837152559247812312599 66950755728838871718468899)
            ·
              refine ⟨100426133593258307577703349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66950755728838871718468899 100426133593258307577703349)
              ·
                refine ⟨9414950024367966335409689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 100426133593258307577703349 9414950024367966335409689)
                ·
                  refine ⟨7061212518275974751557267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9414950024367966335409689 7061212518275974751557267)
                  ·
                    refine ⟨10591818777413962127335901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7061212518275974751557267 10591818777413962127335901)
                    ·
                      refine ⟨3971932041530235797750963, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10591818777413962127335901 3971932041530235797750963)
                      ·
                        rfl

theorem cell23_7735310_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3].length) (baseStart_7735310 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7735310 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7735310 prefixEnd_7735310 := by exact prefixLift 7735310
  have htrace : WordTrace (prefixWord ++ tailWord_7735310) baseStart_7735310 baseEnd_7735310 := by
    simpa [prefixWord, tailWord_7735310, baseEnd_7735310] using wordTrace_append hprefix tailTrace_7735310
  have hstable : (prefixWord ++ tailWord_7735310).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7735310).length < 2 ^ (prefixWord ++ tailWord_7735310).sum := by decide
  have hdescent : baseEnd_7735310 < baseStart_7735310 := by decide
  rcases family_descends (prefixWord ++ tailWord_7735310) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7735320 : List Nat := [2, 1, 2, 3, 2, 1, 2, 4, 1, 3, 2]
def baseStart_7735320 : Nat := 118140960795 + 7735320 * 2 ^ 59
def prefixEnd_7735320 : Nat := 4983230072969 + 3 ^ 40 * 7735320 * 2
def baseEnd_7735320 : Nat := 3971937176336780758625917

theorem tailTrace_7735320 : CollatzResearch.WordTrace tailWord_7735320 prefixEnd_7735320 3971937176336780758625917 := by
  unfold tailWord_7735320
  simp only [CollatzResearch.WordTrace]
  refine ⟨141065149168132101161981707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 188086865557509468215975609 141065149168132101161981707)
  ·
    refine ⟨211597723752198151742972561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141065149168132101161981707 211597723752198151742972561)
    ·
      refine ⟨158698292814148613807229421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 211597723752198151742972561 158698292814148613807229421)
      ·
        refine ⟨59511859805305730177711033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 158698292814148613807229421 59511859805305730177711033)
        ·
          refine ⟨44633894853979297633283275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59511859805305730177711033 44633894853979297633283275)
          ·
            refine ⟨66950842280968946449924913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44633894853979297633283275 66950842280968946449924913)
            ·
              refine ⟨50213131710726709837443685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66950842280968946449924913 50213131710726709837443685)
              ·
                refine ⟨9414962195761258094520691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 50213131710726709837443685 9414962195761258094520691)
                ·
                  refine ⟨14122443293641887141781037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9414962195761258094520691 14122443293641887141781037)
                  ·
                    refine ⟨5295916235115707678167889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14122443293641887141781037 5295916235115707678167889)
                    ·
                      refine ⟨3971937176336780758625917, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5295916235115707678167889 3971937176336780758625917)
                      ·
                        rfl

theorem cell23_7735320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 2, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 2, 4, 1, 3, 2].length) (baseStart_7735320 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7735320 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7735320 prefixEnd_7735320 := by exact prefixLift 7735320
  have htrace : WordTrace (prefixWord ++ tailWord_7735320) baseStart_7735320 baseEnd_7735320 := by
    simpa [prefixWord, tailWord_7735320, baseEnd_7735320] using wordTrace_append hprefix tailTrace_7735320
  have hstable : (prefixWord ++ tailWord_7735320).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7735320).length < 2 ^ (prefixWord ++ tailWord_7735320).sum := by decide
  have hdescent : baseEnd_7735320 < baseStart_7735320 := by decide
  rcases family_descends (prefixWord ++ tailWord_7735320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7735373 : List Nat := [1, 6, 1, 1, 1, 1, 1, 4, 7]
def baseStart_7735373 : Nat := 118140960795 + 7735373 * 2 ^ 59
def prefixEnd_7735373 : Nat := 4983230072969 + 3 ^ 40 * 7735373 * 2
def baseEnd_7735373 : Nat := 441329376756829894584797

theorem tailTrace_7735373 : CollatzResearch.WordTrace tailWord_7735373 prefixEnd_7735373 441329376756829894584797 := by
  unfold tailWord_7735373
  simp only [CollatzResearch.WordTrace]
  refine ⟨282132231405072192375642773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188088154270048128250428515 282132231405072192375642773)
  ·
    refine ⟨13224948347112759017608255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 282132231405072192375642773 13224948347112759017608255)
    ·
      refine ⟨19837422520669138526412383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13224948347112759017608255 19837422520669138526412383)
      ·
        refine ⟨29756133781003707789618575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19837422520669138526412383 29756133781003707789618575)
        ·
          refine ⟨44634200671505561684427863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29756133781003707789618575 44634200671505561684427863)
          ·
            refine ⟨66951301007258342526641795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44634200671505561684427863 66951301007258342526641795)
            ·
              refine ⟨100426951510887513789962693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66951301007258342526641795 100426951510887513789962693)
              ·
                refine ⟨18830053408291408835618005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 100426951510887513789962693 18830053408291408835618005)
                ·
                  refine ⟨441329376756829894584797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18830053408291408835618005 441329376756829894584797)
                  ·
                    rfl

theorem cell23_7735373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 1, 4, 7].length) (baseStart_7735373 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7735373 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7735373 prefixEnd_7735373 := by exact prefixLift 7735373
  have htrace : WordTrace (prefixWord ++ tailWord_7735373) baseStart_7735373 baseEnd_7735373 := by
    simpa [prefixWord, tailWord_7735373, baseEnd_7735373] using wordTrace_append hprefix tailTrace_7735373
  have hstable : (prefixWord ++ tailWord_7735373).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7735373).length < 2 ^ (prefixWord ++ tailWord_7735373).sum := by decide
  have hdescent : baseEnd_7735373 < baseStart_7735373 := by decide
  rcases family_descends (prefixWord ++ tailWord_7735373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7735386 : List Nat := [3, 1, 1, 2, 1, 1, 3, 3, 1, 7]
def baseStart_7735386 : Nat := 118140960795 + 7735386 * 2 ^ 59
def prefixEnd_7735386 : Nat := 4983230072969 + 3 ^ 40 * 7735386 * 2
def baseEnd_7735386 : Nat := 1323990355353325833466871

theorem tailTrace_7735386 : CollatzResearch.WordTrace tailWord_7735386 prefixEnd_7735386 1323990355353325833466871 := by
  unfold tailWord_7735386
  simp only [CollatzResearch.WordTrace]
  refine ⟨70533176388506273898966503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 188088470369350063730577341 70533176388506273898966503)
  ·
    refine ⟨105799764582759410848449755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70533176388506273898966503 105799764582759410848449755)
    ·
      refine ⟨158699646874139116272674633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105799764582759410848449755 158699646874139116272674633)
      ·
        refine ⟨119024735155604337204505975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 158699646874139116272674633 119024735155604337204505975)
        ·
          refine ⟨178537102733406505806758963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 119024735155604337204505975 178537102733406505806758963)
          ·
            refine ⟨267805654100109758710138445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 178537102733406505806758963 267805654100109758710138445)
            ·
              refine ⟨100427120287541159516301917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 267805654100109758710138445 100427120287541159516301917)
              ·
                refine ⟨37660170107827934818613219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 100427120287541159516301917 37660170107827934818613219)
                ·
                  refine ⟨56490255161741902227919829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37660170107827934818613219 56490255161741902227919829)
                  ·
                    refine ⟨1323990355353325833466871, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 56490255161741902227919829 1323990355353325833466871)
                    ·
                      rfl

theorem cell23_7735386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 3, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 3, 3, 1, 7].length) (baseStart_7735386 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7735386 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7735386 prefixEnd_7735386 := by exact prefixLift 7735386
  have htrace : WordTrace (prefixWord ++ tailWord_7735386) baseStart_7735386 baseEnd_7735386 := by
    simpa [prefixWord, tailWord_7735386, baseEnd_7735386] using wordTrace_append hprefix tailTrace_7735386
  have hstable : (prefixWord ++ tailWord_7735386).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7735386).length < 2 ^ (prefixWord ++ tailWord_7735386).sum := by decide
  have hdescent : baseEnd_7735386 < baseStart_7735386 := by decide
  rcases family_descends (prefixWord ++ tailWord_7735386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7735393 : List Nat := [1, 2, 3, 1, 1, 2, 1, 2, 1, 7, 2]
def baseStart_7735393 : Nat := 118140960795 + 7735393 * 2 ^ 59
def prefixEnd_7735393 : Nat := 4983230072969 + 3 ^ 40 * 7735393 * 2
def baseEnd_7735393 : Nat := 3971974660424558973013081

theorem tailTrace_7735393 : CollatzResearch.WordTrace tailWord_7735393 prefixEnd_7735393 3971974660424558973013081 := by
  unfold tailWord_7735393
  simp only [CollatzResearch.WordTrace]
  refine ⟨282132960864999735791370833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188088640576666490527580555 282132960864999735791370833)
  ·
    refine ⟨211599720648749801843528125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 282132960864999735791370833 211599720648749801843528125)
    ·
      refine ⟨79349895243281175691323047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 211599720648749801843528125 79349895243281175691323047)
      ·
        refine ⟨119024842864921763536984571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79349895243281175691323047 119024842864921763536984571)
        ·
          refine ⟨178537264297382645305476857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 119024842864921763536984571 178537264297382645305476857)
          ·
            refine ⟨133902948223036983979107643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 178537264297382645305476857 133902948223036983979107643)
            ·
              refine ⟨200854422334555475968661465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 133902948223036983979107643 200854422334555475968661465)
              ·
                refine ⟨150640816750916606976496099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 200854422334555475968661465 150640816750916606976496099)
                ·
                  refine ⟨225961225126374910464744149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 150640816750916606976496099 225961225126374910464744149)
                  ·
                    refine ⟨5295966213899411964017441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 225961225126374910464744149 5295966213899411964017441)
                    ·
                      refine ⟨3971974660424558973013081, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5295966213899411964017441 3971974660424558973013081)
                      ·
                        rfl

theorem cell23_7735393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 1, 2, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 1, 2, 1, 7, 2].length) (baseStart_7735393 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7735393 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7735393 prefixEnd_7735393 := by exact prefixLift 7735393
  have htrace : WordTrace (prefixWord ++ tailWord_7735393) baseStart_7735393 baseEnd_7735393 := by
    simpa [prefixWord, tailWord_7735393, baseEnd_7735393] using wordTrace_append hprefix tailTrace_7735393
  have hstable : (prefixWord ++ tailWord_7735393).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7735393).length < 2 ^ (prefixWord ++ tailWord_7735393).sum := by decide
  have hdescent : baseEnd_7735393 < baseStart_7735393 := by decide
  rcases family_descends (prefixWord ++ tailWord_7735393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7735433 : List Nat := [1, 2, 1, 1, 4, 2, 2, 1, 5, 4]
def baseStart_7735433 : Nat := 118140960795 + 7735433 * 2 ^ 59
def prefixEnd_7735433 : Nat := 4983230072969 + 3 ^ 40 * 7735433 * 2
def baseEnd_7735433 : Nat := 1323998399883579605504299

theorem tailTrace_7735433 : CollatzResearch.WordTrace tailWord_7735433 prefixEnd_7735433 1323998399883579605504299 := by
  unfold tailWord_7735433
  simp only [CollatzResearch.WordTrace]
  refine ⟨282134419784854822622826953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188089613189903215081884635 282134419784854822622826953)
  ·
    refine ⟨211600814838641116967120215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 282134419784854822622826953 211600814838641116967120215)
    ·
      refine ⟨317401222257961675450680323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 211600814838641116967120215 317401222257961675450680323)
      ·
        refine ⟨476101833386942513176020485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 317401222257961675450680323 476101833386942513176020485)
        ·
          refine ⟨89269093760051721220503841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 476101833386942513176020485 89269093760051721220503841)
          ·
            refine ⟨66951820320038790915377881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 89269093760051721220503841 66951820320038790915377881)
            ·
              refine ⟨50213865240029093186533411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66951820320038790915377881 50213865240029093186533411)
              ·
                refine ⟨75320797860043639779800117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50213865240029093186533411 75320797860043639779800117)
                ·
                  refine ⟨7061324799379091229356261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 75320797860043639779800117 7061324799379091229356261)
                  ·
                    refine ⟨1323998399883579605504299, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7061324799379091229356261 1323998399883579605504299)
                    ·
                      rfl

theorem cell23_7735433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 2, 1, 5, 4].length) (baseStart_7735433 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7735433 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7735433 prefixEnd_7735433 := by exact prefixLift 7735433
  have htrace : WordTrace (prefixWord ++ tailWord_7735433) baseStart_7735433 baseEnd_7735433 := by
    simpa [prefixWord, tailWord_7735433, baseEnd_7735433] using wordTrace_append hprefix tailTrace_7735433
  have hstable : (prefixWord ++ tailWord_7735433).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7735433).length < 2 ^ (prefixWord ++ tailWord_7735433).sum := by decide
  have hdescent : baseEnd_7735433 < baseStart_7735433 := by decide
  rcases family_descends (prefixWord ++ tailWord_7735433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7735436 : List Nat := [2, 2, 1, 2, 1, 1, 1, 1, 3, 3, 6]
def baseStart_7735436 : Nat := 118140960795 + 7735436 * 2 ^ 59
def prefixEnd_7735436 : Nat := 4983230072969 + 3 ^ 40 * 7735436 * 2
def baseEnd_7735436 : Nat := 3971996740092702304775383

theorem tailTrace_7735436 : CollatzResearch.WordTrace tailWord_7735436 prefixEnd_7735436 3971996740092702304775383 := by
  unfold tailWord_7735436
  simp only [CollatzResearch.WordTrace]
  refine ⟨141067264601921977067593081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 188089686135895969423457441 141067264601921977067593081)
  ·
    refine ⟨105800448451441482800694811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 141067264601921977067593081 105800448451441482800694811)
    ·
      refine ⟨158700672677162224201042217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105800448451441482800694811 158700672677162224201042217)
      ·
        refine ⟨119025504507871668150781663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 158700672677162224201042217 119025504507871668150781663)
        ·
          refine ⟨178538256761807502226172495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 119025504507871668150781663 178538256761807502226172495)
          ·
            refine ⟨267807385142711253339258743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 178538256761807502226172495 267807385142711253339258743)
            ·
              refine ⟨401711077714066880008888115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 267807385142711253339258743 401711077714066880008888115)
              ·
                refine ⟨602566616571100320013332173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 401711077714066880008888115 602566616571100320013332173)
                ·
                  refine ⟨225962481214162620004999565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 602566616571100320013332173 225962481214162620004999565)
                  ·
                    refine ⟨84735930455310982501874837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 225962481214162620004999565 84735930455310982501874837)
                    ·
                      refine ⟨3971996740092702304775383, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 84735930455310982501874837 3971996740092702304775383)
                      ·
                        rfl

theorem cell23_7735436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 1, 3, 3, 6].length) (baseStart_7735436 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7735436 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7735436 prefixEnd_7735436 := by exact prefixLift 7735436
  have htrace : WordTrace (prefixWord ++ tailWord_7735436) baseStart_7735436 baseEnd_7735436 := by
    simpa [prefixWord, tailWord_7735436, baseEnd_7735436] using wordTrace_append hprefix tailTrace_7735436
  have hstable : (prefixWord ++ tailWord_7735436).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7735436).length < 2 ^ (prefixWord ++ tailWord_7735436).sum := by decide
  have hdescent : baseEnd_7735436 < baseStart_7735436 := by decide
  rcases family_descends (prefixWord ++ tailWord_7735436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
