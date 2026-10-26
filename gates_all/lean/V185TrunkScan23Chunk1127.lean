import V185TrunkScan23Chunk1126

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_6675359 : List Nat := [1, 1, 2, 5, 2, 1, 4, 1, 2, 4]
def baseStart_6675359 : Nat := 118140960795 + 6675359 * 2 ^ 59
def prefixEnd_6675359 : Nat := 4983230072969 + 3 ^ 40 * 6675359 * 2
def baseEnd_6675359 : Nat := 1142555902772151120304363

theorem tailTrace_6675359 : CollatzResearch.WordTrace tailWord_6675359 prefixEnd_6675359 1142555902772151120304363 := by
  unfold tailWord_6675359
  simp only [CollatzResearch.WordTrace]
  refine ⟨243470344623321878397453131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162313563082214585598302087 243470344623321878397453131)
  ·
    refine ⟨365205516934982817596179697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 243470344623321878397453131 365205516934982817596179697)
    ·
      refine ⟨273904137701237113197134773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 365205516934982817596179697 273904137701237113197134773)
      ·
        refine ⟨25678512909490979362231385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 273904137701237113197134773 25678512909490979362231385)
        ·
          refine ⟨19258884682118234521673539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25678512909490979362231385 19258884682118234521673539)
          ·
            refine ⟨28888327023177351782510309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19258884682118234521673539 28888327023177351782510309)
            ·
              refine ⟨5416561316845753459220683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 28888327023177351782510309 5416561316845753459220683)
              ·
                refine ⟨8124841975268630188831025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5416561316845753459220683 8124841975268630188831025)
                ·
                  refine ⟨6093631481451472641623269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8124841975268630188831025 6093631481451472641623269)
                  ·
                    refine ⟨1142555902772151120304363, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6093631481451472641623269 1142555902772151120304363)
                    ·
                      rfl

theorem cell23_6675359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 4, 1, 2, 4].length) (baseStart_6675359 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6675359 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6675359 prefixEnd_6675359 := by exact prefixLift 6675359
  have htrace : WordTrace (prefixWord ++ tailWord_6675359) baseStart_6675359 baseEnd_6675359 := by
    simpa [prefixWord, tailWord_6675359, baseEnd_6675359] using wordTrace_append hprefix tailTrace_6675359
  have hstable : (prefixWord ++ tailWord_6675359).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6675359).length < 2 ^ (prefixWord ++ tailWord_6675359).sum := by decide
  have hdescent : baseEnd_6675359 < baseStart_6675359 := by decide
  rcases family_descends (prefixWord ++ tailWord_6675359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6675400 : List Nat := [2, 1, 3, 1, 5, 2, 2, 2, 1, 2, 2]
def baseStart_6675400 : Nat := 118140960795 + 6675400 * 2 ^ 59
def prefixEnd_6675400 : Nat := 4983230072969 + 3 ^ 40 * 6675400 * 2
def baseEnd_6675400 : Nat := 3427688761023287700500401

theorem tailTrace_6675400 : CollatzResearch.WordTrace tailWord_6675400 prefixEnd_6675400 3427688761023287700500401 := by
  unfold tailWord_6675400
  simp only [CollatzResearch.WordTrace]
  refine ⟨121735920008086671199847827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 162314560010782228266463769 121735920008086671199847827)
  ·
    refine ⟨182603880012130006799771741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121735920008086671199847827 182603880012130006799771741)
    ·
      refine ⟨68476455004548752549914403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 182603880012130006799771741 68476455004548752549914403)
      ·
        refine ⟨102714682506823128824871605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68476455004548752549914403 102714682506823128824871605)
        ·
          refine ⟨9629501485014668327331713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 102714682506823128824871605 9629501485014668327331713)
          ·
            refine ⟨7222126113761001245498785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9629501485014668327331713 7222126113761001245498785)
            ·
              refine ⟨5416594585320750934124089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7222126113761001245498785 5416594585320750934124089)
              ·
                refine ⟨4062445938990563200593067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5416594585320750934124089 4062445938990563200593067)
                ·
                  refine ⟨6093668908485844800889601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4062445938990563200593067 6093668908485844800889601)
                  ·
                    refine ⟨4570251681364383600667201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6093668908485844800889601 4570251681364383600667201)
                    ·
                      refine ⟨3427688761023287700500401, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4570251681364383600667201 3427688761023287700500401)
                      ·
                        rfl

theorem cell23_6675400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 5, 2, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 5, 2, 2, 2, 1, 2, 2].length) (baseStart_6675400 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6675400 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6675400 prefixEnd_6675400 := by exact prefixLift 6675400
  have htrace : WordTrace (prefixWord ++ tailWord_6675400) baseStart_6675400 baseEnd_6675400 := by
    simpa [prefixWord, tailWord_6675400, baseEnd_6675400] using wordTrace_append hprefix tailTrace_6675400
  have hstable : (prefixWord ++ tailWord_6675400).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6675400).length < 2 ^ (prefixWord ++ tailWord_6675400).sum := by decide
  have hdescent : baseEnd_6675400 < baseStart_6675400 := by decide
  rcases family_descends (prefixWord ++ tailWord_6675400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6675425 : List Nat := [1, 2, 3, 1, 2, 1, 1, 1, 4, 4, 3]
def baseStart_6675425 : Nat := 118140960795 + 6675425 * 2 ^ 59
def prefixEnd_6675425 : Nat := 4983230072969 + 3 ^ 40 * 6675425 * 2
def baseEnd_6675425 : Nat := 3427701598039650102687785

theorem tailTrace_6675425 : CollatzResearch.WordTrace tailWord_6675425 prefixEnd_6675425 3427701598039650102687785 := by
  unfold tailWord_6675425
  simp only [CollatzResearch.WordTrace]
  refine ⟨243472751841082771669355729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162315167894055181112903819 243472751841082771669355729)
  ·
    refine ⟨182604563880812078752016797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 243472751841082771669355729 182604563880812078752016797)
    ·
      refine ⟨68476711455304529532006299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 182604563880812078752016797 68476711455304529532006299)
      ·
        refine ⟨102715067182956794298009449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68476711455304529532006299 102715067182956794298009449)
        ·
          refine ⟨77036300387217595723507087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 102715067182956794298009449 77036300387217595723507087)
          ·
            refine ⟨115554450580826393585260631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77036300387217595723507087 115554450580826393585260631)
            ·
              refine ⟨173331675871239590377890947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 115554450580826393585260631 173331675871239590377890947)
              ·
                refine ⟨259997513806859385566836421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 173331675871239590377890947 259997513806859385566836421)
                ·
                  refine ⟨48749533838786134793781829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 259997513806859385566836421 48749533838786134793781829)
                  ·
                    refine ⟨9140537594772400273834093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 48749533838786134793781829 9140537594772400273834093)
                    ·
                      refine ⟨3427701598039650102687785, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9140537594772400273834093 3427701598039650102687785)
                      ·
                        rfl

theorem cell23_6675425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 1, 1, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 1, 1, 4, 4, 3].length) (baseStart_6675425 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6675425 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6675425 prefixEnd_6675425 := by exact prefixLift 6675425
  have htrace : WordTrace (prefixWord ++ tailWord_6675425) baseStart_6675425 baseEnd_6675425 := by
    simpa [prefixWord, tailWord_6675425, baseEnd_6675425] using wordTrace_append hprefix tailTrace_6675425
  have hstable : (prefixWord ++ tailWord_6675425).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6675425).length < 2 ^ (prefixWord ++ tailWord_6675425).sum := by decide
  have hdescent : baseEnd_6675425 < baseStart_6675425 := by decide
  rcases family_descends (prefixWord ++ tailWord_6675425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6675426 : List Nat := [3, 3, 3, 1, 1, 1, 2, 1, 3, 3, 2]
def baseStart_6675426 : Nat := 118140960795 + 6675426 * 2 ^ 59
def prefixEnd_6675426 : Nat := 4983230072969 + 3 ^ 40 * 6675426 * 2
def baseEnd_6675426 : Nat := 3427702111520304598775281

theorem tailTrace_6675426 : CollatzResearch.WordTrace tailWord_6675426 prefixEnd_6675426 3427702111520304598775281 := by
  unfold tailWord_6675426
  simp only [CollatzResearch.WordTrace]
  refine ⟨60868197078519787210035533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 162315192209386099226761421 60868197078519787210035533)
  ·
    refine ⟨22825573904444920203763325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 60868197078519787210035533 22825573904444920203763325)
    ·
      refine ⟨8559590214166845076411247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22825573904444920203763325 8559590214166845076411247)
      ·
        refine ⟨12839385321250267614616871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8559590214166845076411247 12839385321250267614616871)
        ·
          refine ⟨19259077981875401421925307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12839385321250267614616871 19259077981875401421925307)
          ·
            refine ⟨28888616972813102132887961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19259077981875401421925307 28888616972813102132887961)
            ·
              refine ⟨21666462729609826599665971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28888616972813102132887961 21666462729609826599665971)
              ·
                refine ⟨32499694094414739899498957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21666462729609826599665971 32499694094414739899498957)
                ·
                  refine ⟨12187385285405527462312109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32499694094414739899498957 12187385285405527462312109)
                  ·
                    refine ⟨4570269482027072798367041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12187385285405527462312109 4570269482027072798367041)
                    ·
                      refine ⟨3427702111520304598775281, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4570269482027072798367041 3427702111520304598775281)
                      ·
                        rfl

theorem cell23_6675426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 2, 1, 3, 3, 2].length) (baseStart_6675426 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6675426 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6675426 prefixEnd_6675426 := by exact prefixLift 6675426
  have htrace : WordTrace (prefixWord ++ tailWord_6675426) baseStart_6675426 baseEnd_6675426 := by
    simpa [prefixWord, tailWord_6675426, baseEnd_6675426] using wordTrace_append hprefix tailTrace_6675426
  have hstable : (prefixWord ++ tailWord_6675426).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6675426).length < 2 ^ (prefixWord ++ tailWord_6675426).sum := by decide
  have hdescent : baseEnd_6675426 < baseStart_6675426 := by decide
  rcases family_descends (prefixWord ++ tailWord_6675426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6675492 : List Nat := [2, 3, 1, 4, 1, 1, 2, 1, 1, 7]
def baseStart_6675492 : Nat := 118140960795 + 6675492 * 2 ^ 59
def prefixEnd_6675492 : Nat := 4983230072969 + 3 ^ 40 * 6675492 * 2
def baseEnd_6675492 : Nat := 1142578667081167113516659

theorem tailTrace_6675492 : CollatzResearch.WordTrace tailWord_6675492 prefixEnd_6675492 1142578667081167113516659 := by
  unfold tailWord_6675492
  simp only [CollatzResearch.WordTrace]
  refine ⟨121737597765920021056022365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 162316797021226694741363153 121737597765920021056022365)
  ·
    refine ⟨45651599162220007896008387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 121737597765920021056022365 45651599162220007896008387)
    ·
      refine ⟨68477398743330011844012581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45651599162220007896008387 68477398743330011844012581)
      ·
        refine ⟨12839512264374377220752359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 68477398743330011844012581 12839512264374377220752359)
        ·
          refine ⟨19259268396561565831128539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12839512264374377220752359 19259268396561565831128539)
          ·
            refine ⟨28888902594842348746692809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19259268396561565831128539 28888902594842348746692809)
            ·
              refine ⟨21666676946131761560019607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28888902594842348746692809 21666676946131761560019607)
              ·
                refine ⟨32500015419197642340029411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21666676946131761560019607 32500015419197642340029411)
                ·
                  refine ⟨48750023128796463510044117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32500015419197642340029411 48750023128796463510044117)
                  ·
                    refine ⟨1142578667081167113516659, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 48750023128796463510044117 1142578667081167113516659)
                    ·
                      rfl

theorem cell23_6675492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 2, 1, 1, 7].length) (baseStart_6675492 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6675492 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6675492 prefixEnd_6675492 := by exact prefixLift 6675492
  have htrace : WordTrace (prefixWord ++ tailWord_6675492) baseStart_6675492 baseEnd_6675492 := by
    simpa [prefixWord, tailWord_6675492, baseEnd_6675492] using wordTrace_append hprefix tailTrace_6675492
  have hstable : (prefixWord ++ tailWord_6675492).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6675492).length < 2 ^ (prefixWord ++ tailWord_6675492).sum := by decide
  have hdescent : baseEnd_6675492 < baseStart_6675492 := by decide
  rcases family_descends (prefixWord ++ tailWord_6675492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6675502 : List Nat := [4, 1, 3, 1, 1, 1, 2, 2, 1, 2, 5]
def baseStart_6675502 : Nat := 118140960795 + 6675502 * 2 ^ 59
def prefixEnd_6675502 : Nat := 4983230072969 + 3 ^ 40 * 6675502 * 2
def baseEnd_6675502 : Nat := 3427741136050046301424931

theorem tailTrace_6675502 : CollatzResearch.WordTrace tailWord_6675502 prefixEnd_6675502 3427741136050046301424931 := by
  unfold tailWord_6675502
  simp only [CollatzResearch.WordTrace]
  refine ⟨30434445032725476727488595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 162317040174535875879939173 30434445032725476727488595)
  ·
    refine ⟨45651667549088215091232893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30434445032725476727488595 45651667549088215091232893)
    ·
      refine ⟨17119375330908080659212335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 45651667549088215091232893 17119375330908080659212335)
      ·
        refine ⟨25679062996362120988818503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17119375330908080659212335 25679062996362120988818503)
        ·
          refine ⟨38518594494543181483227755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25679062996362120988818503 38518594494543181483227755)
          ·
            refine ⟨57777891741814772224841633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38518594494543181483227755 57777891741814772224841633)
            ·
              refine ⟨43333418806361079168631225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 57777891741814772224841633 43333418806361079168631225)
              ·
                refine ⟨32500064104770809376473419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43333418806361079168631225 32500064104770809376473419)
                ·
                  refine ⟨48750096157156214064710129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32500064104770809376473419 48750096157156214064710129)
                  ·
                    refine ⟨36562572117867160548532597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 48750096157156214064710129 36562572117867160548532597)
                    ·
                      refine ⟨3427741136050046301424931, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36562572117867160548532597 3427741136050046301424931)
                      ·
                        rfl

theorem cell23_6675502_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 2, 2, 1, 2, 5].length) (baseStart_6675502 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6675502 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6675502 prefixEnd_6675502 := by exact prefixLift 6675502
  have htrace : WordTrace (prefixWord ++ tailWord_6675502) baseStart_6675502 baseEnd_6675502 := by
    simpa [prefixWord, tailWord_6675502, baseEnd_6675502] using wordTrace_append hprefix tailTrace_6675502
  have hstable : (prefixWord ++ tailWord_6675502).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6675502).length < 2 ^ (prefixWord ++ tailWord_6675502).sum := by decide
  have hdescent : baseEnd_6675502 < baseStart_6675502 := by decide
  rcases family_descends (prefixWord ++ tailWord_6675502) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6675512 : List Nat := [2, 1, 2, 1, 5, 1, 1, 1, 4, 1, 4]
def baseStart_6675512 : Nat := 118140960795 + 6675512 * 2 ^ 59
def prefixEnd_6675512 : Nat := 4983230072969 + 3 ^ 40 * 6675512 * 2
def baseEnd_6675512 : Nat := 3427746270856591262299885

theorem tailTrace_6675512 : CollatzResearch.WordTrace tailWord_6675512 prefixEnd_6675512 3427746270856591262299885 := by
  unfold tailWord_6675512
  simp only [CollatzResearch.WordTrace]
  refine ⟨121737962495883792763886395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 162317283327845057018515193 121737962495883792763886395)
  ·
    refine ⟨182606943743825689145829593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121737962495883792763886395 182606943743825689145829593)
    ·
      refine ⟨136955207807869266859372195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 182606943743825689145829593 136955207807869266859372195)
      ·
        refine ⟨205432811711803900289058293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 136955207807869266859372195 205432811711803900289058293)
        ·
          refine ⟨19259326097981615652099215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 205432811711803900289058293 19259326097981615652099215)
          ·
            refine ⟨28888989146972423478148823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19259326097981615652099215 28888989146972423478148823)
            ·
              refine ⟨43333483720458635217223235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28888989146972423478148823 43333483720458635217223235)
              ·
                refine ⟨65000225580687952825834853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43333483720458635217223235 65000225580687952825834853)
                ·
                  refine ⟨12187542296378991154844035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 65000225580687952825834853 12187542296378991154844035)
                  ·
                    refine ⟨18281313444568486732266053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12187542296378991154844035 18281313444568486732266053)
                    ·
                      refine ⟨3427746270856591262299885, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18281313444568486732266053 3427746270856591262299885)
                      ·
                        rfl

theorem cell23_6675512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 1, 1, 4, 1, 4].length) (baseStart_6675512 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6675512 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6675512 prefixEnd_6675512 := by exact prefixLift 6675512
  have htrace : WordTrace (prefixWord ++ tailWord_6675512) baseStart_6675512 baseEnd_6675512 := by
    simpa [prefixWord, tailWord_6675512, baseEnd_6675512] using wordTrace_append hprefix tailTrace_6675512
  have hstable : (prefixWord ++ tailWord_6675512).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6675512).length < 2 ^ (prefixWord ++ tailWord_6675512).sum := by decide
  have hdescent : baseEnd_6675512 < baseStart_6675512 := by decide
  rcases family_descends (prefixWord ++ tailWord_6675512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6675525 : List Nat := [1, 3, 1, 1, 1, 3, 2, 2, 2, 1, 6]
def baseStart_6675525 : Nat := 118140960795 + 6675525 * 2 ^ 59
def prefixEnd_6675525 : Nat := 4983230072969 + 3 ^ 40 * 6675525 * 2
def baseEnd_6675525 : Nat := 3427752946105099711437325

theorem tailTrace_6675525 : CollatzResearch.WordTrace tailWord_6675525 prefixEnd_6675525 3427752946105099711437325 := by
  unfold tailWord_6675525
  simp only [CollatzResearch.WordTrace]
  refine ⟨243476399140720488747996029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162317599427146992498664019 243476399140720488747996029)
  ·
    refine ⟨91303649677770183280498511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 243476399140720488747996029 91303649677770183280498511)
    ·
      refine ⟨136955474516655274920747767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91303649677770183280498511 136955474516655274920747767)
      ·
        refine ⟨205433211774982912381121651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 136955474516655274920747767 205433211774982912381121651)
        ·
          refine ⟨308149817662474368571682477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 205433211774982912381121651 308149817662474368571682477)
          ·
            refine ⟨115556181623427888214380929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 308149817662474368571682477 115556181623427888214380929)
            ·
              refine ⟨86667136217570916160785697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 115556181623427888214380929 86667136217570916160785697)
              ·
                refine ⟨65000352163178187120589273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 86667136217570916160785697 65000352163178187120589273)
                ·
                  refine ⟨48750264122383640340441955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 65000352163178187120589273 48750264122383640340441955)
                  ·
                    refine ⟨73125396183575460510662933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 48750264122383640340441955 73125396183575460510662933)
                    ·
                      refine ⟨3427752946105099711437325, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 73125396183575460510662933 3427752946105099711437325)
                      ·
                        rfl

theorem cell23_6675525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 2, 2, 2, 1, 6].length) (baseStart_6675525 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6675525 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6675525 prefixEnd_6675525 := by exact prefixLift 6675525
  have htrace : WordTrace (prefixWord ++ tailWord_6675525) baseStart_6675525 baseEnd_6675525 := by
    simpa [prefixWord, tailWord_6675525, baseEnd_6675525] using wordTrace_append hprefix tailTrace_6675525
  have hstable : (prefixWord ++ tailWord_6675525).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6675525).length < 2 ^ (prefixWord ++ tailWord_6675525).sum := by decide
  have hdescent : baseEnd_6675525 < baseStart_6675525 := by decide
  rcases family_descends (prefixWord ++ tailWord_6675525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6675532 : List Nat := [2, 2, 1, 3, 1, 1, 1, 1, 6, 2, 3]
def baseStart_6675532 : Nat := 118140960795 + 6675532 * 2 ^ 59
def prefixEnd_6675532 : Nat := 4983230072969 + 3 ^ 40 * 6675532 * 2
def baseEnd_6675532 : Nat := 3427756540469681184049793

theorem tailTrace_6675532 : CollatzResearch.WordTrace tailWord_6675532 prefixEnd_6675532 3427756540469681184049793 := by
  unfold tailWord_6675532
  simp only [CollatzResearch.WordTrace]
  refine ⟨121738327225847564471750425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 162317769634463419295667233 121738327225847564471750425)
  ·
    refine ⟨91303745419385673353812819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 121738327225847564471750425 91303745419385673353812819)
    ·
      refine ⟨136955618129078510030719229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91303745419385673353812819 136955618129078510030719229)
      ·
        refine ⟨51358356798404441261519711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 136955618129078510030719229 51358356798404441261519711)
        ·
          refine ⟨77037535197606661892279567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51358356798404441261519711 77037535197606661892279567)
          ·
            refine ⟨115556302796409992838419351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77037535197606661892279567 115556302796409992838419351)
            ·
              refine ⟨173334454194614989257629027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 115556302796409992838419351 173334454194614989257629027)
              ·
                refine ⟨260001681291922483886443541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 173334454194614989257629027 260001681291922483886443541)
                ·
                  refine ⟨12187578810558866432177041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 260001681291922483886443541 12187578810558866432177041)
                  ·
                    refine ⟨9140684107919149824132781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12187578810558866432177041 9140684107919149824132781)
                    ·
                      refine ⟨3427756540469681184049793, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9140684107919149824132781 3427756540469681184049793)
                      ·
                        rfl

theorem cell23_6675532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 1, 1, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 1, 1, 6, 2, 3].length) (baseStart_6675532 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6675532 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6675532 prefixEnd_6675532 := by exact prefixLift 6675532
  have htrace : WordTrace (prefixWord ++ tailWord_6675532) baseStart_6675532 baseEnd_6675532 := by
    simpa [prefixWord, tailWord_6675532, baseEnd_6675532] using wordTrace_append hprefix tailTrace_6675532
  have hstable : (prefixWord ++ tailWord_6675532).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6675532).length < 2 ^ (prefixWord ++ tailWord_6675532).sum := by decide
  have hdescent : baseEnd_6675532 < baseStart_6675532 := by decide
  rcases family_descends (prefixWord ++ tailWord_6675532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6675555 : List Nat := [1, 1, 1, 5, 1, 1, 1, 2, 1, 1, 8]
def baseStart_6675555 : Nat := 118140960795 + 6675555 * 2 ^ 59
def prefixEnd_6675555 : Nat := 4983230072969 + 3 ^ 40 * 6675555 * 2
def baseEnd_6675555 : Nat := 3427768350524734594062187

theorem tailTrace_6675555 : CollatzResearch.WordTrace tailWord_6675555 prefixEnd_6675555 3427768350524734594062187 := by
  unfold tailWord_6675555
  simp only [CollatzResearch.WordTrace]
  refine ⟨243477493330611803871588119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162318328887074535914392079 243477493330611803871588119)
  ·
    refine ⟨365216239995917705807382179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 243477493330611803871588119 365216239995917705807382179)
    ·
      refine ⟨547824359993876558711073269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 365216239995917705807382179 547824359993876558711073269)
      ·
        refine ⟨51358533749425927379163119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 547824359993876558711073269 51358533749425927379163119)
        ·
          refine ⟨77037800624138891068744679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51358533749425927379163119 77037800624138891068744679)
          ·
            refine ⟨115556700936208336603117019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77037800624138891068744679 115556700936208336603117019)
            ·
              refine ⟨173335051404312504904675529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 115556700936208336603117019 173335051404312504904675529)
              ·
                refine ⟨130001288553234378678506647, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 173335051404312504904675529 130001288553234378678506647)
                ·
                  refine ⟨195001932829851568017759971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 130001288553234378678506647 195001932829851568017759971)
                  ·
                    refine ⟨292502899244777352026639957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 195001932829851568017759971 292502899244777352026639957)
                    ·
                      refine ⟨3427768350524734594062187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 292502899244777352026639957 3427768350524734594062187)
                      ·
                        rfl

theorem cell23_6675555_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 1, 2, 1, 1, 8].length) (baseStart_6675555 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6675555 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6675555 prefixEnd_6675555 := by exact prefixLift 6675555
  have htrace : WordTrace (prefixWord ++ tailWord_6675555) baseStart_6675555 baseEnd_6675555 := by
    simpa [prefixWord, tailWord_6675555, baseEnd_6675555] using wordTrace_append hprefix tailTrace_6675555
  have hstable : (prefixWord ++ tailWord_6675555).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6675555).length < 2 ^ (prefixWord ++ tailWord_6675555).sum := by decide
  have hdescent : baseEnd_6675555 < baseStart_6675555 := by decide
  rcases family_descends (prefixWord ++ tailWord_6675555) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6675613 : List Nat := [1, 4, 2, 1, 1, 2, 4, 3, 1, 1, 3]
def baseStart_6675613 : Nat := 118140960795 + 6675613 * 2 ^ 59
def prefixEnd_6675613 : Nat := 4983230072969 + 3 ^ 40 * 6675613 * 2
def baseEnd_6675613 : Nat := 3427798132402695367136921

theorem tailTrace_6675613 : CollatzResearch.WordTrace tailWord_6675613 prefixEnd_6675613 3427798132402695367136921 := by
  unfold tailWord_6675613
  simp only [CollatzResearch.WordTrace]
  refine ⟨243479608764401679777199493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162319739176267786518132995 243479608764401679777199493)
  ·
    refine ⟨45652426643325314958224905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 243479608764401679777199493 45652426643325314958224905)
    ·
      refine ⟨34239319982493986218668679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45652426643325314958224905 34239319982493986218668679)
      ·
        refine ⟨51358979973740979328003019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34239319982493986218668679 51358979973740979328003019)
        ·
          refine ⟨77038469960611468992004529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51358979973740979328003019 77038469960611468992004529)
          ·
            refine ⟨57778852470458601744003397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 77038469960611468992004529 57778852470458601744003397)
            ·
              refine ⟨10833534838210987827000637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 57778852470458601744003397 10833534838210987827000637)
              ·
                refine ⟨4062575564329120435125239, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10833534838210987827000637 4062575564329120435125239)
                ·
                  refine ⟨6093863346493680652687859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4062575564329120435125239 6093863346493680652687859)
                  ·
                    refine ⟨9140795019740520979031789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6093863346493680652687859 9140795019740520979031789)
                    ·
                      refine ⟨3427798132402695367136921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9140795019740520979031789 3427798132402695367136921)
                      ·
                        rfl

theorem cell23_6675613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 4, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 4, 3, 1, 1, 3].length) (baseStart_6675613 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6675613 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6675613 prefixEnd_6675613 := by exact prefixLift 6675613
  have htrace : WordTrace (prefixWord ++ tailWord_6675613) baseStart_6675613 baseEnd_6675613 := by
    simpa [prefixWord, tailWord_6675613, baseEnd_6675613] using wordTrace_append hprefix tailTrace_6675613
  have hstable : (prefixWord ++ tailWord_6675613).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6675613).length < 2 ^ (prefixWord ++ tailWord_6675613).sum := by decide
  have hdescent : baseEnd_6675613 < baseStart_6675613 := by decide
  rcases family_descends (prefixWord ++ tailWord_6675613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6675646 : List Nat := [4, 2, 1, 1, 3, 3, 1, 1, 1, 6]
def baseStart_6675646 : Nat := 118140960795 + 6675646 * 2 ^ 59
def prefixEnd_6675646 : Nat := 4983230072969 + 3 ^ 40 * 6675646 * 2
def baseEnd_6675646 : Nat := 1142605025754764579341423

theorem tailTrace_6675646 : CollatzResearch.WordTrace tailWord_6675646 prefixEnd_6675646 1142605025754764579341423 := by
  unfold tailWord_6675646
  simp only [CollatzResearch.WordTrace]
  refine ⟨30435101546660265801643849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 162320541582188084275433861 30435101546660265801643849)
  ·
    refine ⟨22826326159995199351232887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30435101546660265801643849 22826326159995199351232887)
    ·
      refine ⟨34239489239992799026849331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22826326159995199351232887 34239489239992799026849331)
      ·
        refine ⟨51359233859989198540273997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34239489239992799026849331 51359233859989198540273997)
        ·
          refine ⟨19259712697495949452602749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 51359233859989198540273997 19259712697495949452602749)
          ·
            refine ⟨7222392261560981044726031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19259712697495949452602749 7222392261560981044726031)
            ·
              refine ⟨10833588392341471567089047, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7222392261560981044726031 10833588392341471567089047)
              ·
                refine ⟨16250382588512207350633571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10833588392341471567089047 16250382588512207350633571)
                ·
                  refine ⟨24375573882768311025950357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16250382588512207350633571 24375573882768311025950357)
                  ·
                    refine ⟨1142605025754764579341423, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24375573882768311025950357 1142605025754764579341423)
                    ·
                      rfl

theorem cell23_6675646_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 3, 1, 1, 1, 6].length) (baseStart_6675646 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6675646 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6675646 prefixEnd_6675646 := by exact prefixLift 6675646
  have htrace : WordTrace (prefixWord ++ tailWord_6675646) baseStart_6675646 baseEnd_6675646 := by
    simpa [prefixWord, tailWord_6675646, baseEnd_6675646] using wordTrace_append hprefix tailTrace_6675646
  have hstable : (prefixWord ++ tailWord_6675646).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6675646).length < 2 ^ (prefixWord ++ tailWord_6675646).sum := by decide
  have hdescent : baseEnd_6675646 < baseStart_6675646 := by decide
  rcases family_descends (prefixWord ++ tailWord_6675646) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6675650 : List Nat := [3, 5, 1, 1, 2, 1, 2, 2, 1, 5]
def baseStart_6675650 : Nat := 118140960795 + 6675650 * 2 ^ 59
def prefixEnd_6675650 : Nat := 4983230072969 + 3 ^ 40 * 6675650 * 2
def baseEnd_6675650 : Nat := 1142605710395637240791417

theorem tailTrace_6675650 : CollatzResearch.WordTrace tailWord_6675650 prefixEnd_6675650 1142605710395637240791417 := by
  unfold tailWord_6675650
  simp only [CollatzResearch.WordTrace]
  refine ⟨60870239566316908774074101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 162320638843511756730864269 60870239566316908774074101)
  ·
    refine ⟨5706584959342210197569447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 60870239566316908774074101 5706584959342210197569447)
    ·
      refine ⟨8559877439013315296354171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5706584959342210197569447 8559877439013315296354171)
      ·
        refine ⟨12839816158519972944531257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8559877439013315296354171 12839816158519972944531257)
        ·
          refine ⟨9629862118889979708398443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12839816158519972944531257 9629862118889979708398443)
          ·
            refine ⟨14444793178334969562597665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9629862118889979708398443 14444793178334969562597665)
            ·
              refine ⟨10833594883751227171948249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14444793178334969562597665 10833594883751227171948249)
              ·
                refine ⟨8125196162813420378961187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10833594883751227171948249 8125196162813420378961187)
                ·
                  refine ⟨12187794244220130568441781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8125196162813420378961187 12187794244220130568441781)
                  ·
                    refine ⟨1142605710395637240791417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12187794244220130568441781 1142605710395637240791417)
                    ·
                      rfl

theorem cell23_6675650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 2, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 2, 1, 2, 2, 1, 5].length) (baseStart_6675650 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6675650 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6675650 prefixEnd_6675650 := by exact prefixLift 6675650
  have htrace : WordTrace (prefixWord ++ tailWord_6675650) baseStart_6675650 baseEnd_6675650 := by
    simpa [prefixWord, tailWord_6675650, baseEnd_6675650] using wordTrace_append hprefix tailTrace_6675650
  have hstable : (prefixWord ++ tailWord_6675650).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6675650).length < 2 ^ (prefixWord ++ tailWord_6675650).sum := by decide
  have hdescent : baseEnd_6675650 < baseStart_6675650 := by decide
  rcases family_descends (prefixWord ++ tailWord_6675650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6675687 : List Nat := [1, 1, 5, 3, 3, 1, 1, 1, 3, 2, 2]
def baseStart_6675687 : Nat := 118140960795 + 6675687 * 2 ^ 59
def prefixEnd_6675687 : Nat := 4983230072969 + 3 ^ 40 * 6675687 * 2
def baseEnd_6675687 : Nat := 3427836129971128077611581

theorem tailTrace_6675687 : CollatzResearch.WordTrace tailWord_6675687 prefixEnd_6675687 3427836129971128077611581 := by
  unfold tailWord_6675687
  simp only [CollatzResearch.WordTrace]
  refine ⟨243482307766133590415393315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162321538510755726943595543 243482307766133590415393315)
  ·
    refine ⟨365223461649200385623089973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 243482307766133590415393315 365223461649200385623089973)
    ·
      refine ⟨34239699529612536152164685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 365223461649200385623089973 34239699529612536152164685)
      ·
        refine ⟨12839887323604701057061757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34239699529612536152164685 12839887323604701057061757)
        ·
          refine ⟨4814957746351762896398159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12839887323604701057061757 4814957746351762896398159)
          ·
            refine ⟨7222436619527644344597239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4814957746351762896398159 7222436619527644344597239)
            ·
              refine ⟨10833654929291466516895859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7222436619527644344597239 10833654929291466516895859)
              ·
                refine ⟨16250482393937199775343789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10833654929291466516895859 16250482393937199775343789)
                ·
                  refine ⟨6093930897726449915753921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16250482393937199775343789 6093930897726449915753921)
                  ·
                    refine ⟨4570448173294837436815441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6093930897726449915753921 4570448173294837436815441)
                    ·
                      refine ⟨3427836129971128077611581, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4570448173294837436815441 3427836129971128077611581)
                      ·
                        rfl

theorem cell23_6675687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 3, 1, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 3, 1, 1, 1, 3, 2, 2].length) (baseStart_6675687 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6675687 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6675687 prefixEnd_6675687 := by exact prefixLift 6675687
  have htrace : WordTrace (prefixWord ++ tailWord_6675687) baseStart_6675687 baseEnd_6675687 := by
    simpa [prefixWord, tailWord_6675687, baseEnd_6675687] using wordTrace_append hprefix tailTrace_6675687
  have hstable : (prefixWord ++ tailWord_6675687).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6675687).length < 2 ^ (prefixWord ++ tailWord_6675687).sum := by decide
  have hdescent : baseEnd_6675687 < baseStart_6675687 := by decide
  rcases family_descends (prefixWord ++ tailWord_6675687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6675713 : List Nat := [1, 2, 4, 1, 1, 3, 3, 2, 1, 3, 2]
def baseStart_6675713 : Nat := 118140960795 + 6675713 * 2 ^ 59
def prefixEnd_6675713 : Nat := 4983230072969 + 3 ^ 40 * 6675713 * 2
def baseEnd_6675713 : Nat := 3427849480468144975886461

theorem tailTrace_6675713 : CollatzResearch.WordTrace tailWord_6675713 prefixEnd_6675713 3427849480468144975886461 := by
  unfold tailWord_6675713
  simp only [CollatzResearch.WordTrace]
  refine ⟨243483256064039396855839793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162322170709359597903893195 243483256064039396855839793)
  ·
    refine ⟨182612442048029547641879845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 243483256064039396855839793 182612442048029547641879845)
    ·
      refine ⟨34239832884005540182852471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 182612442048029547641879845 34239832884005540182852471)
      ·
        refine ⟨51359749326008310274278707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34239832884005540182852471 51359749326008310274278707)
        ·
          refine ⟨77039623989012465411418061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51359749326008310274278707 77039623989012465411418061)
          ·
            refine ⟨28889858995879674529281773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 77039623989012465411418061 28889858995879674529281773)
            ·
              refine ⟨10833697123454877948480665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28889858995879674529281773 10833697123454877948480665)
              ·
                refine ⟨8125272842591158461360499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10833697123454877948480665 8125272842591158461360499)
                ·
                  refine ⟨12187909263886737692040749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8125272842591158461360499 12187909263886737692040749)
                  ·
                    refine ⟨4570465973957526634515281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12187909263886737692040749 4570465973957526634515281)
                    ·
                      refine ⟨3427849480468144975886461, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4570465973957526634515281 3427849480468144975886461)
                      ·
                        rfl

theorem cell23_6675713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 3, 2, 1, 3, 2].length) (baseStart_6675713 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6675713 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6675713 prefixEnd_6675713 := by exact prefixLift 6675713
  have htrace : WordTrace (prefixWord ++ tailWord_6675713) baseStart_6675713 baseEnd_6675713 := by
    simpa [prefixWord, tailWord_6675713, baseEnd_6675713] using wordTrace_append hprefix tailTrace_6675713
  have hstable : (prefixWord ++ tailWord_6675713).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6675713).length < 2 ^ (prefixWord ++ tailWord_6675713).sum := by decide
  have hdescent : baseEnd_6675713 < baseStart_6675713 := by decide
  rcases family_descends (prefixWord ++ tailWord_6675713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6675726 : List Nat := [4, 1, 1, 2, 1, 3, 1, 1, 3, 4, 2]
def baseStart_6675726 : Nat := 118140960795 + 6675726 * 2 ^ 59
def prefixEnd_6675726 : Nat := 4983230072969 + 3 ^ 40 * 6675726 * 2
def baseEnd_6675726 : Nat := 3427856155716653425023901

theorem tailTrace_6675726 : CollatzResearch.WordTrace tailWord_6675726 prefixEnd_6675726 3427856155716653425023901 := by
  unfold tailWord_6675726
  simp only [CollatzResearch.WordTrace]
  refine ⟨30435466276624037509507879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 162322486808661533384042021 30435466276624037509507879)
  ·
    refine ⟨45653199414936056264261819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30435466276624037509507879 45653199414936056264261819)
    ·
      refine ⟨68479799122404084396392729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45653199414936056264261819 68479799122404084396392729)
      ·
        refine ⟨51359849341803063297294547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68479799122404084396392729 51359849341803063297294547)
        ·
          refine ⟨77039774012704594945941821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51359849341803063297294547 77039774012704594945941821)
          ·
            refine ⟨28889915254764223104728183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 77039774012704594945941821 28889915254764223104728183)
            ·
              refine ⟨43334872882146334657092275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28889915254764223104728183 43334872882146334657092275)
              ·
                refine ⟨65002309323219501985638413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43334872882146334657092275 65002309323219501985638413)
                ·
                  refine ⟨24375865996207313244614405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 65002309323219501985638413 24375865996207313244614405)
                  ·
                    refine ⟨4570474874288871233365201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24375865996207313244614405 4570474874288871233365201)
                    ·
                      refine ⟨3427856155716653425023901, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4570474874288871233365201 3427856155716653425023901)
                      ·
                        rfl

theorem cell23_6675726_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 1, 1, 3, 4, 2].length) (baseStart_6675726 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6675726 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6675726 prefixEnd_6675726 := by exact prefixLift 6675726
  have htrace : WordTrace (prefixWord ++ tailWord_6675726) baseStart_6675726 baseEnd_6675726 := by
    simpa [prefixWord, tailWord_6675726, baseEnd_6675726] using wordTrace_append hprefix tailTrace_6675726
  have hstable : (prefixWord ++ tailWord_6675726).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6675726).length < 2 ^ (prefixWord ++ tailWord_6675726).sum := by decide
  have hdescent : baseEnd_6675726 < baseStart_6675726 := by decide
  rcases family_descends (prefixWord ++ tailWord_6675726) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6675826 : List Nat := [3, 2, 1, 2, 1, 2, 1, 4, 3, 4]
def baseStart_6675826 : Nat := 118140960795 + 6675826 * 2 ^ 59
def prefixEnd_6675826 : Nat := 4983230072969 + 3 ^ 40 * 6675826 * 2
def baseEnd_6675826 : Nat := 1142635834594034344591147

theorem tailTrace_6675826 : CollatzResearch.WordTrace tailWord_6675826 prefixEnd_6675826 1142635834594034344591147 := by
  unfold tailWord_6675826
  simp only [CollatzResearch.WordTrace]
  refine ⟨60871844378157504288675833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 162324918341753344769802221 60871844378157504288675833)
  ·
    refine ⟨45653883283618128216506875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60871844378157504288675833 45653883283618128216506875)
    ·
      refine ⟨68480824925427192324760313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45653883283618128216506875 68480824925427192324760313)
      ·
        refine ⟨51360618694070394243570235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68480824925427192324760313 51360618694070394243570235)
        ·
          refine ⟨77040928041105591365355353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51360618694070394243570235 77040928041105591365355353)
          ·
            refine ⟨57780696030829193524016515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 77040928041105591365355353 57780696030829193524016515)
            ·
              refine ⟨86671044046243790286024773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57780696030829193524016515 86671044046243790286024773)
              ·
                refine ⟨16250820758670710678629645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 86671044046243790286024773 16250820758670710678629645)
                ·
                  refine ⟨6094057784501516504486117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16250820758670710678629645 6094057784501516504486117)
                  ·
                    refine ⟨1142635834594034344591147, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6094057784501516504486117 1142635834594034344591147)
                    ·
                      rfl

theorem cell23_6675826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 1, 4, 3, 4].length) (baseStart_6675826 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6675826 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6675826 prefixEnd_6675826 := by exact prefixLift 6675826
  have htrace : WordTrace (prefixWord ++ tailWord_6675826) baseStart_6675826 baseEnd_6675826 := by
    simpa [prefixWord, tailWord_6675826, baseEnd_6675826] using wordTrace_append hprefix tailTrace_6675826
  have hstable : (prefixWord ++ tailWord_6675826).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6675826).length < 2 ^ (prefixWord ++ tailWord_6675826).sum := by decide
  have hdescent : baseEnd_6675826 < baseStart_6675826 := by decide
  rcases family_descends (prefixWord ++ tailWord_6675826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6675836 : List Nat := [2, 2, 2, 1, 1, 1, 4, 3, 2, 2, 3]
def baseStart_6675836 : Nat := 118140960795 + 6675836 * 2 ^ 59
def prefixEnd_6675836 : Nat := 4983230072969 + 3 ^ 40 * 6675836 * 2
def baseEnd_6675836 : Nat := 3427912638588647994648395

theorem tailTrace_6675836 : CollatzResearch.WordTrace tailWord_6675836 prefixEnd_6675836 3427912638588647994648395 := by
  unfold tailWord_6675836
  simp only [CollatzResearch.WordTrace]
  refine ⟨121743871121296894431283681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 162325161495062525908378241 121743871121296894431283681)
  ·
    refine ⟨91307903340972670823462761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 121743871121296894431283681 91307903340972670823462761)
    ·
      refine ⟨68480927505729503117597071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 91307903340972670823462761 68480927505729503117597071)
      ·
        refine ⟨102721391258594254676395607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68480927505729503117597071 102721391258594254676395607)
        ·
          refine ⟨154082086887891382014593411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 102721391258594254676395607 154082086887891382014593411)
          ·
            refine ⟨231123130331837073021890117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 154082086887891382014593411 231123130331837073021890117)
            ·
              refine ⟨43335586937219451191604397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 231123130331837073021890117 43335586937219451191604397)
              ·
                refine ⟨16250845101457294196851649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 43335586937219451191604397 16250845101457294196851649)
                ·
                  refine ⟨12188133826092970647638737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16250845101457294196851649 12188133826092970647638737)
                  ·
                    refine ⟨9141100369569727985729053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12188133826092970647638737 9141100369569727985729053)
                    ·
                      refine ⟨3427912638588647994648395, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9141100369569727985729053 3427912638588647994648395)
                      ·
                        rfl

theorem cell23_6675836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 4, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 4, 3, 2, 2, 3].length) (baseStart_6675836 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6675836 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6675836 prefixEnd_6675836 := by exact prefixLift 6675836
  have htrace : WordTrace (prefixWord ++ tailWord_6675836) baseStart_6675836 baseEnd_6675836 := by
    simpa [prefixWord, tailWord_6675836, baseEnd_6675836] using wordTrace_append hprefix tailTrace_6675836
  have hstable : (prefixWord ++ tailWord_6675836).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6675836).length < 2 ^ (prefixWord ++ tailWord_6675836).sum := by decide
  have hdescent : baseEnd_6675836 < baseStart_6675836 := by decide
  rcases family_descends (prefixWord ++ tailWord_6675836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6675860 : List Nat := [2, 4, 2, 1, 2, 3, 1, 1, 3, 4]
def baseStart_6675860 : Nat := 118140960795 + 6675860 * 2 ^ 59
def prefixEnd_6675860 : Nat := 4983230072969 + 3 ^ 40 * 6675860 * 2
def baseEnd_6675860 : Nat := 1142641654041451966916095

theorem tailTrace_6675860 : CollatzResearch.WordTrace tailWord_6675860 prefixEnd_6675860 1142641654041451966916095 := by
  unfold tailWord_6675860
  simp only [CollatzResearch.WordTrace]
  refine ⟨121744308797253420480720517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 162325745063004560640960689 121744308797253420480720517)
  ·
    refine ⟨22827057899485016340135097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 121744308797253420480720517 22827057899485016340135097)
    ·
      refine ⟨17120293424613762255101323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22827057899485016340135097 17120293424613762255101323)
      ·
        refine ⟨25680440136920643382651985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17120293424613762255101323 25680440136920643382651985)
        ·
          refine ⟨19260330102690482536988989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25680440136920643382651985 19260330102690482536988989)
          ·
            refine ⟨7222623788508930951370871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19260330102690482536988989 7222623788508930951370871)
            ·
              refine ⟨10833935682763396427056307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7222623788508930951370871 10833935682763396427056307)
              ·
                refine ⟨16250903524145094640584461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10833935682763396427056307 16250903524145094640584461)
                ·
                  refine ⟨6094088821554410490219173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16250903524145094640584461 6094088821554410490219173)
                  ·
                    refine ⟨1142641654041451966916095, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6094088821554410490219173 1142641654041451966916095)
                    ·
                      rfl

theorem cell23_6675860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 3, 1, 1, 3, 4].length) (baseStart_6675860 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6675860 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6675860 prefixEnd_6675860 := by exact prefixLift 6675860
  have htrace : WordTrace (prefixWord ++ tailWord_6675860) baseStart_6675860 baseEnd_6675860 := by
    simpa [prefixWord, tailWord_6675860, baseEnd_6675860] using wordTrace_append hprefix tailTrace_6675860
  have hstable : (prefixWord ++ tailWord_6675860).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6675860).length < 2 ^ (prefixWord ++ tailWord_6675860).sum := by decide
  have hdescent : baseEnd_6675860 < baseStart_6675860 := by decide
  rcases family_descends (prefixWord ++ tailWord_6675860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6675919 : List Nat := [1, 1, 2, 1, 1, 4, 2, 1, 3, 1, 6]
def baseStart_6675919 : Nat := 118140960795 + 6675919 * 2 ^ 59
def prefixEnd_6675919 : Nat := 4983230072969 + 3 ^ 40 * 6675919 * 2
def baseEnd_6675919 : Nat := 3427955257482971169910513

theorem tailTrace_6675919 : CollatzResearch.WordTrace tailWord_6675919 prefixEnd_6675919 3427955257482971169910513 := by
  unfold tailWord_6675919
  simp only [CollatzResearch.WordTrace]
  refine ⟨243490769501293094037838811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162327179667528729358559207 243490769501293094037838811)
  ·
    refine ⟨365236154251939641056758217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 243490769501293094037838811 365236154251939641056758217)
    ·
      refine ⟨273927115688954730792568663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 365236154251939641056758217 273927115688954730792568663)
      ·
        refine ⟨410890673533432096188852995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 273927115688954730792568663 410890673533432096188852995)
        ·
          refine ⟨616336010300148144283279493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 410890673533432096188852995 616336010300148144283279493)
          ·
            refine ⟨115563001931277777053114905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 616336010300148144283279493 115563001931277777053114905)
            ·
              refine ⟨86672251448458332789836179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 115563001931277777053114905 86672251448458332789836179)
              ·
                refine ⟨130008377172687499184754269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 86672251448458332789836179 130008377172687499184754269)
                ·
                  refine ⟨48753141439757812194282851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 130008377172687499184754269 48753141439757812194282851)
                  ·
                    refine ⟨73129712159636718291424277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 48753141439757812194282851 73129712159636718291424277)
                    ·
                      refine ⟨3427955257482971169910513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 73129712159636718291424277 3427955257482971169910513)
                      ·
                        rfl

theorem cell23_6675919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 2, 1, 3, 1, 6].length) (baseStart_6675919 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6675919 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6675919 prefixEnd_6675919 := by exact prefixLift 6675919
  have htrace : WordTrace (prefixWord ++ tailWord_6675919) baseStart_6675919 baseEnd_6675919 := by
    simpa [prefixWord, tailWord_6675919, baseEnd_6675919] using wordTrace_append hprefix tailTrace_6675919
  have hstable : (prefixWord ++ tailWord_6675919).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6675919).length < 2 ^ (prefixWord ++ tailWord_6675919).sum := by decide
  have hdescent : baseEnd_6675919 < baseStart_6675919 := by decide
  rcases family_descends (prefixWord ++ tailWord_6675919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6675933 : List Nat := [1, 4, 3, 1, 1, 3, 2, 1, 1, 6]
def baseStart_6675933 : Nat := 118140960795 + 6675933 * 2 ^ 59
def prefixEnd_6675933 : Nat := 4983230072969 + 3 ^ 40 * 6675933 * 2
def baseEnd_6675933 : Nat := 1142654148737378038378483

theorem tailTrace_6675933 : CollatzResearch.WordTrace tailWord_6675933 prefixEnd_6675933 1142654148737378038378483 := by
  unfold tailWord_6675933
  simp only [CollatzResearch.WordTrace]
  refine ⟨243491280123242374428848453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162327520082161582952565635 243491280123242374428848453)
  ·
    refine ⟨45654615023107945205409085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 243491280123242374428848453 45654615023107945205409085)
    ·
      refine ⟨17120480633665479452028407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 45654615023107945205409085 17120480633665479452028407)
      ·
        refine ⟨25680720950498219178042611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17120480633665479452028407 25680720950498219178042611)
        ·
          refine ⟨38521081425747328767063917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25680720950498219178042611 38521081425747328767063917)
          ·
            refine ⟨14445405534655248287648969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38521081425747328767063917 14445405534655248287648969)
            ·
              refine ⟨10834054150991436215736727, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14445405534655248287648969 10834054150991436215736727)
              ·
                refine ⟨16251081226487154323605091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10834054150991436215736727 16251081226487154323605091)
                ·
                  refine ⟨24376621839730731485407637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16251081226487154323605091 24376621839730731485407637)
                  ·
                    refine ⟨1142654148737378038378483, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24376621839730731485407637 1142654148737378038378483)
                    ·
                      rfl

theorem cell23_6675933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 3, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 3, 2, 1, 1, 6].length) (baseStart_6675933 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6675933 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6675933 prefixEnd_6675933 := by exact prefixLift 6675933
  have htrace : WordTrace (prefixWord ++ tailWord_6675933) baseStart_6675933 baseEnd_6675933 := by
    simpa [prefixWord, tailWord_6675933, baseEnd_6675933] using wordTrace_append hprefix tailTrace_6675933
  have hstable : (prefixWord ++ tailWord_6675933).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6675933).length < 2 ^ (prefixWord ++ tailWord_6675933).sum := by decide
  have hdescent : baseEnd_6675933 < baseStart_6675933 := by decide
  rcases family_descends (prefixWord ++ tailWord_6675933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6675943 : List Nat := [1, 1, 5, 2, 1, 2, 2, 1, 3, 2, 3]
def baseStart_6675943 : Nat := 118140960795 + 6675943 * 2 ^ 59
def prefixEnd_6675943 : Nat := 4983230072969 + 3 ^ 40 * 6675943 * 2
def baseEnd_6675943 : Nat := 3427967581018679076010403

theorem tailTrace_6675943 : CollatzResearch.WordTrace tailWord_6675943 prefixEnd_6675943 3427967581018679076010403 := by
  unfold tailWord_6675943
  simp only [CollatzResearch.WordTrace]
  refine ⟨243491644853206146136712483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162327763235470764091141655 243491644853206146136712483)
  ·
    refine ⟨365237467279809219205068725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 243491644853206146136712483 365237467279809219205068725)
    ·
      refine ⟨34241012557482114300475193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 365237467279809219205068725 34241012557482114300475193)
      ·
        refine ⟨25680759418111585725356395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34241012557482114300475193 25680759418111585725356395)
        ·
          refine ⟨38521139127167378588034593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25680759418111585725356395 38521139127167378588034593)
          ·
            refine ⟨28890854345375533941025945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38521139127167378588034593 28890854345375533941025945)
            ·
              refine ⟨21668140759031650455769459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28890854345375533941025945 21668140759031650455769459)
              ·
                refine ⟨32502211138547475683654189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21668140759031650455769459 32502211138547475683654189)
                ·
                  refine ⟨12188329176955303381370321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32502211138547475683654189 12188329176955303381370321)
                  ·
                    refine ⟨9141246882716477536027741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12188329176955303381370321 9141246882716477536027741)
                    ·
                      refine ⟨3427967581018679076010403, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9141246882716477536027741 3427967581018679076010403)
                      ·
                        rfl

theorem cell23_6675943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 2, 1, 3, 2, 3].length) (baseStart_6675943 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6675943 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6675943 prefixEnd_6675943 := by exact prefixLift 6675943
  have htrace : WordTrace (prefixWord ++ tailWord_6675943) baseStart_6675943 baseEnd_6675943 := by
    simpa [prefixWord, tailWord_6675943, baseEnd_6675943] using wordTrace_append hprefix tailTrace_6675943
  have hstable : (prefixWord ++ tailWord_6675943).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6675943).length < 2 ^ (prefixWord ++ tailWord_6675943).sum := by decide
  have hdescent : baseEnd_6675943 < baseStart_6675943 := by decide
  rcases family_descends (prefixWord ++ tailWord_6675943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6675957 : List Nat := [1, 3, 5, 1, 1, 1, 4, 1, 1, 1, 4]
def baseStart_6675957 : Nat := 118140960795 + 6675957 * 2 ^ 59
def prefixEnd_6675957 : Nat := 4983230072969 + 3 ^ 40 * 6675957 * 2
def baseEnd_6675957 : Nat := 3427974769747842021235339

theorem tailTrace_6675957 : CollatzResearch.WordTrace tailWord_6675957 prefixEnd_6675957 3427974769747842021235339 := by
  unfold tailWord_6675957
  simp only [CollatzResearch.WordTrace]
  refine ⟨243492155475155426527722125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162328103650103617685148083 243492155475155426527722125)
  ·
    refine ⟨91309558303183284947895797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 243492155475155426527722125 91309558303183284947895797)
    ·
      refine ⟨8560271090923432963865231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 91309558303183284947895797 8560271090923432963865231)
      ·
        refine ⟨12840406636385149445797847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8560271090923432963865231 12840406636385149445797847)
        ·
          refine ⟨19260609954577724168696771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12840406636385149445797847 19260609954577724168696771)
          ·
            refine ⟨28890914931866586253045157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19260609954577724168696771 28890914931866586253045157)
            ·
              refine ⟨5417046549724984922445967, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 28890914931866586253045157 5417046549724984922445967)
              ·
                refine ⟨8125569824587477383668951, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5417046549724984922445967 8125569824587477383668951)
                ·
                  refine ⟨12188354736881216075503427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8125569824587477383668951 12188354736881216075503427)
                  ·
                    refine ⟨18282532105321824113255141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12188354736881216075503427 18282532105321824113255141)
                    ·
                      refine ⟨3427974769747842021235339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18282532105321824113255141 3427974769747842021235339)
                      ·
                        rfl

theorem cell23_6675957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 4, 1, 1, 1, 4].length) (baseStart_6675957 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6675957 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6675957 prefixEnd_6675957 := by exact prefixLift 6675957
  have htrace : WordTrace (prefixWord ++ tailWord_6675957) baseStart_6675957 baseEnd_6675957 := by
    simpa [prefixWord, tailWord_6675957, baseEnd_6675957] using wordTrace_append hprefix tailTrace_6675957
  have hstable : (prefixWord ++ tailWord_6675957).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6675957).length < 2 ^ (prefixWord ++ tailWord_6675957).sum := by decide
  have hdescent : baseEnd_6675957 < baseStart_6675957 := by decide
  rcases family_descends (prefixWord ++ tailWord_6675957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6675959 : List Nat := [1, 1, 3, 1, 1, 1, 1, 4, 1, 9]
def baseStart_6675959 : Nat := 118140960795 + 6675959 * 2 ^ 59
def prefixEnd_6675959 : Nat := 4983230072969 + 3 ^ 40 * 6675959 * 2
def baseEnd_6675959 : Nat := 1142658598903050337803443

theorem tailTrace_6675959 : CollatzResearch.WordTrace tailWord_6675959 prefixEnd_6675959 1142658598903050337803443 := by
  unfold tailWord_6675959
  simp only [CollatzResearch.WordTrace]
  refine ⟨243492228421148180869294931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162328152280765453912863287 243492228421148180869294931)
  ·
    refine ⟨365238342631722271303942397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 243492228421148180869294931 365238342631722271303942397)
    ·
      refine ⟨136964378486895851738978399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 365238342631722271303942397 136964378486895851738978399)
      ·
        refine ⟨205446567730343777608467599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 136964378486895851738978399 205446567730343777608467599)
        ·
          refine ⟨308169851595515666412701399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 205446567730343777608467599 308169851595515666412701399)
          ·
            refine ⟨462254777393273499619052099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 308169851595515666412701399 462254777393273499619052099)
            ·
              refine ⟨693382166089910249428578149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 462254777393273499619052099 693382166089910249428578149)
              ·
                refine ⟨130009156141858171767858403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 693382166089910249428578149 130009156141858171767858403)
                ·
                  refine ⟨195013734212787257651787605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 130009156141858171767858403 195013734212787257651787605)
                  ·
                    refine ⟨1142658598903050337803443, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 195013734212787257651787605 1142658598903050337803443)
                    ·
                      rfl

theorem cell23_6675959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 4, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 4, 1, 9].length) (baseStart_6675959 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6675959 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6675959 prefixEnd_6675959 := by exact prefixLift 6675959
  have htrace : WordTrace (prefixWord ++ tailWord_6675959) baseStart_6675959 baseEnd_6675959 := by
    simpa [prefixWord, tailWord_6675959, baseEnd_6675959] using wordTrace_append hprefix tailTrace_6675959
  have hstable : (prefixWord ++ tailWord_6675959).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6675959).length < 2 ^ (prefixWord ++ tailWord_6675959).sum := by decide
  have hdescent : baseEnd_6675959 < baseStart_6675959 := by decide
  rcases family_descends (prefixWord ++ tailWord_6675959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6675960 : List Nat := [2, 1, 2, 1, 1, 5, 4, 1, 1, 2, 3]
def baseStart_6675960 : Nat := 118140960795 + 6675960 * 2 ^ 59
def prefixEnd_6675960 : Nat := 4983230072969 + 3 ^ 40 * 6675960 * 2
def baseEnd_6675960 : Nat := 3427976310189805509497825

theorem tailTrace_6675960 : CollatzResearch.WordTrace tailWord_6675960 prefixEnd_6675960 3427976310189805509497825 := by
  unfold tailWord_6675960
  simp only [CollatzResearch.WordTrace]
  refine ⟨121746132447072279020040667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 162328176596096372026720889 121746132447072279020040667)
  ·
    refine ⟨182619198670608418530061001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121746132447072279020040667 182619198670608418530061001)
    ·
      refine ⟨136964399002956313897545751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 182619198670608418530061001 136964399002956313897545751)
      ·
        refine ⟨205446598504434470846318627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 136964399002956313897545751 205446598504434470846318627)
        ·
          refine ⟨308169897756651706269477941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 205446598504434470846318627 308169897756651706269477941)
          ·
            refine ⟨28890927914686097462763557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 308169897756651706269477941 28890927914686097462763557)
            ·
              refine ⟨5417048984003643274268167, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 28890927914686097462763557 5417048984003643274268167)
              ·
                refine ⟨8125573476005464911402251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5417048984003643274268167 8125573476005464911402251)
                ·
                  refine ⟨12188360214008197367103377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8125573476005464911402251 12188360214008197367103377)
                  ·
                    refine ⟨9141270160506148025327533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12188360214008197367103377 9141270160506148025327533)
                    ·
                      refine ⟨3427976310189805509497825, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9141270160506148025327533 3427976310189805509497825)
                      ·
                        rfl

theorem cell23_6675960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 4, 1, 1, 2, 3].length) (baseStart_6675960 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6675960 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6675960 prefixEnd_6675960 := by exact prefixLift 6675960
  have htrace : WordTrace (prefixWord ++ tailWord_6675960) baseStart_6675960 baseEnd_6675960 := by
    simpa [prefixWord, tailWord_6675960, baseEnd_6675960] using wordTrace_append hprefix tailTrace_6675960
  have hstable : (prefixWord ++ tailWord_6675960).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6675960).length < 2 ^ (prefixWord ++ tailWord_6675960).sum := by decide
  have hdescent : baseEnd_6675960 < baseStart_6675960 := by decide
  rcases family_descends (prefixWord ++ tailWord_6675960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6676008 : List Nat := [2, 1, 5, 2, 3, 1, 1, 3, 1, 2, 2]
def baseStart_6676008 : Nat := 118140960795 + 6676008 * 2 ^ 59
def prefixEnd_6676008 : Nat := 4983230072969 + 3 ^ 40 * 6676008 * 2
def baseEnd_6676008 : Nat := 3428000957261221321697605

theorem tailTrace_6676008 : CollatzResearch.WordTrace tailWord_6676008 prefixEnd_6676008 3428000957261221321697605 := by
  unfold tailWord_6676008
  simp only [CollatzResearch.WordTrace]
  refine ⟨121747007798985331118914339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 162329343731980441491885785 121747007798985331118914339)
  ·
    refine ⟨182620511698477996678371509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121747007798985331118914339 182620511698477996678371509)
    ·
      refine ⟨17120672971732312188597329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 182620511698477996678371509 17120672971732312188597329)
      ·
        refine ⟨12840504728799234141447997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17120672971732312188597329 12840504728799234141447997)
        ·
          refine ⟨4815189273299712803042999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12840504728799234141447997 4815189273299712803042999)
          ·
            refine ⟨7222783909949569204564499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4815189273299712803042999 7222783909949569204564499)
            ·
              refine ⟨10834175864924353806846749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7222783909949569204564499 10834175864924353806846749)
              ·
                refine ⟨4062815949346632677567531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10834175864924353806846749 4062815949346632677567531)
                ·
                  refine ⟨6094223924019949016351297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4062815949346632677567531 6094223924019949016351297)
                  ·
                    refine ⟨4570667943014961762263473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6094223924019949016351297 4570667943014961762263473)
                    ·
                      refine ⟨3428000957261221321697605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4570667943014961762263473 3428000957261221321697605)
                      ·
                        rfl

theorem cell23_6676008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 3, 1, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 3, 1, 1, 3, 1, 2, 2].length) (baseStart_6676008 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6676008 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6676008 prefixEnd_6676008 := by exact prefixLift 6676008
  have htrace : WordTrace (prefixWord ++ tailWord_6676008) baseStart_6676008 baseEnd_6676008 := by
    simpa [prefixWord, tailWord_6676008, baseEnd_6676008] using wordTrace_append hprefix tailTrace_6676008
  have hstable : (prefixWord ++ tailWord_6676008).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6676008).length < 2 ^ (prefixWord ++ tailWord_6676008).sum := by decide
  have hdescent : baseEnd_6676008 < baseStart_6676008 := by decide
  rcases family_descends (prefixWord ++ tailWord_6676008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6676016 : List Nat := [2, 1, 1, 1, 2, 3, 1, 2, 1, 6, 3]
def baseStart_6676016 : Nat := 118140960795 + 6676016 * 2 ^ 59
def prefixEnd_6676016 : Nat := 4983230072969 + 3 ^ 40 * 6676016 * 2
def baseEnd_6676016 : Nat := 3428005065106457290397567

theorem tailTrace_6676016 : CollatzResearch.WordTrace tailWord_6676016 prefixEnd_6676016 3428005065106457290397567 := by
  unfold tailWord_6676016
  simp only [CollatzResearch.WordTrace]
  refine ⟨121747153690970839802059951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 162329538254627786402746601 121747153690970839802059951)
  ·
    refine ⟨182620730536456259703089927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121747153690970839802059951 182620730536456259703089927)
    ·
      refine ⟨273931095804684389554634891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 182620730536456259703089927 273931095804684389554634891)
      ·
        refine ⟨410896643707026584331952337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 273931095804684389554634891 410896643707026584331952337)
        ·
          refine ⟨308172482780269938248964253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 410896643707026584331952337 308172482780269938248964253)
          ·
            refine ⟨115564681042601226843361595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 308172482780269938248964253 115564681042601226843361595)
            ·
              refine ⟨173347021563901840265042393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 115564681042601226843361595 173347021563901840265042393)
              ·
                refine ⟨130010266172926380198781795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 173347021563901840265042393 130010266172926380198781795)
                ·
                  refine ⟨195015399259389570298172693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 130010266172926380198781795 195015399259389570298172693)
                  ·
                    refine ⟨9141346840283886107726845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 195015399259389570298172693 9141346840283886107726845)
                    ·
                      refine ⟨3428005065106457290397567, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9141346840283886107726845 3428005065106457290397567)
                      ·
                        rfl

theorem cell23_6676016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 1, 2, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 1, 2, 1, 6, 3].length) (baseStart_6676016 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6676016 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6676016 prefixEnd_6676016 := by exact prefixLift 6676016
  have htrace : WordTrace (prefixWord ++ tailWord_6676016) baseStart_6676016 baseEnd_6676016 := by
    simpa [prefixWord, tailWord_6676016, baseEnd_6676016] using wordTrace_append hprefix tailTrace_6676016
  have hstable : (prefixWord ++ tailWord_6676016).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6676016).length < 2 ^ (prefixWord ++ tailWord_6676016).sum := by decide
  have hdescent : baseEnd_6676016 < baseStart_6676016 := by decide
  rcases family_descends (prefixWord ++ tailWord_6676016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6676033 : List Nat := [1, 2, 5, 1, 1, 1, 2, 1, 2, 4, 3]
def baseStart_6676033 : Nat := 118140960795 + 6676033 * 2 ^ 59
def prefixEnd_6676033 : Nat := 4983230072969 + 3 ^ 40 * 6676033 * 2
def baseEnd_6676033 : Nat := 3428013794277583723884989

theorem tailTrace_6676033 : CollatzResearch.WordTrace tailWord_6676033 prefixEnd_6676033 3428013794277583723884989 := by
  unfold tailWord_6676033
  simp only [CollatzResearch.WordTrace]
  refine ⟨243494927422880091507488753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162329951615253394338325835 243494927422880091507488753)
  ·
    refine ⟨182621195567160068630616565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 243494927422880091507488753 182621195567160068630616565)
    ·
      refine ⟨17120737084421256434120303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 182621195567160068630616565 17120737084421256434120303)
      ·
        refine ⟨25681105626631884651180455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17120737084421256434120303 25681105626631884651180455)
        ·
          refine ⟨38521658439947826976770683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25681105626631884651180455 38521658439947826976770683)
          ·
            refine ⟨57782487659921740465156025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38521658439947826976770683 57782487659921740465156025)
            ·
              refine ⟨43336865744941305348867019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 57782487659921740465156025 43336865744941305348867019)
              ·
                refine ⟨65005298617411958023300529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43336865744941305348867019 65005298617411958023300529)
                ·
                  refine ⟨48753973963058968517475397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 65005298617411958023300529 48753973963058968517475397)
                  ·
                    refine ⟨9141370118073556597026637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 48753973963058968517475397 9141370118073556597026637)
                    ·
                      refine ⟨3428013794277583723884989, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9141370118073556597026637 3428013794277583723884989)
                      ·
                        rfl

theorem cell23_6676033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 2, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 2, 1, 2, 4, 3].length) (baseStart_6676033 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6676033 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6676033 prefixEnd_6676033 := by exact prefixLift 6676033
  have htrace : WordTrace (prefixWord ++ tailWord_6676033) baseStart_6676033 baseEnd_6676033 := by
    simpa [prefixWord, tailWord_6676033, baseEnd_6676033] using wordTrace_append hprefix tailTrace_6676033
  have hstable : (prefixWord ++ tailWord_6676033).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6676033).length < 2 ^ (prefixWord ++ tailWord_6676033).sum := by decide
  have hdescent : baseEnd_6676033 < baseStart_6676033 := by decide
  rcases family_descends (prefixWord ++ tailWord_6676033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6676093 : List Nat := [1, 4, 1, 1, 4, 1, 2, 1, 1, 2, 5]
def baseStart_6676093 : Nat := 118140960795 + 6676093 * 2 ^ 59
def prefixEnd_6676093 : Nat := 4983230072969 + 3 ^ 40 * 6676093 * 2
def baseEnd_6676093 : Nat := 3428044603116853489134713

theorem tailTrace_6676093 : CollatzResearch.WordTrace tailWord_6676093 prefixEnd_6676093 3428044603116853489134713 := by
  unfold tailWord_6676093
  simp only [CollatzResearch.WordTrace]
  refine ⟨243497115802662721754672933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162331410535108481169781955 243497115802662721754672933)
  ·
    refine ⟨45655709212999260329001175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 243497115802662721754672933 45655709212999260329001175)
    ·
      refine ⟨68483563819498890493501763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45655709212999260329001175 68483563819498890493501763)
      ·
        refine ⟨102725345729248335740252645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68483563819498890493501763 102725345729248335740252645)
        ·
          refine ⟨19261002324234062951297371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 102725345729248335740252645 19261002324234062951297371)
          ·
            refine ⟨28891503486351094426946057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19261002324234062951297371 28891503486351094426946057)
            ·
              refine ⟨21668627614763320820209543, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28891503486351094426946057 21668627614763320820209543)
              ·
                refine ⟨32502941422144981230314315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21668627614763320820209543 32502941422144981230314315)
                ·
                  refine ⟨48754412133217471845471473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32502941422144981230314315 48754412133217471845471473)
                  ·
                    refine ⟨36565809099913103884103605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 48754412133217471845471473 36565809099913103884103605)
                    ·
                      refine ⟨3428044603116853489134713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36565809099913103884103605 3428044603116853489134713)
                      ·
                        rfl

theorem cell23_6676093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 2, 1, 1, 2, 5].length) (baseStart_6676093 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6676093 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6676093 prefixEnd_6676093 := by exact prefixLift 6676093
  have htrace : WordTrace (prefixWord ++ tailWord_6676093) baseStart_6676093 baseEnd_6676093 := by
    simpa [prefixWord, tailWord_6676093, baseEnd_6676093] using wordTrace_append hprefix tailTrace_6676093
  have hstable : (prefixWord ++ tailWord_6676093).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6676093).length < 2 ^ (prefixWord ++ tailWord_6676093).sum := by decide
  have hdescent : baseEnd_6676093 < baseStart_6676093 := by decide
  rcases family_descends (prefixWord ++ tailWord_6676093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6676120 : List Nat := [2, 1, 2, 4, 1, 2, 3, 1, 2, 1, 4]
def baseStart_6676120 : Nat := 118140960795 + 6676120 * 2 ^ 59
def prefixEnd_6676120 : Nat := 4983230072969 + 3 ^ 40 * 6676120 * 2
def baseEnd_6676120 : Nat := 3428058467094524883497089

theorem tailTrace_6676120 : CollatzResearch.WordTrace tailWord_6676120 prefixEnd_6676120 3428058467094524883497089 := by
  unfold tailWord_6676120
  simp only [CollatzResearch.WordTrace]
  refine ⟨121749050286782452682952907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 162332067049043270243937209 121749050286782452682952907)
  ·
    refine ⟨182623575430173679024429361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121749050286782452682952907 182623575430173679024429361)
    ·
      refine ⟨136967681572630259268322021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 182623575430173679024429361 136967681572630259268322021)
      ·
        refine ⟨25681440294868173612810379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 136967681572630259268322021 25681440294868173612810379)
        ·
          refine ⟨38522160442302260419215569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25681440294868173612810379 38522160442302260419215569)
          ·
            refine ⟨28891620331726695314411677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38522160442302260419215569 28891620331726695314411677)
            ·
              refine ⟨10834357624397510742904379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28891620331726695314411677 10834357624397510742904379)
              ·
                refine ⟨16251536436596266114356569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10834357624397510742904379 16251536436596266114356569)
                ·
                  refine ⟨12188652327447199585767427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16251536436596266114356569 12188652327447199585767427)
                  ·
                    refine ⟨18282978491170799378651141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12188652327447199585767427 18282978491170799378651141)
                    ·
                      refine ⟨3428058467094524883497089, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18282978491170799378651141 3428058467094524883497089)
                      ·
                        rfl

theorem cell23_6676120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 3, 1, 2, 1, 4].length) (baseStart_6676120 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6676120 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6676120 prefixEnd_6676120 := by exact prefixLift 6676120
  have htrace : WordTrace (prefixWord ++ tailWord_6676120) baseStart_6676120 baseEnd_6676120 := by
    simpa [prefixWord, tailWord_6676120, baseEnd_6676120] using wordTrace_append hprefix tailTrace_6676120
  have hstable : (prefixWord ++ tailWord_6676120).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6676120).length < 2 ^ (prefixWord ++ tailWord_6676120).sum := by decide
  have hdescent : baseEnd_6676120 < baseStart_6676120 := by decide
  rcases family_descends (prefixWord ++ tailWord_6676120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6676160 : List Nat := [2, 1, 1, 2, 4, 1, 5, 1, 6]
def baseStart_6676160 : Nat := 118140960795 + 6676160 * 2 ^ 59
def prefixEnd_6676160 : Nat := 4983230072969 + 3 ^ 40 * 6676160 * 2
def baseEnd_6676160 : Nat := 380897667368967191888545

theorem tailTrace_6676160 : CollatzResearch.WordTrace tailWord_6676160 prefixEnd_6676160 380897667368967191888545 := by
  unfold tailWord_6676160
  simp only [CollatzResearch.WordTrace]
  refine ⟨121749779746709996098680967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 162333039662279994798241289 121749779746709996098680967)
  ·
    refine ⟨182624669620064994148021451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121749779746709996098680967 182624669620064994148021451)
    ·
      refine ⟨273937004430097491222032177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 182624669620064994148021451 273937004430097491222032177)
      ·
        refine ⟨205452753322573118416524133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 273937004430097491222032177 205452753322573118416524133)
        ·
          refine ⟨38522391247982459703098275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 205452753322573118416524133 38522391247982459703098275)
          ·
            refine ⟨57783586871973689554647413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38522391247982459703098275 57783586871973689554647413)
            ·
              refine ⟨5417211269247533395748195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 57783586871973689554647413 5417211269247533395748195)
              ·
                refine ⟨8125816903871300093622293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5417211269247533395748195 8125816903871300093622293)
                ·
                  refine ⟨380897667368967191888545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8125816903871300093622293 380897667368967191888545)
                  ·
                    rfl

theorem cell23_6676160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 5, 1, 6].length) (baseStart_6676160 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6676160 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6676160 prefixEnd_6676160 := by exact prefixLift 6676160
  have htrace : WordTrace (prefixWord ++ tailWord_6676160) baseStart_6676160 baseEnd_6676160 := by
    simpa [prefixWord, tailWord_6676160, baseEnd_6676160] using wordTrace_append hprefix tailTrace_6676160
  have hstable : (prefixWord ++ tailWord_6676160).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6676160).length < 2 ^ (prefixWord ++ tailWord_6676160).sum := by decide
  have hdescent : baseEnd_6676160 < baseStart_6676160 := by decide
  rcases family_descends (prefixWord ++ tailWord_6676160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6676197 : List Nat := [1, 3, 1, 4, 1, 1, 3, 2, 2, 3, 2]
def baseStart_6676197 : Nat := 118140960795 + 6676197 * 2 ^ 59
def prefixEnd_6676197 : Nat := 4983230072969 + 3 ^ 40 * 6676197 * 2
def baseEnd_6676197 : Nat := 3428098005104921082234235

theorem tailTrace_6676197 : CollatzResearch.WordTrace tailWord_6676197 prefixEnd_6676197 3428098005104921082234235 := by
  unfold tailWord_6676197
  simp only [CollatzResearch.WordTrace]
  refine ⟨243500908994285947516458845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162333939329523965010972563 243500908994285947516458845)
  ·
    refine ⟨91312840872857230318672067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 243500908994285947516458845 91312840872857230318672067)
    ·
      refine ⟨136969261309285845478008101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91312840872857230318672067 136969261309285845478008101)
      ·
        refine ⟨25681736495491096027126519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 136969261309285845478008101 25681736495491096027126519)
        ·
          refine ⟨38522604743236644040689779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25681736495491096027126519 38522604743236644040689779)
          ·
            refine ⟨57783907114854966061034669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38522604743236644040689779 57783907114854966061034669)
            ·
              refine ⟨21668965168070612272888001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 57783907114854966061034669 21668965168070612272888001)
              ·
                refine ⟨16251723876052959204666001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21668965168070612272888001 16251723876052959204666001)
                ·
                  refine ⟨12188792907039719403499501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16251723876052959204666001 12188792907039719403499501)
                  ·
                    refine ⟨4570797340139894776312313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12188792907039719403499501 4570797340139894776312313)
                    ·
                      refine ⟨3428098005104921082234235, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4570797340139894776312313 3428098005104921082234235)
                      ·
                        rfl

theorem cell23_6676197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 3, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 3, 2, 2, 3, 2].length) (baseStart_6676197 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6676197 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6676197 prefixEnd_6676197 := by exact prefixLift 6676197
  have htrace : WordTrace (prefixWord ++ tailWord_6676197) baseStart_6676197 baseEnd_6676197 := by
    simpa [prefixWord, tailWord_6676197, baseEnd_6676197] using wordTrace_append hprefix tailTrace_6676197
  have hstable : (prefixWord ++ tailWord_6676197).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6676197).length < 2 ^ (prefixWord ++ tailWord_6676197).sum := by decide
  have hdescent : baseEnd_6676197 < baseStart_6676197 := by decide
  rcases family_descends (prefixWord ++ tailWord_6676197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6676210 : List Nat := [3, 2, 1, 3, 1, 1, 2, 2, 3, 1, 4]
def baseStart_6676210 : Nat := 118140960795 + 6676210 * 2 ^ 59
def prefixEnd_6676210 : Nat := 4983230072969 + 3 ^ 40 * 6676210 * 2
def baseEnd_6676210 : Nat := 3428104680353429531371675

theorem tailTrace_6676210 : CollatzResearch.WordTrace tailWord_6676210 prefixEnd_6676210 3428104680353429531371675 := by
  unfold tailWord_6676210
  simp only [CollatzResearch.WordTrace]
  refine ⟨60875345785809712684170521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 162334255428825900491121389 60875345785809712684170521)
  ·
    refine ⟨45656509339357284513127891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60875345785809712684170521 45656509339357284513127891)
    ·
      refine ⟨68484764009035926769691837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45656509339357284513127891 68484764009035926769691837)
      ·
        refine ⟨25681786503388472538634439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 68484764009035926769691837 25681786503388472538634439)
        ·
          refine ⟨38522679755082708807951659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25681786503388472538634439 38522679755082708807951659)
          ·
            refine ⟨57784019632624063211927489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38522679755082708807951659 57784019632624063211927489)
            ·
              refine ⟨43338014724468047408945617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 57784019632624063211927489 43338014724468047408945617)
              ·
                refine ⟨32503511043351035556709213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43338014724468047408945617 32503511043351035556709213)
                ·
                  refine ⟨12188816641256638333765955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32503511043351035556709213 12188816641256638333765955)
                  ·
                    refine ⟨18283224961884957500648933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12188816641256638333765955 18283224961884957500648933)
                    ·
                      refine ⟨3428104680353429531371675, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18283224961884957500648933 3428104680353429531371675)
                      ·
                        rfl

theorem cell23_6676210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 2, 2, 3, 1, 4].length) (baseStart_6676210 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6676210 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6676210 prefixEnd_6676210 := by exact prefixLift 6676210
  have htrace : WordTrace (prefixWord ++ tailWord_6676210) baseStart_6676210 baseEnd_6676210 := by
    simpa [prefixWord, tailWord_6676210, baseEnd_6676210] using wordTrace_append hprefix tailTrace_6676210
  have hstable : (prefixWord ++ tailWord_6676210).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6676210).length < 2 ^ (prefixWord ++ tailWord_6676210).sum := by decide
  have hdescent : baseEnd_6676210 < baseStart_6676210 := by decide
  rcases family_descends (prefixWord ++ tailWord_6676210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6676223 : List Nat := [1, 1, 2, 2, 1, 3, 4, 1, 1, 1, 6]
def baseStart_6676223 : Nat := 118140960795 + 6676223 * 2 ^ 59
def prefixEnd_6676223 : Nat := 4983230072969 + 3 ^ 40 * 6676223 * 2
def baseEnd_6676223 : Nat := 3428111355601937980509115

theorem tailTrace_6676223 : CollatzResearch.WordTrace tailWord_6676223 prefixEnd_6676223 3428111355601937980509115 := by
  unfold tailWord_6676223
  simp only [CollatzResearch.WordTrace]
  refine ⟨243501857292191753956905323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162334571528127835971270215 243501857292191753956905323)
  ·
    refine ⟨365252785938287630935357985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 243501857292191753956905323 365252785938287630935357985)
    ·
      refine ⟨273939589453715723201518489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 365252785938287630935357985 273939589453715723201518489)
      ·
        refine ⟨205454692090286792401138867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 273939589453715723201518489 205454692090286792401138867)
        ·
          refine ⟨308182038135430188601708301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 205454692090286792401138867 308182038135430188601708301)
          ·
            refine ⟨115568264300786320725640613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 308182038135430188601708301 115568264300786320725640613)
            ·
              refine ⟨21669049556397435136057615, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 115568264300786320725640613 21669049556397435136057615)
              ·
                refine ⟨32503574334596152704086423, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21669049556397435136057615 32503574334596152704086423)
                ·
                  refine ⟨48755361501894229056129635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32503574334596152704086423 48755361501894229056129635)
                  ·
                    refine ⟨73133042252841343584194453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 48755361501894229056129635 73133042252841343584194453)
                    ·
                      refine ⟨3428111355601937980509115, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 73133042252841343584194453 3428111355601937980509115)
                      ·
                        rfl

theorem cell23_6676223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 4, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 4, 1, 1, 1, 6].length) (baseStart_6676223 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6676223 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6676223 prefixEnd_6676223 := by exact prefixLift 6676223
  have htrace : WordTrace (prefixWord ++ tailWord_6676223) baseStart_6676223 baseEnd_6676223 := by
    simpa [prefixWord, tailWord_6676223, baseEnd_6676223] using wordTrace_append hprefix tailTrace_6676223
  have hstable : (prefixWord ++ tailWord_6676223).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6676223).length < 2 ^ (prefixWord ++ tailWord_6676223).sum := by decide
  have hdescent : baseEnd_6676223 < baseStart_6676223 := by decide
  rcases family_descends (prefixWord ++ tailWord_6676223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6676227 : List Nat := [1, 1, 1, 3, 2, 2, 2, 4, 3, 2, 2]
def baseStart_6676227 : Nat := 118140960795 + 6676227 * 2 ^ 59
def prefixEnd_6676227 : Nat := 4983230072969 + 3 ^ 40 * 6676227 * 2
def baseEnd_6676227 : Nat := 3428113409524555964859097

theorem tailTrace_6676227 : CollatzResearch.WordTrace tailWord_6676227 prefixEnd_6676227 3428113409524555964859097 := by
  unfold tailWord_6676227
  simp only [CollatzResearch.WordTrace]
  refine ⟨243502003184177262640050935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162334668789451508426700623 243502003184177262640050935)
  ·
    refine ⟨365253004776265893960076403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 243502003184177262640050935 365253004776265893960076403)
    ·
      refine ⟨547879507164398840940114605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 365253004776265893960076403 547879507164398840940114605)
      ·
        refine ⟨205454815186649565352542977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 547879507164398840940114605 205454815186649565352542977)
        ·
          refine ⟨154091111389987174014407233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 205454815186649565352542977 154091111389987174014407233)
          ·
            refine ⟨115568333542490380510805425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 154091111389987174014407233 115568333542490380510805425)
            ·
              refine ⟨86676250156867785383104069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 115568333542490380510805425 86676250156867785383104069)
              ·
                refine ⟨16251796904412709759332013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 86676250156867785383104069 16251796904412709759332013)
                ·
                  refine ⟨6094423839154766159749505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16251796904412709759332013 6094423839154766159749505)
                  ·
                    refine ⟨4570817879366074619812129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6094423839154766159749505 4570817879366074619812129)
                    ·
                      refine ⟨3428113409524555964859097, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4570817879366074619812129 3428113409524555964859097)
                      ·
                        rfl

theorem cell23_6676227_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 2, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 2, 4, 3, 2, 2].length) (baseStart_6676227 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6676227 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6676227 prefixEnd_6676227 := by exact prefixLift 6676227
  have htrace : WordTrace (prefixWord ++ tailWord_6676227) baseStart_6676227 baseEnd_6676227 := by
    simpa [prefixWord, tailWord_6676227, baseEnd_6676227] using wordTrace_append hprefix tailTrace_6676227
  have hstable : (prefixWord ++ tailWord_6676227).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6676227).length < 2 ^ (prefixWord ++ tailWord_6676227).sum := by decide
  have hdescent : baseEnd_6676227 < baseStart_6676227 := by decide
  rcases family_descends (prefixWord ++ tailWord_6676227) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6676247 : List Nat := [1, 1, 3, 4, 2, 3, 1, 1, 1, 1, 5]
def baseStart_6676247 : Nat := 118140960795 + 6676247 * 2 ^ 59
def prefixEnd_6676247 : Nat := 4983230072969 + 3 ^ 40 * 6676247 * 2
def baseEnd_6676247 : Nat := 3428123679137645886609005

theorem tailTrace_6676247 : CollatzResearch.WordTrace tailWord_6676247 prefixEnd_6676247 3428123679137645886609005 := by
  unfold tailWord_6676247
  simp only [CollatzResearch.WordTrace]
  refine ⟨243502732644104806055778995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162335155096069870703852663 243502732644104806055778995)
  ·
    refine ⟨365254098966157209083668493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 243502732644104806055778995 365254098966157209083668493)
    ·
      refine ⟨136970287112308953406375685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 365254098966157209083668493 136970287112308953406375685)
      ·
        refine ⟨25681928833557928763695441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 136970287112308953406375685 25681928833557928763695441)
        ·
          refine ⟨19261446625168446572771581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25681928833557928763695441 19261446625168446572771581)
          ·
            refine ⟨7223042484438167464789343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19261446625168446572771581 7223042484438167464789343)
            ·
              refine ⟨10834563726657251197184015, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7223042484438167464789343 10834563726657251197184015)
              ·
                refine ⟨16251845589985876795776023, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10834563726657251197184015 16251845589985876795776023)
                ·
                  refine ⟨24377768384978815193664035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16251845589985876795776023 24377768384978815193664035)
                  ·
                    refine ⟨36566652577468222790496053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24377768384978815193664035 36566652577468222790496053)
                    ·
                      refine ⟨3428123679137645886609005, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36566652577468222790496053 3428123679137645886609005)
                      ·
                        rfl

theorem cell23_6676247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 3, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 3, 1, 1, 1, 1, 5].length) (baseStart_6676247 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6676247 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6676247 prefixEnd_6676247 := by exact prefixLift 6676247
  have htrace : WordTrace (prefixWord ++ tailWord_6676247) baseStart_6676247 baseEnd_6676247 := by
    simpa [prefixWord, tailWord_6676247, baseEnd_6676247] using wordTrace_append hprefix tailTrace_6676247
  have hstable : (prefixWord ++ tailWord_6676247).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6676247).length < 2 ^ (prefixWord ++ tailWord_6676247).sum := by decide
  have hdescent : baseEnd_6676247 < baseStart_6676247 := by decide
  rcases family_descends (prefixWord ++ tailWord_6676247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6676261 : List Nat := [1, 3, 1, 2, 3, 3, 1, 4, 1, 2, 2]
def baseStart_6676261 : Nat := 118140960795 + 6676261 * 2 ^ 59
def prefixEnd_6676261 : Nat := 4983230072969 + 3 ^ 40 * 6676261 * 2
def baseEnd_6676261 : Nat := 3428130867866808831833941

theorem tailTrace_6676261 : CollatzResearch.WordTrace tailWord_6676261 prefixEnd_6676261 3428130867866808831833941 := by
  unfold tailWord_6676261
  simp only [CollatzResearch.WordTrace]
  refine ⟨243503243266054086446788637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162335495510702724297859091 243503243266054086446788637)
  ·
    refine ⟨91313716224770282417545739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 243503243266054086446788637 91313716224770282417545739)
    ·
      refine ⟨136970574337155423626318609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91313716224770282417545739 136970574337155423626318609)
      ·
        refine ⟨102727930752866567719738957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 136970574337155423626318609 102727930752866567719738957)
        ·
          refine ⟨38522974032324962894902109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 102727930752866567719738957 38522974032324962894902109)
          ·
            refine ⟨14446115262121861085588291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38522974032324962894902109 14446115262121861085588291)
            ·
              refine ⟨21669172893182791628382437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14446115262121861085588291 21669172893182791628382437)
              ·
                refine ⟨4062969917471773430321707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21669172893182791628382437 4062969917471773430321707)
                ·
                  refine ⟨6094454876207660145482561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4062969917471773430321707 6094454876207660145482561)
                  ·
                    refine ⟨4570841157155745109111921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6094454876207660145482561 4570841157155745109111921)
                    ·
                      refine ⟨3428130867866808831833941, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4570841157155745109111921 3428130867866808831833941)
                      ·
                        rfl

theorem cell23_6676261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 3, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 3, 1, 4, 1, 2, 2].length) (baseStart_6676261 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6676261 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6676261 prefixEnd_6676261 := by exact prefixLift 6676261
  have htrace : WordTrace (prefixWord ++ tailWord_6676261) baseStart_6676261 baseEnd_6676261 := by
    simpa [prefixWord, tailWord_6676261, baseEnd_6676261] using wordTrace_append hprefix tailTrace_6676261
  have hstable : (prefixWord ++ tailWord_6676261).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6676261).length < 2 ^ (prefixWord ++ tailWord_6676261).sum := by decide
  have hdescent : baseEnd_6676261 < baseStart_6676261 := by decide
  rcases family_descends (prefixWord ++ tailWord_6676261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6676293 : List Nat := [1, 3, 1, 1, 1, 2, 3, 2, 1, 8]
def baseStart_6676293 : Nat := 118140960795 + 6676293 * 2 ^ 59
def prefixEnd_6676293 : Nat := 4983230072969 + 3 ^ 40 * 6676293 * 2
def baseEnd_6676293 : Nat := 1142715766415917568877931

theorem tailTrace_6676293 : CollatzResearch.WordTrace tailWord_6676293 prefixEnd_6676293 1142715766415917568877931 := by
  unfold tailWord_6676293
  simp only [CollatzResearch.WordTrace]
  refine ⟨243504410401938155911953533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162336273601292103941302355 243504410401938155911953533)
  ·
    refine ⟨91314153900726808466982575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 243504410401938155911953533 91314153900726808466982575)
    ·
      refine ⟨136971230851090212700473863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91314153900726808466982575 136971230851090212700473863)
      ·
        refine ⟨205456846276635319050710795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 136971230851090212700473863 205456846276635319050710795)
        ·
          refine ⟨308185269414952978576066193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 205456846276635319050710795 308185269414952978576066193)
          ·
            refine ⟨231138952061214733932049645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 308185269414952978576066193 231138952061214733932049645)
            ·
              refine ⟨86677107022955525224518617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 231138952061214733932049645 86677107022955525224518617)
              ·
                refine ⟨65007830267216643918388963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 86677107022955525224518617 65007830267216643918388963)
                ·
                  refine ⟨97511745400824965877583445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 65007830267216643918388963 97511745400824965877583445)
                  ·
                    refine ⟨1142715766415917568877931, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 97511745400824965877583445 1142715766415917568877931)
                    ·
                      rfl

theorem cell23_6676293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 3, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 3, 2, 1, 8].length) (baseStart_6676293 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6676293 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6676293 prefixEnd_6676293 := by exact prefixLift 6676293
  have htrace : WordTrace (prefixWord ++ tailWord_6676293) baseStart_6676293 baseEnd_6676293 := by
    simpa [prefixWord, tailWord_6676293, baseEnd_6676293] using wordTrace_append hprefix tailTrace_6676293
  have hstable : (prefixWord ++ tailWord_6676293).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6676293).length < 2 ^ (prefixWord ++ tailWord_6676293).sum := by decide
  have hdescent : baseEnd_6676293 < baseStart_6676293 := by decide
  rcases family_descends (prefixWord ++ tailWord_6676293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6676311 : List Nat := [1, 1, 3, 2, 5, 2, 1, 2, 2, 1, 3]
def baseStart_6676311 : Nat := 118140960795 + 6676311 * 2 ^ 59
def prefixEnd_6676311 : Nat := 4983230072969 + 3 ^ 40 * 6676311 * 2
def baseEnd_6676311 : Nat := 3428156541899533636208711

theorem tailTrace_6676311 : CollatzResearch.WordTrace tailWord_6676311 prefixEnd_6676311 3428156541899533636208711 := by
  unfold tailWord_6676311
  simp only [CollatzResearch.WordTrace]
  refine ⟨243505066915872944986108787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162336711277248629990739191 243505066915872944986108787)
  ·
    refine ⟨365257600373809417479163181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 243505066915872944986108787 365257600373809417479163181)
    ·
      refine ⟨136971600140178531554686193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 365257600373809417479163181 136971600140178531554686193)
      ·
        refine ⟨102728700105133898666014645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 136971600140178531554686193 102728700105133898666014645)
        ·
          refine ⟨9630815634856302999938873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 102728700105133898666014645 9630815634856302999938873)
          ·
            refine ⟨7223111726142227249954155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9630815634856302999938873 7223111726142227249954155)
            ·
              refine ⟨10834667589213340874931233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7223111726142227249954155 10834667589213340874931233)
              ·
                refine ⟨8126000691910005656198425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10834667589213340874931233 8126000691910005656198425)
                ·
                  refine ⟨6094500518932504242148819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8126000691910005656198425 6094500518932504242148819)
                  ·
                    refine ⟨9141750778398756363223229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6094500518932504242148819 9141750778398756363223229)
                    ·
                      refine ⟨3428156541899533636208711, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9141750778398756363223229 3428156541899533636208711)
                      ·
                        rfl

theorem cell23_6676311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 5, 2, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 5, 2, 1, 2, 2, 1, 3].length) (baseStart_6676311 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6676311 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6676311 prefixEnd_6676311 := by exact prefixLift 6676311
  have htrace : WordTrace (prefixWord ++ tailWord_6676311) baseStart_6676311 baseEnd_6676311 := by
    simpa [prefixWord, tailWord_6676311, baseEnd_6676311] using wordTrace_append hprefix tailTrace_6676311
  have hstable : (prefixWord ++ tailWord_6676311).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6676311).length < 2 ^ (prefixWord ++ tailWord_6676311).sum := by decide
  have hdescent : baseEnd_6676311 < baseStart_6676311 := by decide
  rcases family_descends (prefixWord ++ tailWord_6676311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6676385 : List Nat := [1, 2, 3, 4, 2, 2, 2, 1, 2, 2, 2]
def baseStart_6676385 : Nat := 118140960795 + 6676385 * 2 ^ 59
def prefixEnd_6676385 : Nat := 4983230072969 + 3 ^ 40 * 6676385 * 2
def baseEnd_6676385 : Nat := 3428194539467966346683371

theorem tailTrace_6676385 : CollatzResearch.WordTrace tailWord_6676385 prefixEnd_6676385 3428194539467966346683371 := by
  unfold tailWord_6676385
  simp only [CollatzResearch.WordTrace]
  refine ⟨243507765917604855624302609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162338510611736570416201739 243507765917604855624302609)
  ·
    refine ⟨182630824438203641718226957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 243507765917604855624302609 182630824438203641718226957)
    ·
      refine ⟨68486559164326365644335109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 182630824438203641718226957 68486559164326365644335109)
      ·
        refine ⟨12841229843311193558312833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 68486559164326365644335109 12841229843311193558312833)
        ·
          refine ⟨9630922382483395168734625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12841229843311193558312833 9630922382483395168734625)
          ·
            refine ⟨7223191786862546376550969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9630922382483395168734625 7223191786862546376550969)
            ·
              refine ⟨5417393840146909782413227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7223191786862546376550969 5417393840146909782413227)
              ·
                refine ⟨8126090760220364673619841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5417393840146909782413227 8126090760220364673619841)
                ·
                  refine ⟨6094568070165273505214881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8126090760220364673619841 6094568070165273505214881)
                  ·
                    refine ⟨4570926052623955128911161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6094568070165273505214881 4570926052623955128911161)
                    ·
                      refine ⟨3428194539467966346683371, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4570926052623955128911161 3428194539467966346683371)
                      ·
                        rfl

theorem cell23_6676385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 2, 2, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 2, 2, 2, 1, 2, 2, 2].length) (baseStart_6676385 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6676385 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6676385 prefixEnd_6676385 := by exact prefixLift 6676385
  have htrace : WordTrace (prefixWord ++ tailWord_6676385) baseStart_6676385 baseEnd_6676385 := by
    simpa [prefixWord, tailWord_6676385, baseEnd_6676385] using wordTrace_append hprefix tailTrace_6676385
  have hstable : (prefixWord ++ tailWord_6676385).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6676385).length < 2 ^ (prefixWord ++ tailWord_6676385).sum := by decide
  have hdescent : baseEnd_6676385 < baseStart_6676385 := by decide
  rcases family_descends (prefixWord ++ tailWord_6676385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6676407 : List Nat := [1, 1, 3, 1, 3, 1, 1, 2, 4, 4, 2]
def baseStart_6676407 : Nat := 118140960795 + 6676407 * 2 ^ 59
def prefixEnd_6676407 : Nat := 4983230072969 + 3 ^ 40 * 6676407 * 2
def baseEnd_6676407 : Nat := 3428205836042365260608269

theorem tailTrace_6676407 : CollatzResearch.WordTrace tailWord_6676407 prefixEnd_6676407 3428205836042365260608269 := by
  unfold tailWord_6676407
  simp only [CollatzResearch.WordTrace]
  refine ⟨243508568323525153381603475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162339045549016768921068983 243508568323525153381603475)
  ·
    refine ⟨365262852485287730072405213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 243508568323525153381603475 365262852485287730072405213)
    ·
      refine ⟨136973569681982898777151955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 365262852485287730072405213 136973569681982898777151955)
      ·
        refine ⟨205460354522974348165727933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 136973569681982898777151955 205460354522974348165727933)
        ·
          refine ⟨77047632946115380562147975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 205460354522974348165727933 77047632946115380562147975)
          ·
            refine ⟨115571449419173070843221963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77047632946115380562147975 115571449419173070843221963)
            ·
              refine ⟨173357174128759606264832945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 115571449419173070843221963 173357174128759606264832945)
              ·
                refine ⟨130017880596569704698624709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 173357174128759606264832945 130017880596569704698624709)
                ·
                  refine ⟨24378352611856819630992133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 130017880596569704698624709 24378352611856819630992133)
                  ·
                    refine ⟨4570941114723153680811025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24378352611856819630992133 4570941114723153680811025)
                    ·
                      refine ⟨3428205836042365260608269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4570941114723153680811025 3428205836042365260608269)
                      ·
                        rfl

theorem cell23_6676407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 1, 2, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 1, 2, 4, 4, 2].length) (baseStart_6676407 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6676407 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6676407 prefixEnd_6676407 := by exact prefixLift 6676407
  have htrace : WordTrace (prefixWord ++ tailWord_6676407) baseStart_6676407 baseEnd_6676407 := by
    simpa [prefixWord, tailWord_6676407, baseEnd_6676407] using wordTrace_append hprefix tailTrace_6676407
  have hstable : (prefixWord ++ tailWord_6676407).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6676407).length < 2 ^ (prefixWord ++ tailWord_6676407).sum := by decide
  have hdescent : baseEnd_6676407 < baseStart_6676407 := by decide
  rcases family_descends (prefixWord ++ tailWord_6676407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6676427 : List Nat := [1, 1, 1, 1, 3, 4, 1, 4, 2, 2, 3]
def baseStart_6676427 : Nat := 118140960795 + 6676427 * 2 ^ 59
def prefixEnd_6676427 : Nat := 4983230072969 + 3 ^ 40 * 6676427 * 2
def baseEnd_6676427 : Nat := 3428216105655455182358177

theorem tailTrace_6676427 : CollatzResearch.WordTrace tailWord_6676427 prefixEnd_6676427 3428216105655455182358177 := by
  unfold tailWord_6676427
  simp only [CollatzResearch.WordTrace]
  refine ⟨243509297783452696797331535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162339531855635131198221023 243509297783452696797331535)
  ·
    refine ⟨365263946675179045195997303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 243509297783452696797331535 365263946675179045195997303)
    ·
      refine ⟨547895920012768567793995955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 365263946675179045195997303 547895920012768567793995955)
      ·
        refine ⟨821843880019152851690993933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 547895920012768567793995955 821843880019152851690993933)
        ·
          refine ⟨308191455007182319384122725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 821843880019152851690993933 308191455007182319384122725)
          ·
            refine ⟨57785897813846684884523011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 308191455007182319384122725 57785897813846684884523011)
            ·
              refine ⟨86678846720770027326784517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57785897813846684884523011 86678846720770027326784517)
              ·
                refine ⟨16252283760144380123772097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 86678846720770027326784517 16252283760144380123772097)
                ·
                  refine ⟨12189212820108285092829073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16252283760144380123772097 12189212820108285092829073)
                  ·
                    refine ⟨9141909615081213819621805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12189212820108285092829073 9141909615081213819621805)
                    ·
                      refine ⟨3428216105655455182358177, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9141909615081213819621805 3428216105655455182358177)
                      ·
                        rfl

theorem cell23_6676427_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 1, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 1, 4, 2, 2, 3].length) (baseStart_6676427 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6676427 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6676427 prefixEnd_6676427 := by exact prefixLift 6676427
  have htrace : WordTrace (prefixWord ++ tailWord_6676427) baseStart_6676427 baseEnd_6676427 := by
    simpa [prefixWord, tailWord_6676427, baseEnd_6676427] using wordTrace_append hprefix tailTrace_6676427
  have hstable : (prefixWord ++ tailWord_6676427).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6676427).length < 2 ^ (prefixWord ++ tailWord_6676427).sum := by decide
  have hdescent : baseEnd_6676427 < baseStart_6676427 := by decide
  rcases family_descends (prefixWord ++ tailWord_6676427) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6676447 : List Nat := [1, 1, 2, 3, 4, 1, 2, 3, 6]
def baseStart_6676447 : Nat := 118140960795 + 6676447 * 2 ^ 59
def prefixEnd_6676447 : Nat := 4983230072969 + 3 ^ 40 * 6676447 * 2
def baseEnd_6676447 : Nat := 380914041696505011567565

theorem tailTrace_6676447 : CollatzResearch.WordTrace tailWord_6676447 prefixEnd_6676447 380914041696505011567565 := by
  unfold tailWord_6676447
  simp only [CollatzResearch.WordTrace]
  refine ⟨243510027243380240213059595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162340018162253493475373063 243510027243380240213059595)
  ·
    refine ⟨365265040865070360319589393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 243510027243380240213059595 365265040865070360319589393)
    ·
      refine ⟨273948780648802770239692045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 365265040865070360319589393 273948780648802770239692045)
      ·
        refine ⟨102730792743301038839884517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 273948780648802770239692045 102730792743301038839884517)
        ·
          refine ⟨19262023639368944782478347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 102730792743301038839884517 19262023639368944782478347)
          ·
            refine ⟨28893035459053417173717521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19262023639368944782478347 28893035459053417173717521)
            ·
              refine ⟨21669776594290062880288141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28893035459053417173717521 21669776594290062880288141)
              ·
                refine ⟨8126166222858773580108053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21669776594290062880288141 8126166222858773580108053)
                ·
                  refine ⟨380914041696505011567565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8126166222858773580108053 380914041696505011567565)
                  ·
                    rfl

theorem cell23_6676447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 2, 3, 6].length) (baseStart_6676447 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6676447 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6676447 prefixEnd_6676447 := by exact prefixLift 6676447
  have htrace : WordTrace (prefixWord ++ tailWord_6676447) baseStart_6676447 baseEnd_6676447 := by
    simpa [prefixWord, tailWord_6676447, baseEnd_6676447] using wordTrace_append hprefix tailTrace_6676447
  have hstable : (prefixWord ++ tailWord_6676447).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6676447).length < 2 ^ (prefixWord ++ tailWord_6676447).sum := by decide
  have hdescent : baseEnd_6676447 < baseStart_6676447 := by decide
  rcases family_descends (prefixWord ++ tailWord_6676447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6676461 : List Nat := [1, 5, 1, 4, 1, 1, 1, 1, 1, 4, 3]
def baseStart_6676461 : Nat := 118140960795 + 6676461 * 2 ^ 59
def prefixEnd_6676461 : Nat := 4983230072969 + 3 ^ 40 * 6676461 * 2
def baseEnd_6676461 : Nat := 3428233563997708049333021

theorem tailTrace_6676461 : CollatzResearch.WordTrace tailWord_6676461 prefixEnd_6676461 3428233563997708049333021 := by
  unfold tailWord_6676461
  simp only [CollatzResearch.WordTrace]
  refine ⟨243510537865329520604069237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162340358576886347069379491 243510537865329520604069237)
  ·
    refine ⟨22829112924874642556631491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 243510537865329520604069237 22829112924874642556631491)
    ·
      refine ⟨34243669387311963834947237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22829112924874642556631491 34243669387311963834947237)
      ·
        refine ⟨6420688010120993219052607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 34243669387311963834947237 6420688010120993219052607)
        ·
          refine ⟨9631032015181489828578911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6420688010120993219052607 9631032015181489828578911)
          ·
            refine ⟨14446548022772234742868367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9631032015181489828578911 14446548022772234742868367)
            ·
              refine ⟨21669822034158352114302551, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14446548022772234742868367 21669822034158352114302551)
              ·
                refine ⟨32504733051237528171453827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21669822034158352114302551 32504733051237528171453827)
                ·
                  refine ⟨48757099576856292257180741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32504733051237528171453827 48757099576856292257180741)
                  ·
                    refine ⟨9141956170660554798221389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 48757099576856292257180741 9141956170660554798221389)
                    ·
                      refine ⟨3428233563997708049333021, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9141956170660554798221389 3428233563997708049333021)
                      ·
                        rfl

theorem cell23_6676461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 1, 1, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 1, 1, 1, 1, 1, 4, 3].length) (baseStart_6676461 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6676461 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6676461 prefixEnd_6676461 := by exact prefixLift 6676461
  have htrace : WordTrace (prefixWord ++ tailWord_6676461) baseStart_6676461 baseEnd_6676461 := by
    simpa [prefixWord, tailWord_6676461, baseEnd_6676461] using wordTrace_append hprefix tailTrace_6676461
  have hstable : (prefixWord ++ tailWord_6676461).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6676461).length < 2 ^ (prefixWord ++ tailWord_6676461).sum := by decide
  have hdescent : baseEnd_6676461 < baseStart_6676461 := by decide
  rcases family_descends (prefixWord ++ tailWord_6676461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6676491 : List Nat := [1, 1, 1, 1, 6, 1, 1, 6, 1, 1, 3]
def baseStart_6676491 : Nat := 118140960795 + 6676491 * 2 ^ 59
def prefixEnd_6676491 : Nat := 4983230072969 + 3 ^ 40 * 6676491 * 2
def baseEnd_6676491 : Nat := 3428248968417342931957883

theorem tailTrace_6676491 : CollatzResearch.WordTrace tailWord_6676491 prefixEnd_6676491 3428248968417342931957883 := by
  unfold tailWord_6676491
  simp only [CollatzResearch.WordTrace]
  refine ⟨243511632055220835727661327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162341088036813890485107551 243511632055220835727661327)
  ·
    refine ⟨365267448082831253591491991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 243511632055220835727661327 365267448082831253591491991)
    ·
      refine ⟨547901172124246880387237987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 365267448082831253591491991 547901172124246880387237987)
      ·
        refine ⟨821851758186370320580856981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 547901172124246880387237987 821851758186370320580856981)
        ·
          refine ⟨38524301164986108777227671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 821851758186370320580856981 38524301164986108777227671)
          ·
            refine ⟨57786451747479163165841507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38524301164986108777227671 57786451747479163165841507)
            ·
              refine ⟨86679677621218744748762261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57786451747479163165841507 86679677621218744748762261)
              ·
                refine ⟨4063109888494628660098231, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 86679677621218744748762261 4063109888494628660098231)
                ·
                  refine ⟨6094664832741942990147347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4063109888494628660098231 6094664832741942990147347)
                  ·
                    refine ⟨9141997249112914485221021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6094664832741942990147347 9141997249112914485221021)
                    ·
                      refine ⟨3428248968417342931957883, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9141997249112914485221021 3428248968417342931957883)
                      ·
                        rfl

theorem cell23_6676491_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 1, 6, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 1, 6, 1, 1, 3].length) (baseStart_6676491 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6676491 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6676491 prefixEnd_6676491 := by exact prefixLift 6676491
  have htrace : WordTrace (prefixWord ++ tailWord_6676491) baseStart_6676491 baseEnd_6676491 := by
    simpa [prefixWord, tailWord_6676491, baseEnd_6676491] using wordTrace_append hprefix tailTrace_6676491
  have hstable : (prefixWord ++ tailWord_6676491).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6676491).length < 2 ^ (prefixWord ++ tailWord_6676491).sum := by decide
  have hdescent : baseEnd_6676491 < baseStart_6676491 := by decide
  rcases family_descends (prefixWord ++ tailWord_6676491) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6676514 : List Nat := [3, 3, 1, 1, 1, 2, 1, 1, 2, 6, 2]
def baseStart_6676514 : Nat := 118140960795 + 6676514 * 2 ^ 59
def prefixEnd_6676514 : Nat := 4983230072969 + 3 ^ 40 * 6676514 * 2
def baseEnd_6676514 : Nat := 3428260778472396341970277

theorem tailTrace_6676514 : CollatzResearch.WordTrace tailWord_6676514 prefixEnd_6676514 3428260778472396341970277 := by
  unfold tailWord_6676514
  simp only [CollatzResearch.WordTrace]
  refine ⟨60878117733534377663937149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 162341647289425007103832397 60878117733534377663937149)
  ·
    refine ⟨22829294150075391623976431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 60878117733534377663937149 22829294150075391623976431)
    ·
      refine ⟨34243941225113087435964647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22829294150075391623976431 34243941225113087435964647)
      ·
        refine ⟨51365911837669631153946971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34243941225113087435964647 51365911837669631153946971)
        ·
          refine ⟨77048867756504446730920457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51365911837669631153946971 77048867756504446730920457)
          ·
            refine ⟨57786650817378335048190343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 77048867756504446730920457 57786650817378335048190343)
            ·
              refine ⟨86679976226067502572285515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57786650817378335048190343 86679976226067502572285515)
              ·
                refine ⟨130019964339101253858428273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 86679976226067502572285515 130019964339101253858428273)
                ·
                  refine ⟨97514973254325940393821205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 130019964339101253858428273 97514973254325940393821205)
                  ·
                    refine ⟨4571014371296528455960369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 97514973254325940393821205 4571014371296528455960369)
                    ·
                      refine ⟨3428260778472396341970277, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4571014371296528455960369 3428260778472396341970277)
                      ·
                        rfl

theorem cell23_6676514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 1, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 1, 1, 2, 6, 2].length) (baseStart_6676514 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6676514 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6676514 prefixEnd_6676514 := by exact prefixLift 6676514
  have htrace : WordTrace (prefixWord ++ tailWord_6676514) baseStart_6676514 baseEnd_6676514 := by
    simpa [prefixWord, tailWord_6676514, baseEnd_6676514] using wordTrace_append hprefix tailTrace_6676514
  have hstable : (prefixWord ++ tailWord_6676514).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6676514).length < 2 ^ (prefixWord ++ tailWord_6676514).sum := by decide
  have hdescent : baseEnd_6676514 < baseStart_6676514 := by decide
  rcases family_descends (prefixWord ++ tailWord_6676514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6676542 : List Nat := [4, 2, 1, 3, 2, 1, 3, 2, 1, 1, 3]
def baseStart_6676542 : Nat := 118140960795 + 6676542 * 2 ^ 59
def prefixEnd_6676542 : Nat := 4983230072969 + 3 ^ 40 * 6676542 * 2
def baseEnd_6676542 : Nat := 3428275155930722232420149

theorem tailTrace_6676542 : CollatzResearch.WordTrace tailWord_6676542 prefixEnd_6676542 3428275155930722232420149 := by
  unfold tailWord_6676542
  simp only [CollatzResearch.WordTrace]
  refine ⟨30439186522254508929720985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 162342328118690714291845253 30439186522254508929720985)
  ·
    refine ⟨22829389891690881697290739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30439186522254508929720985 22829389891690881697290739)
    ·
      refine ⟨34244084837536322545936109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22829389891690881697290739 34244084837536322545936109)
      ·
        refine ⟨12841531814076120954726041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34244084837536322545936109 12841531814076120954726041)
        ·
          refine ⟨9631148860557090716044531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12841531814076120954726041 9631148860557090716044531)
          ·
            refine ⟨14446723290835636074066797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9631148860557090716044531 14446723290835636074066797)
            ·
              refine ⟨5417521234063363527775049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14446723290835636074066797 5417521234063363527775049)
              ·
                refine ⟨4063140925547522645831287, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5417521234063363527775049 4063140925547522645831287)
                ·
                  refine ⟨6094711388321283968746931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4063140925547522645831287 6094711388321283968746931)
                  ·
                    refine ⟨9142067082481925953120397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6094711388321283968746931 9142067082481925953120397)
                    ·
                      refine ⟨3428275155930722232420149, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9142067082481925953120397 3428275155930722232420149)
                      ·
                        rfl

theorem cell23_6676542_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 2, 1, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 2, 1, 3, 2, 1, 1, 3].length) (baseStart_6676542 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6676542 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6676542 prefixEnd_6676542 := by exact prefixLift 6676542
  have htrace : WordTrace (prefixWord ++ tailWord_6676542) baseStart_6676542 baseEnd_6676542 := by
    simpa [prefixWord, tailWord_6676542, baseEnd_6676542] using wordTrace_append hprefix tailTrace_6676542
  have hstable : (prefixWord ++ tailWord_6676542).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6676542).length < 2 ^ (prefixWord ++ tailWord_6676542).sum := by decide
  have hdescent : baseEnd_6676542 < baseStart_6676542 := by decide
  rcases family_descends (prefixWord ++ tailWord_6676542) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6676547 : List Nat := [1, 1, 1, 3, 1, 2, 2, 1, 5, 3, 3]
def baseStart_6676547 : Nat := 118140960795 + 6676547 * 2 ^ 59
def prefixEnd_6676547 : Nat := 4983230072969 + 3 ^ 40 * 6676547 * 2
def baseEnd_6676547 : Nat := 3428277723333994712857625

theorem tailTrace_6676547 : CollatzResearch.WordTrace tailWord_6676547 prefixEnd_6676547 3428277723333994712857625 := by
  unfold tailWord_6676547
  simp only [CollatzResearch.WordTrace]
  refine ⟨243513674543017957291699895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162342449695345304861133263 243513674543017957291699895)
  ·
    refine ⟨365270511814526935937549843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 243513674543017957291699895 365270511814526935937549843)
    ·
      refine ⟨547905767721790403906324765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 365270511814526935937549843 547905767721790403906324765)
      ·
        refine ⟨205464662895671401464871787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 547905767721790403906324765 205464662895671401464871787)
        ·
          refine ⟨308196994343507102197307681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 205464662895671401464871787 308196994343507102197307681)
          ·
            refine ⟨231147745757630326647980761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 308196994343507102197307681 231147745757630326647980761)
            ·
              refine ⟨173360809318222744985985571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 231147745757630326647980761 173360809318222744985985571)
              ·
                refine ⟨260041213977334117478978357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 173360809318222744985985571 260041213977334117478978357)
                ·
                  refine ⟨24378863810375073513654221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 260041213977334117478978357 24378863810375073513654221)
                  ·
                    refine ⟨9142073928890652567620333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24378863810375073513654221 9142073928890652567620333)
                    ·
                      refine ⟨3428277723333994712857625, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9142073928890652567620333 3428277723333994712857625)
                      ·
                        rfl

theorem cell23_6676547_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 2, 1, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 2, 1, 5, 3, 3].length) (baseStart_6676547 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6676547 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6676547 prefixEnd_6676547 := by exact prefixLift 6676547
  have htrace : WordTrace (prefixWord ++ tailWord_6676547) baseStart_6676547 baseEnd_6676547 := by
    simpa [prefixWord, tailWord_6676547, baseEnd_6676547] using wordTrace_append hprefix tailTrace_6676547
  have hstable : (prefixWord ++ tailWord_6676547).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6676547).length < 2 ^ (prefixWord ++ tailWord_6676547).sum := by decide
  have hdescent : baseEnd_6676547 < baseStart_6676547 := by decide
  rcases family_descends (prefixWord ++ tailWord_6676547) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6676558 : List Nat := [4, 1, 1, 1, 1, 6, 2, 1, 2, 4]
def baseStart_6676558 : Nat := 118140960795 + 6676558 * 2 ^ 59
def prefixEnd_6676558 : Nat := 4983230072969 + 3 ^ 40 * 6676558 * 2
def baseEnd_6676558 : Nat := 1142761123873731389940025

theorem tailTrace_6676558 : CollatzResearch.WordTrace tailWord_6676558 prefixEnd_6676558 1142761123873731389940025 := by
  unfold tailWord_6676558
  simp only [CollatzResearch.WordTrace]
  refine ⟨30439259468247263271293791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 162342717163985404113566885 30439259468247263271293791)
  ·
    refine ⟨45658889202370894906940687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30439259468247263271293791 45658889202370894906940687)
    ·
      refine ⟨68488333803556342360411031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45658889202370894906940687 68488333803556342360411031)
      ·
        refine ⟨102732500705334513540616547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68488333803556342360411031 102732500705334513540616547)
        ·
          refine ⟨154098751058001770310924821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 102732500705334513540616547 154098751058001770310924821)
          ·
            refine ⟨7223378955843832983324601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 154098751058001770310924821 7223378955843832983324601)
            ·
              refine ⟨5417534216882874737493451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7223378955843832983324601 5417534216882874737493451)
              ·
                refine ⟨8126301325324312106240177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5417534216882874737493451 8126301325324312106240177)
                ·
                  refine ⟨6094725993993234079680133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8126301325324312106240177 6094725993993234079680133)
                  ·
                    refine ⟨1142761123873731389940025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6094725993993234079680133 1142761123873731389940025)
                    ·
                      rfl

theorem cell23_6676558_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 6, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 6, 2, 1, 2, 4].length) (baseStart_6676558 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6676558 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6676558 prefixEnd_6676558 := by exact prefixLift 6676558
  have htrace : WordTrace (prefixWord ++ tailWord_6676558) baseStart_6676558 baseEnd_6676558 := by
    simpa [prefixWord, tailWord_6676558, baseEnd_6676558] using wordTrace_append hprefix tailTrace_6676558
  have hstable : (prefixWord ++ tailWord_6676558).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6676558).length < 2 ^ (prefixWord ++ tailWord_6676558).sum := by decide
  have hdescent : baseEnd_6676558 < baseStart_6676558 := by decide
  rcases family_descends (prefixWord ++ tailWord_6676558) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6676564 : List Nat := [2, 4, 1, 1, 1, 1, 1, 5, 1, 3, 3]
def baseStart_6676564 : Nat := 118140960795 + 6676564 * 2 ^ 59
def prefixEnd_6676564 : Nat := 4983230072969 + 3 ^ 40 * 6676564 * 2
def baseEnd_6676564 : Nat := 3428286452505121146345047

theorem tailTrace_6676564 : CollatzResearch.WordTrace tailWord_6676564 prefixEnd_6676564 3428286452505121146345047 := by
  unfold tailWord_6676564
  simp only [CollatzResearch.WordTrace]
  refine ⟨121757147291978184597534373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 162342863055970912796712497 121757147291978184597534373)
  ·
    refine ⟨22829465117245909612037695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 121757147291978184597534373 22829465117245909612037695)
    ·
      refine ⟨34244197675868864418056543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22829465117245909612037695 34244197675868864418056543)
      ·
        refine ⟨51366296513803296627084815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34244197675868864418056543 51366296513803296627084815)
        ·
          refine ⟨77049444770704944940627223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51366296513803296627084815 77049444770704944940627223)
          ·
            refine ⟨115574167156057417410940835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77049444770704944940627223 115574167156057417410940835)
            ·
              refine ⟨173361250734086126116411253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 115574167156057417410940835 173361250734086126116411253)
              ·
                refine ⟨16252617256320574323413555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 173361250734086126116411253 16252617256320574323413555)
                ·
                  refine ⟨24378925884480861485120333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16252617256320574323413555 24378925884480861485120333)
                  ·
                    refine ⟨9142097206680323056920125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24378925884480861485120333 9142097206680323056920125)
                    ·
                      refine ⟨3428286452505121146345047, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9142097206680323056920125 3428286452505121146345047)
                      ·
                        rfl

theorem cell23_6676564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 1, 5, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 1, 5, 1, 3, 3].length) (baseStart_6676564 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6676564 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6676564 prefixEnd_6676564 := by exact prefixLift 6676564
  have htrace : WordTrace (prefixWord ++ tailWord_6676564) baseStart_6676564 baseEnd_6676564 := by
    simpa [prefixWord, tailWord_6676564, baseEnd_6676564] using wordTrace_append hprefix tailTrace_6676564
  have hstable : (prefixWord ++ tailWord_6676564).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6676564).length < 2 ^ (prefixWord ++ tailWord_6676564).sum := by decide
  have hdescent : baseEnd_6676564 < baseStart_6676564 := by decide
  rcases family_descends (prefixWord ++ tailWord_6676564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6676598 : List Nat := [5, 1, 1, 2, 1, 2, 1, 4, 2, 1, 3]
def baseStart_6676598 : Nat := 118140960795 + 6676598 * 2 ^ 59
def prefixEnd_6676598 : Nat := 4983230072969 + 3 ^ 40 * 6676598 * 2
def baseEnd_6676598 : Nat := 3428303910847374013319891

theorem tailTrace_6676598 : CollatzResearch.WordTrace tailWord_6676598 prefixEnd_6676598 3428303910847374013319891 := by
  unfold tailWord_6676598
  simp only [CollatzResearch.WordTrace]
  refine ⟨15219720916614574562612903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 162343689777222128667870965 15219720916614574562612903)
  ·
    refine ⟨22829581374921861843919355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15219720916614574562612903 22829581374921861843919355)
    ·
      refine ⟨34244372062382792765879033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22829581374921861843919355 34244372062382792765879033)
      ·
        refine ⟨25683279046787094574409275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34244372062382792765879033 25683279046787094574409275)
        ·
          refine ⟨38524918570180641861613913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25683279046787094574409275 38524918570180641861613913)
          ·
            refine ⟨28893688927635481396210435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38524918570180641861613913 28893688927635481396210435)
            ·
              refine ⟨43340533391453222094315653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28893688927635481396210435 43340533391453222094315653)
              ·
                refine ⟨8126350010897479142684185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 43340533391453222094315653 8126350010897479142684185)
                ·
                  refine ⟨6094762508173109357013139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8126350010897479142684185 6094762508173109357013139)
                  ·
                    refine ⟨9142143762259664035519709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6094762508173109357013139 9142143762259664035519709)
                    ·
                      refine ⟨3428303910847374013319891, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9142143762259664035519709 3428303910847374013319891)
                      ·
                        rfl

theorem cell23_6676598_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 1, 4, 2, 1, 3].length) (baseStart_6676598 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6676598 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6676598 prefixEnd_6676598 := by exact prefixLift 6676598
  have htrace : WordTrace (prefixWord ++ tailWord_6676598) baseStart_6676598 baseEnd_6676598 := by
    simpa [prefixWord, tailWord_6676598, baseEnd_6676598] using wordTrace_append hprefix tailTrace_6676598
  have hstable : (prefixWord ++ tailWord_6676598).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6676598).length < 2 ^ (prefixWord ++ tailWord_6676598).sum := by decide
  have hdescent : baseEnd_6676598 < baseStart_6676598 := by decide
  rcases family_descends (prefixWord ++ tailWord_6676598) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6676642 : List Nat := [3, 3, 1, 3, 1, 3, 2, 1, 1, 3, 2]
def baseStart_6676642 : Nat := 118140960795 + 6676642 * 2 ^ 59
def prefixEnd_6676642 : Nat := 4983230072969 + 3 ^ 40 * 6676642 * 2
def baseEnd_6676642 : Nat := 3428326503996171841169689

theorem tailTrace_6676642 : CollatzResearch.WordTrace tailWord_6676642 prefixEnd_6676642 3428326503996171841169689 := by
  unfold tailWord_6676642
  simp only [CollatzResearch.WordTrace]
  refine ⟨60879284869418447129102045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 162344759651782525677605453 60879284869418447129102045)
  ·
    refine ⟨22829731826031917673413267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 60879284869418447129102045 22829731826031917673413267)
    ·
      refine ⟨34244597739047876510119901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22829731826031917673413267 34244597739047876510119901)
      ·
        refine ⟨12841724152142953691294963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34244597739047876510119901 12841724152142953691294963)
        ·
          refine ⟨19262586228214430536942445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12841724152142953691294963 19262586228214430536942445)
          ·
            refine ⟨7223469835580411451353417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19262586228214430536942445 7223469835580411451353417)
            ·
              refine ⟨5417602376685308588515063, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7223469835580411451353417 5417602376685308588515063)
              ·
                refine ⟨8126403565027962882772595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5417602376685308588515063 8126403565027962882772595)
                ·
                  refine ⟨12189605347541944324158893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8126403565027962882772595 12189605347541944324158893)
                  ·
                    refine ⟨4571102005328229121559585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12189605347541944324158893 4571102005328229121559585)
                    ·
                      refine ⟨3428326503996171841169689, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4571102005328229121559585 3428326503996171841169689)
                      ·
                        rfl

theorem cell23_6676642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 3, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 3, 2, 1, 1, 3, 2].length) (baseStart_6676642 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6676642 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6676642 prefixEnd_6676642 := by exact prefixLift 6676642
  have htrace : WordTrace (prefixWord ++ tailWord_6676642) baseStart_6676642 baseEnd_6676642 := by
    simpa [prefixWord, tailWord_6676642, baseEnd_6676642] using wordTrace_append hprefix tailTrace_6676642
  have hstable : (prefixWord ++ tailWord_6676642).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6676642).length < 2 ^ (prefixWord ++ tailWord_6676642).sum := by decide
  have hdescent : baseEnd_6676642 < baseStart_6676642 := by decide
  rcases family_descends (prefixWord ++ tailWord_6676642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6676667 : List Nat := [1, 1, 1, 1, 1, 2, 6, 1, 1, 1, 7]
def baseStart_6676667 : Nat := 118140960795 + 6676667 * 2 ^ 59
def prefixEnd_6676667 : Nat := 4983230072969 + 3 ^ 40 * 6676667 * 2
def baseEnd_6676667 : Nat := 3428339341012534243357073

theorem tailTrace_6676667 : CollatzResearch.WordTrace tailWord_6676667 prefixEnd_6676667 3428339341012534243357073 := by
  unfold tailWord_6676667
  simp only [CollatzResearch.WordTrace]
  refine ⟨243518051302583217786068255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162345367535055478524045503 243518051302583217786068255)
  ·
    refine ⟨365277076953874826679102383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 243518051302583217786068255 365277076953874826679102383)
    ·
      refine ⟨547915615430812240018653575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 365277076953874826679102383 547915615430812240018653575)
      ·
        refine ⟨821873423146218360027980363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 547915615430812240018653575 821873423146218360027980363)
        ·
          refine ⟨1232810134719327540041970545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 821873423146218360027980363 1232810134719327540041970545)
          ·
            refine ⟨924607601039495655031477909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1232810134719327540041970545 924607601039495655031477909)
            ·
              refine ⟨43340981298726358829600527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 924607601039495655031477909 43340981298726358829600527)
              ·
                refine ⟨65011471948089538244400791, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43340981298726358829600527 65011471948089538244400791)
                ·
                  refine ⟨97517207922134307366601187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 65011471948089538244400791 97517207922134307366601187)
                  ·
                    refine ⟨146275811883201461049901781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 97517207922134307366601187 146275811883201461049901781)
                    ·
                      refine ⟨3428339341012534243357073, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 146275811883201461049901781 3428339341012534243357073)
                      ·
                        rfl

theorem cell23_6676667_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 6, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 6, 1, 1, 1, 7].length) (baseStart_6676667 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6676667 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6676667 prefixEnd_6676667 := by exact prefixLift 6676667
  have htrace : WordTrace (prefixWord ++ tailWord_6676667) baseStart_6676667 baseEnd_6676667 := by
    simpa [prefixWord, tailWord_6676667, baseEnd_6676667] using wordTrace_append hprefix tailTrace_6676667
  have hstable : (prefixWord ++ tailWord_6676667).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6676667).length < 2 ^ (prefixWord ++ tailWord_6676667).sum := by decide
  have hdescent : baseEnd_6676667 < baseStart_6676667 := by decide
  rcases family_descends (prefixWord ++ tailWord_6676667) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6676687 : List Nat := [1, 1, 2, 1, 1, 3, 3, 1, 2, 8]
def baseStart_6676687 : Nat := 118140960795 + 6676687 * 2 ^ 59
def prefixEnd_6676687 : Nat := 4983230072969 + 3 ^ 40 * 6676687 * 2
def baseEnd_6676687 : Nat := 1142783203541874721702327

theorem tailTrace_6676687 : CollatzResearch.WordTrace tailWord_6676687 prefixEnd_6676687 1142783203541874721702327 := by
  unfold tailWord_6676687
  simp only [CollatzResearch.WordTrace]
  refine ⟨243518780762510761201796315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162345853841673840801197543 243518780762510761201796315)
  ·
    refine ⟨365278171143766141802694473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 243518780762510761201796315 365278171143766141802694473)
    ·
      refine ⟨273958628357824606352020855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 365278171143766141802694473 273958628357824606352020855)
      ·
        refine ⟨410937942536736909528031283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 273958628357824606352020855 410937942536736909528031283)
        ·
          refine ⟨616406913805105364292046925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 410937942536736909528031283 616406913805105364292046925)
          ·
            refine ⟨231152592676914511609517597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 616406913805105364292046925 231152592676914511609517597)
            ·
              refine ⟨86682222253842941853569099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 231152592676914511609517597 86682222253842941853569099)
              ·
                refine ⟨130023333380764412780353649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 86682222253842941853569099 130023333380764412780353649)
                ·
                  refine ⟨97517500035573309585265237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 130023333380764412780353649 97517500035573309585265237)
                  ·
                    refine ⟨1142783203541874721702327, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 97517500035573309585265237 1142783203541874721702327)
                    ·
                      rfl

theorem cell23_6676687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 3, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 3, 1, 2, 8].length) (baseStart_6676687 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6676687 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6676687 prefixEnd_6676687 := by exact prefixLift 6676687
  have htrace : WordTrace (prefixWord ++ tailWord_6676687) baseStart_6676687 baseEnd_6676687 := by
    simpa [prefixWord, tailWord_6676687, baseEnd_6676687] using wordTrace_append hprefix tailTrace_6676687
  have hstable : (prefixWord ++ tailWord_6676687).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6676687).length < 2 ^ (prefixWord ++ tailWord_6676687).sum := by decide
  have hdescent : baseEnd_6676687 < baseStart_6676687 := by decide
  rcases family_descends (prefixWord ++ tailWord_6676687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6676711 : List Nat := [1, 1, 5, 3, 1, 1, 1, 1, 4, 1, 4]
def baseStart_6676711 : Nat := 118140960795 + 6676711 * 2 ^ 59
def prefixEnd_6676711 : Nat := 4983230072969 + 3 ^ 40 * 6676711 * 2
def baseEnd_6676711 : Nat := 3428361934161332071206871

theorem tailTrace_6676711 : CollatzResearch.WordTrace tailWord_6676711 prefixEnd_6676711 3428361934161332071206871 := by
  unfold tailWord_6676711
  simp only [CollatzResearch.WordTrace]
  refine ⟨243519656114423813300669987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162346437409615875533779991 243519656114423813300669987)
  ·
    refine ⟨365279484171635719951004981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 243519656114423813300669987 365279484171635719951004981)
    ·
      refine ⟨34244951641090848745406717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 365279484171635719951004981 34244951641090848745406717)
      ·
        refine ⟨12841856865409068279527519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34244951641090848745406717 12841856865409068279527519)
        ·
          refine ⟨19262785298113602419291279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12841856865409068279527519 19262785298113602419291279)
          ·
            refine ⟨28894177947170403628936919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19262785298113602419291279 28894177947170403628936919)
            ·
              refine ⟨43341266920755605443405379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28894177947170403628936919 43341266920755605443405379)
              ·
                refine ⟨65011900381133408165108069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43341266920755605443405379 65011900381133408165108069)
                ·
                  refine ⟨12189731321462514030957763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 65011900381133408165108069 12189731321462514030957763)
                  ·
                    refine ⟨18284596982193771046436645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12189731321462514030957763 18284596982193771046436645)
                    ·
                      refine ⟨3428361934161332071206871, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18284596982193771046436645 3428361934161332071206871)
                      ·
                        rfl

theorem cell23_6676711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 1, 1, 4, 1, 4].length) (baseStart_6676711 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6676711 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6676711 prefixEnd_6676711 := by exact prefixLift 6676711
  have htrace : WordTrace (prefixWord ++ tailWord_6676711) baseStart_6676711 baseEnd_6676711 := by
    simpa [prefixWord, tailWord_6676711, baseEnd_6676711] using wordTrace_append hprefix tailTrace_6676711
  have hstable : (prefixWord ++ tailWord_6676711).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6676711).length < 2 ^ (prefixWord ++ tailWord_6676711).sum := by decide
  have hdescent : baseEnd_6676711 < baseStart_6676711 := by decide
  rcases family_descends (prefixWord ++ tailWord_6676711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6676721 : List Nat := [1, 2, 2, 2, 2, 1, 5, 1, 3, 4]
def baseStart_6676721 : Nat := 118140960795 + 6676721 * 2 ^ 59
def prefixEnd_6676721 : Nat := 4983230072969 + 3 ^ 40 * 6676721 * 2
def baseEnd_6676721 : Nat := 1142789022989292344027275

theorem tailTrace_6676721 : CollatzResearch.WordTrace tailWord_6676721 prefixEnd_6676721 1142789022989292344027275 := by
  unfold tailWord_6676721
  simp only [CollatzResearch.WordTrace]
  refine ⟨243520020844387585008534017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162346680562925056672356011 243520020844387585008534017)
  ·
    refine ⟨182640015633290688756400513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 243520020844387585008534017 182640015633290688756400513)
    ·
      refine ⟨136980011724968016567300385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 182640015633290688756400513 136980011724968016567300385)
      ·
        refine ⟨102735008793726012425475289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 136980011724968016567300385 102735008793726012425475289)
        ·
          refine ⟨77051256595294509319106467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 102735008793726012425475289 77051256595294509319106467)
          ·
            refine ⟨115576884892941763978659701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77051256595294509319106467 115576884892941763978659701)
            ·
              refine ⟨10835332958713290372999347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 115576884892941763978659701 10835332958713290372999347)
              ·
                refine ⟨16252999438069935559499021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10835332958713290372999347 16252999438069935559499021)
                ·
                  refine ⟨6094874789276225834812133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16252999438069935559499021 6094874789276225834812133)
                  ·
                    refine ⟨1142789022989292344027275, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6094874789276225834812133 1142789022989292344027275)
                    ·
                      rfl

theorem cell23_6676721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 5, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 5, 1, 3, 4].length) (baseStart_6676721 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6676721 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6676721 prefixEnd_6676721 := by exact prefixLift 6676721
  have htrace : WordTrace (prefixWord ++ tailWord_6676721) baseStart_6676721 baseEnd_6676721 := by
    simpa [prefixWord, tailWord_6676721, baseEnd_6676721] using wordTrace_append hprefix tailTrace_6676721
  have hstable : (prefixWord ++ tailWord_6676721).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6676721).length < 2 ^ (prefixWord ++ tailWord_6676721).sum := by decide
  have hdescent : baseEnd_6676721 < baseStart_6676721 := by decide
  rcases family_descends (prefixWord ++ tailWord_6676721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6676772 : List Nat := [2, 3, 1, 3, 1, 4, 2, 2, 1, 4]
def baseStart_6676772 : Nat := 118140960795 + 6676772 * 2 ^ 59
def prefixEnd_6676772 : Nat := 4983230072969 + 3 ^ 40 * 6676772 * 2
def baseEnd_6676772 : Nat := 1142797752160418777514697

theorem tailTrace_6676772 : CollatzResearch.WordTrace tailWord_6676772 prefixEnd_6676772 1142797752160418777514697 := by
  unfold tailWord_6676772
  simp only [CollatzResearch.WordTrace]
  refine ⟨121760940483601410359320285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 162347920644801880479093713 121760940483601410359320285)
  ·
    refine ⟨45660352681350528884745107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 121760940483601410359320285 45660352681350528884745107)
    ·
      refine ⟨68490529022025793327117661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45660352681350528884745107 68490529022025793327117661)
      ·
        refine ⟨25683948383259672497669123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 68490529022025793327117661 25683948383259672497669123)
        ·
          refine ⟨38525922574889508746503685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25683948383259672497669123 38525922574889508746503685)
          ·
            refine ⟨7223610482791782889969441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 38525922574889508746503685 7223610482791782889969441)
            ·
              refine ⟨5417707862093837167477081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7223610482791782889969441 5417707862093837167477081)
              ·
                refine ⟨4063280896570377875607811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5417707862093837167477081 4063280896570377875607811)
                ·
                  refine ⟨6094921344855566813411717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4063280896570377875607811 6094921344855566813411717)
                  ·
                    refine ⟨1142797752160418777514697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6094921344855566813411717 1142797752160418777514697)
                    ·
                      rfl

theorem cell23_6676772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 4, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 4, 2, 2, 1, 4].length) (baseStart_6676772 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6676772 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6676772 prefixEnd_6676772 := by exact prefixLift 6676772
  have htrace : WordTrace (prefixWord ++ tailWord_6676772) baseStart_6676772 baseEnd_6676772 := by
    simpa [prefixWord, tailWord_6676772, baseEnd_6676772] using wordTrace_append hprefix tailTrace_6676772
  have hstable : (prefixWord ++ tailWord_6676772).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6676772).length < 2 ^ (prefixWord ++ tailWord_6676772).sum := by decide
  have hdescent : baseEnd_6676772 < baseStart_6676772 := by decide
  rcases family_descends (prefixWord ++ tailWord_6676772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6676835 : List Nat := [1, 1, 1, 5, 2, 1, 4, 1, 3, 2, 2]
def baseStart_6676835 : Nat := 118140960795 + 6676835 * 2 ^ 59
def prefixEnd_6676835 : Nat := 4983230072969 + 3 ^ 40 * 6676835 * 2
def baseEnd_6676835 : Nat := 3428425605762489586056301

theorem tailTrace_6676835 : CollatzResearch.WordTrace tailWord_6676835 prefixEnd_6676835 3428425605762489586056301 := by
  unfold tailWord_6676835
  simp only [CollatzResearch.WordTrace]
  refine ⟨243524178765974582478183959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162349452510649721652122639 243524178765974582478183959)
  ·
    refine ⟨365286268148961873717275939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 243524178765974582478183959 365286268148961873717275939)
    ·
      refine ⟨547929402223442810575913909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 365286268148961873717275939 547929402223442810575913909)
      ·
        refine ⟨51368381458447763491491929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 547929402223442810575913909 51368381458447763491491929)
        ·
          refine ⟨38526286093835822618618947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51368381458447763491491929 38526286093835822618618947)
          ·
            refine ⟨57789429140753733927928421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38526286093835822618618947 57789429140753733927928421)
            ·
              refine ⟨10835517963891325111486579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 57789429140753733927928421 10835517963891325111486579)
              ·
                refine ⟨16253276945836987667229869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10835517963891325111486579 16253276945836987667229869)
                ·
                  refine ⟨6094978854688870375211201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16253276945836987667229869 6094978854688870375211201)
                  ·
                    refine ⟨4571234141016652781408401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6094978854688870375211201 4571234141016652781408401)
                    ·
                      refine ⟨3428425605762489586056301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4571234141016652781408401 3428425605762489586056301)
                      ·
                        rfl

theorem cell23_6676835_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 4, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 4, 1, 3, 2, 2].length) (baseStart_6676835 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6676835 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6676835 prefixEnd_6676835 := by exact prefixLift 6676835
  have htrace : WordTrace (prefixWord ++ tailWord_6676835) baseStart_6676835 baseEnd_6676835 := by
    simpa [prefixWord, tailWord_6676835, baseEnd_6676835] using wordTrace_append hprefix tailTrace_6676835
  have hstable : (prefixWord ++ tailWord_6676835).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6676835).length < 2 ^ (prefixWord ++ tailWord_6676835).sum := by decide
  have hdescent : baseEnd_6676835 < baseStart_6676835 := by decide
  rcases family_descends (prefixWord ++ tailWord_6676835) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6676845 : List Nat := [1, 5, 1, 1, 1, 2, 5, 1, 2, 4]
def baseStart_6676845 : Nat := 118140960795 + 6676845 * 2 ^ 59
def prefixEnd_6676845 : Nat := 4983230072969 + 3 ^ 40 * 6676845 * 2
def baseEnd_6676845 : Nat := 1142810246856344848977085

theorem tailTrace_6676845 : CollatzResearch.WordTrace tailWord_6676845 prefixEnd_6676845 1142810246856344848977085 := by
  unfold tailWord_6676845
  simp only [CollatzResearch.WordTrace]
  refine ⟨243524543495938354186047989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162349695663958902790698659 243524543495938354186047989)
  ·
    refine ⟨22830425952744220704941999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 243524543495938354186047989 22830425952744220704941999)
    ·
      refine ⟨34245638929116331057412999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22830425952744220704941999 34245638929116331057412999)
      ·
        refine ⟨51368458393674496586119499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34245638929116331057412999 51368458393674496586119499)
        ·
          refine ⟨77052687590511744879179249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51368458393674496586119499 77052687590511744879179249)
          ·
            refine ⟨57789515692883808659384437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 77052687590511744879179249 57789515692883808659384437)
            ·
              refine ⟨5417767096207857061817291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 57789515692883808659384437 5417767096207857061817291)
              ·
                refine ⟨8126650644311785592725937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5417767096207857061817291 8126650644311785592725937)
                ·
                  refine ⟨6094987983233839194544453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8126650644311785592725937 6094987983233839194544453)
                  ·
                    refine ⟨1142810246856344848977085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6094987983233839194544453 1142810246856344848977085)
                    ·
                      rfl

theorem cell23_6676845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 5, 1, 2, 4].length) (baseStart_6676845 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6676845 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6676845 prefixEnd_6676845 := by exact prefixLift 6676845
  have htrace : WordTrace (prefixWord ++ tailWord_6676845) baseStart_6676845 baseEnd_6676845 := by
    simpa [prefixWord, tailWord_6676845, baseEnd_6676845] using wordTrace_append hprefix tailTrace_6676845
  have hstable : (prefixWord ++ tailWord_6676845).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6676845).length < 2 ^ (prefixWord ++ tailWord_6676845).sum := by decide
  have hdescent : baseEnd_6676845 < baseStart_6676845 := by decide
  rcases family_descends (prefixWord ++ tailWord_6676845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6676848 : List Nat := [2, 1, 1, 1, 4, 5, 1, 1, 1, 2, 4]
def baseStart_6676848 : Nat := 118140960795 + 6676848 * 2 ^ 59
def prefixEnd_6676848 : Nat := 4983230072969 + 3 ^ 40 * 6676848 * 2
def baseEnd_6676848 : Nat := 3428432281010998035193741

theorem tailTrace_6676848 : CollatzResearch.WordTrace tailWord_6676848 prefixEnd_6676848 3428432281010998035193741 := by
  unfold tailWord_6676848
  simp only [CollatzResearch.WordTrace]
  refine ⟨121762326457463742849203599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 162349768609951657132271465 121762326457463742849203599)
  ·
    refine ⟨182643489686195614273805399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121762326457463742849203599 182643489686195614273805399)
    ·
      refine ⟨273965234529293421410708099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 182643489686195614273805399 273965234529293421410708099)
      ·
        refine ⟨410947851793940132116062149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 273965234529293421410708099 410947851793940132116062149)
        ·
          refine ⟨77052722211363774771761653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 410947851793940132116062149 77052722211363774771761653)
          ·
            refine ⟨7223692707315353884852655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 77052722211363774771761653 7223692707315353884852655)
            ·
              refine ⟨10835539060973030827278983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7223692707315353884852655 10835539060973030827278983)
              ·
                refine ⟨16253308591459546240918475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10835539060973030827278983 16253308591459546240918475)
                ·
                  refine ⟨24379962887189319361377713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16253308591459546240918475 24379962887189319361377713)
                  ·
                    refine ⟨18284972165391989521033285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24379962887189319361377713 18284972165391989521033285)
                    ·
                      refine ⟨3428432281010998035193741, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18284972165391989521033285 3428432281010998035193741)
                      ·
                        rfl

theorem cell23_6676848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 5, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 5, 1, 1, 1, 2, 4].length) (baseStart_6676848 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6676848 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6676848 prefixEnd_6676848 := by exact prefixLift 6676848
  have htrace : WordTrace (prefixWord ++ tailWord_6676848) baseStart_6676848 baseEnd_6676848 := by
    simpa [prefixWord, tailWord_6676848, baseEnd_6676848] using wordTrace_append hprefix tailTrace_6676848
  have hstable : (prefixWord ++ tailWord_6676848).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6676848).length < 2 ^ (prefixWord ++ tailWord_6676848).sum := by decide
  have hdescent : baseEnd_6676848 < baseStart_6676848 := by decide
  rcases family_descends (prefixWord ++ tailWord_6676848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6676868 : List Nat := [2, 3, 2, 1, 1, 2, 1, 1, 6, 1, 3]
def baseStart_6676868 : Nat := 118140960795 + 6676868 * 2 ^ 59
def prefixEnd_6676868 : Nat := 4983230072969 + 3 ^ 40 * 6676868 * 2
def baseEnd_6676868 : Nat := 3428442550624087956943649

theorem tailTrace_6676868 : CollatzResearch.WordTrace tailWord_6676868 prefixEnd_6676868 3428442550624087956943649 := by
  unfold tailWord_6676868
  simp only [CollatzResearch.WordTrace]
  refine ⟨121762691187427514557067629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 162350254916570019409423505 121762691187427514557067629)
  ·
    refine ⟨45661009195285317958900361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 121762691187427514557067629 45661009195285317958900361)
    ·
      refine ⟨34245756896463988469175271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45661009195285317958900361 34245756896463988469175271)
      ·
        refine ⟨51368635344695982703762907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34245756896463988469175271 51368635344695982703762907)
        ·
          refine ⟨77052953017043974055644361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51368635344695982703762907 77052953017043974055644361)
          ·
            refine ⟨57789714762782980541733271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 77052953017043974055644361 57789714762782980541733271)
            ·
              refine ⟨86684572144174470812599907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57789714762782980541733271 86684572144174470812599907)
              ·
                refine ⟨130026858216261706218899861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 86684572144174470812599907 130026858216261706218899861)
                ·
                  refine ⟨6095008978887267479010931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 130026858216261706218899861 6095008978887267479010931)
                  ·
                    refine ⟨9142513468330901218516397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6095008978887267479010931 9142513468330901218516397)
                    ·
                      refine ⟨3428442550624087956943649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9142513468330901218516397 3428442550624087956943649)
                      ·
                        rfl

theorem cell23_6676868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 1, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 1, 1, 6, 1, 3].length) (baseStart_6676868 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6676868 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6676868 prefixEnd_6676868 := by exact prefixLift 6676868
  have htrace : WordTrace (prefixWord ++ tailWord_6676868) baseStart_6676868 baseEnd_6676868 := by
    simpa [prefixWord, tailWord_6676868, baseEnd_6676868] using wordTrace_append hprefix tailTrace_6676868
  have hstable : (prefixWord ++ tailWord_6676868).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6676868).length < 2 ^ (prefixWord ++ tailWord_6676868).sum := by decide
  have hdescent : baseEnd_6676868 < baseStart_6676868 := by decide
  rcases family_descends (prefixWord ++ tailWord_6676868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6676906 : List Nat := [3, 1, 6, 1, 1, 2, 1, 2, 1, 2, 3]
def baseStart_6676906 : Nat := 118140960795 + 6676906 * 2 ^ 59
def prefixEnd_6676906 : Nat := 4983230072969 + 3 ^ 40 * 6676906 * 2
def baseEnd_6676906 : Nat := 3428462062888958808268475

theorem tailTrace_6676906 : CollatzResearch.WordTrace tailWord_6676906 prefixEnd_6676906 3428462062888958808268475 := by
  unfold tailWord_6676906
  simp only [CollatzResearch.WordTrace]
  refine ⟨60881692087179340401004643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 162351178899144907736012381 60881692087179340401004643)
  ·
    refine ⟨91322538130769010601506965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60881692087179340401004643 91322538130769010601506965)
    ·
      refine ⟨4280743974879797371945639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 91322538130769010601506965 4280743974879797371945639)
      ·
        refine ⟨6421115962319696057918459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4280743974879797371945639 6421115962319696057918459)
        ·
          refine ⟨9631673943479544086877689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6421115962319696057918459 9631673943479544086877689)
          ·
            refine ⟨7223755457609658065158267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9631673943479544086877689 7223755457609658065158267)
            ·
              refine ⟨10835633186414487097737401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7223755457609658065158267 10835633186414487097737401)
              ·
                refine ⟨8126724889810865323303051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10835633186414487097737401 8126724889810865323303051)
                ·
                  refine ⟨12190087334716297984954577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8126724889810865323303051 12190087334716297984954577)
                  ·
                    refine ⟨9142565501037223488715933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12190087334716297984954577 9142565501037223488715933)
                    ·
                      refine ⟨3428462062888958808268475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9142565501037223488715933 3428462062888958808268475)
                      ·
                        rfl

theorem cell23_6676906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 1, 2, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 1, 2, 1, 2, 1, 2, 3].length) (baseStart_6676906 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6676906 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6676906 prefixEnd_6676906 := by exact prefixLift 6676906
  have htrace : WordTrace (prefixWord ++ tailWord_6676906) baseStart_6676906 baseEnd_6676906 := by
    simpa [prefixWord, tailWord_6676906, baseEnd_6676906] using wordTrace_append hprefix tailTrace_6676906
  have hstable : (prefixWord ++ tailWord_6676906).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6676906).length < 2 ^ (prefixWord ++ tailWord_6676906).sum := by decide
  have hdescent : baseEnd_6676906 < baseStart_6676906 := by decide
  rcases family_descends (prefixWord ++ tailWord_6676906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6676908 : List Nat := [2, 2, 1, 1, 1, 1, 3, 5, 1, 4, 2]
def baseStart_6676908 : Nat := 118140960795 + 6676908 * 2 ^ 59
def prefixEnd_6676908 : Nat := 4983230072969 + 3 ^ 40 * 6676908 * 2
def baseEnd_6676908 : Nat := 3428463089850267800443465

theorem tailTrace_6676908 : CollatzResearch.WordTrace tailWord_6676908 prefixEnd_6676908 3428463089850267800443465 := by
  unfold tailWord_6676908
  simp only [CollatzResearch.WordTrace]
  refine ⟨121763420647355057972795689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 162351227529806743963727585 121763420647355057972795689)
  ·
    refine ⟨91322565485516293479596767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 121763420647355057972795689 91322565485516293479596767)
    ·
      refine ⟨136983848228274440219395151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91322565485516293479596767 136983848228274440219395151)
      ·
        refine ⟨205475772342411660329092727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 136983848228274440219395151 205475772342411660329092727)
        ·
          refine ⟨308213658513617490493639091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 205475772342411660329092727 308213658513617490493639091)
          ·
            refine ⟨462320487770426235740458637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 308213658513617490493639091 462320487770426235740458637)
            ·
              refine ⟨173370182913909838402671989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 462320487770426235740458637 173370182913909838402671989)
              ·
                refine ⟨16253454648179047350250499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 173370182913909838402671989 16253454648179047350250499)
                ·
                  refine ⟨24380181972268571025375749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16253454648179047350250499 24380181972268571025375749)
                  ·
                    refine ⟨4571284119800357067257953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24380181972268571025375749 4571284119800357067257953)
                    ·
                      refine ⟨3428463089850267800443465, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4571284119800357067257953 3428463089850267800443465)
                      ·
                        rfl

theorem cell23_6676908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 4, 2].length) (baseStart_6676908 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6676908 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6676908 prefixEnd_6676908 := by exact prefixLift 6676908
  have htrace : WordTrace (prefixWord ++ tailWord_6676908) baseStart_6676908 baseEnd_6676908 := by
    simpa [prefixWord, tailWord_6676908, baseEnd_6676908] using wordTrace_append hprefix tailTrace_6676908
  have hstable : (prefixWord ++ tailWord_6676908).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6676908).length < 2 ^ (prefixWord ++ tailWord_6676908).sum := by decide
  have hdescent : baseEnd_6676908 < baseStart_6676908 := by decide
  rcases family_descends (prefixWord ++ tailWord_6676908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6676925 : List Nat := [1, 4, 1, 2, 2, 3, 1, 2, 1, 4, 2]
def baseStart_6676925 : Nat := 118140960795 + 6676925 * 2 ^ 59
def prefixEnd_6676925 : Nat := 4983230072969 + 3 ^ 40 * 6676925 * 2
def baseEnd_6676925 : Nat := 3428471819021394233930887

theorem tailTrace_6676925 : CollatzResearch.WordTrace tailWord_6676925 prefixEnd_6676925 3428471819021394233930887 := by
  unfold tailWord_6676925
  simp only [CollatzResearch.WordTrace]
  refine ⟨243527461335648527848960229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162351640890432351899306819 243527461335648527848960229)
  ·
    refine ⟨45661399000434098971680043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 243527461335648527848960229 45661399000434098971680043)
    ·
      refine ⟨68492098500651148457520065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45661399000434098971680043 68492098500651148457520065)
      ·
        refine ⟨51369073875488361343140049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68492098500651148457520065 51369073875488361343140049)
        ·
          refine ⟨38526805406616271007355037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51369073875488361343140049 38526805406616271007355037)
          ·
            refine ⟨14447552027481101627758139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38526805406616271007355037 14447552027481101627758139)
            ·
              refine ⟨21671328041221652441637209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14447552027481101627758139 21671328041221652441637209)
              ·
                refine ⟨16253496030916239331227907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21671328041221652441637209 16253496030916239331227907)
                ·
                  refine ⟨24380244046374358996841861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16253496030916239331227907 24380244046374358996841861)
                  ·
                    refine ⟨4571295758695192311907849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24380244046374358996841861 4571295758695192311907849)
                    ·
                      refine ⟨3428471819021394233930887, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4571295758695192311907849 3428471819021394233930887)
                      ·
                        rfl

theorem cell23_6676925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 3, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 3, 1, 2, 1, 4, 2].length) (baseStart_6676925 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6676925 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6676925 prefixEnd_6676925 := by exact prefixLift 6676925
  have htrace : WordTrace (prefixWord ++ tailWord_6676925) baseStart_6676925 baseEnd_6676925 := by
    simpa [prefixWord, tailWord_6676925, baseEnd_6676925] using wordTrace_append hprefix tailTrace_6676925
  have hstable : (prefixWord ++ tailWord_6676925).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6676925).length < 2 ^ (prefixWord ++ tailWord_6676925).sum := by decide
  have hdescent : baseEnd_6676925 < baseStart_6676925 := by decide
  rcases family_descends (prefixWord ++ tailWord_6676925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6676961 : List Nat := [1, 2, 3, 1, 2, 2, 2, 2, 1, 7]
def baseStart_6676961 : Nat := 118140960795 + 6676961 * 2 ^ 59
def prefixEnd_6676961 : Nat := 4983230072969 + 3 ^ 40 * 6676961 * 2
def baseEnd_6676961 : Nat := 1142830101441652031026907

theorem tailTrace_6676961 : CollatzResearch.WordTrace tailWord_6676961 prefixEnd_6676961 1142830101441652031026907 := by
  unfold tailWord_6676961
  simp only [CollatzResearch.WordTrace]
  refine ⟨243528774363518105997270737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162352516242345403998180491 243528774363518105997270737)
  ·
    refine ⟨182646580772638579497953053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 243528774363518105997270737 182646580772638579497953053)
    ·
      refine ⟨68492467789739467311732395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 182646580772638579497953053 68492467789739467311732395)
      ·
        refine ⟨102738701684609200967598593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68492467789739467311732395 102738701684609200967598593)
        ·
          refine ⟨77054026263456900725698945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 102738701684609200967598593 77054026263456900725698945)
          ·
            refine ⟨57790519697592675544274209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 77054026263456900725698945 57790519697592675544274209)
            ·
              refine ⟨43342889773194506658205657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 57790519697592675544274209 43342889773194506658205657)
              ·
                refine ⟨32507167329895879993654243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43342889773194506658205657 32507167329895879993654243)
                ·
                  refine ⟨48760750994843819990481365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32507167329895879993654243 48760750994843819990481365)
                  ·
                    refine ⟨1142830101441652031026907, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 48760750994843819990481365 1142830101441652031026907)
                    ·
                      rfl

theorem cell23_6676961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 2, 2, 1, 7].length) (baseStart_6676961 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6676961 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6676961 prefixEnd_6676961 := by exact prefixLift 6676961
  have htrace : WordTrace (prefixWord ++ tailWord_6676961) baseStart_6676961 baseEnd_6676961 := by
    simpa [prefixWord, tailWord_6676961, baseEnd_6676961] using wordTrace_append hprefix tailTrace_6676961
  have hstable : (prefixWord ++ tailWord_6676961).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6676961).length < 2 ^ (prefixWord ++ tailWord_6676961).sum := by decide
  have hdescent : baseEnd_6676961 < baseStart_6676961 := by decide
  rcases family_descends (prefixWord ++ tailWord_6676961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6677011 : List Nat := [1, 1, 1, 2, 1, 5, 1, 2, 2, 1, 6]
def baseStart_6677011 : Nat := 118140960795 + 6677011 * 2 ^ 59
def prefixEnd_6677011 : Nat := 4983230072969 + 3 ^ 40 * 6677011 * 2
def baseEnd_6677011 : Nat := 3428515978357680897455491

theorem tailTrace_6677011 : CollatzResearch.WordTrace tailWord_6677011 prefixEnd_6677011 3428515978357680897455491 := by
  unfold tailWord_6677011
  simp only [CollatzResearch.WordTrace]
  refine ⟨243530598013336964536590887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162353732008891309691060591 243530598013336964536590887)
  ·
    refine ⟨365295897020005446804886331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 243530598013336964536590887 365295897020005446804886331)
    ·
      refine ⟨547943845530008170207329497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 365295897020005446804886331 547943845530008170207329497)
      ·
        refine ⟨410957884147506127655497123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 547943845530008170207329497 410957884147506127655497123)
        ·
          refine ⟨616436826221259191483245685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 410957884147506127655497123 616436826221259191483245685)
          ·
            refine ⟨57790952458243049201554283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 616436826221259191483245685 57790952458243049201554283)
            ·
              refine ⟨86686428687364573802331425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57790952458243049201554283 86686428687364573802331425)
              ·
                refine ⟨65014821515523430351748569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 86686428687364573802331425 65014821515523430351748569)
                ·
                  refine ⟨48761116136642572763811427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 65014821515523430351748569 48761116136642572763811427)
                  ·
                    refine ⟨73141674204963859145717141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 48761116136642572763811427 73141674204963859145717141)
                    ·
                      refine ⟨3428515978357680897455491, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 73141674204963859145717141 3428515978357680897455491)
                      ·
                        rfl

theorem cell23_6677011_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 1, 2, 2, 1, 6].length) (baseStart_6677011 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6677011 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6677011 prefixEnd_6677011 := by exact prefixLift 6677011
  have htrace : WordTrace (prefixWord ++ tailWord_6677011) baseStart_6677011 baseEnd_6677011 := by
    simpa [prefixWord, tailWord_6677011, baseEnd_6677011] using wordTrace_append hprefix tailTrace_6677011
  have hstable : (prefixWord ++ tailWord_6677011).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6677011).length < 2 ^ (prefixWord ++ tailWord_6677011).sum := by decide
  have hdescent : baseEnd_6677011 < baseStart_6677011 := by decide
  rcases family_descends (prefixWord ++ tailWord_6677011) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6677018 : List Nat := [3, 1, 1, 3, 1, 1, 3, 2, 1, 4, 3]
def baseStart_6677018 : Nat := 118140960795 + 6677018 * 2 ^ 59
def prefixEnd_6677018 : Nat := 4983230072969 + 3 ^ 40 * 6677018 * 2
def baseEnd_6677018 : Nat := 3428519572722262370067959

theorem tailTrace_6677018 : CollatzResearch.WordTrace tailWord_6677018 prefixEnd_6677018 3428519572722262370067959 := by
  unfold tailWord_6677018
  simp only [CollatzResearch.WordTrace]
  refine ⟨60882713331077901183023927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 162353902216207736488063805 60882713331077901183023927)
  ·
    refine ⟨91324069996616851774535891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60882713331077901183023927 91324069996616851774535891)
    ·
      refine ⟨136986104994925277661803837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91324069996616851774535891 136986104994925277661803837)
      ·
        refine ⟨51369789373096979123176439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 136986104994925277661803837 51369789373096979123176439)
        ·
          refine ⟨77054684059645468684764659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51369789373096979123176439 77054684059645468684764659)
          ·
            refine ⟨115582026089468203027146989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77054684059645468684764659 115582026089468203027146989)
            ·
              refine ⟨43343259783550576135180121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 115582026089468203027146989 43343259783550576135180121)
              ·
                refine ⟨32507444837662932101385091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43343259783550576135180121 32507444837662932101385091)
                ·
                  refine ⟨48761167256494398152077637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32507444837662932101385091 48761167256494398152077637)
                  ·
                    refine ⟨9142718860592699653514557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 48761167256494398152077637 9142718860592699653514557)
                    ·
                      refine ⟨3428519572722262370067959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9142718860592699653514557 3428519572722262370067959)
                      ·
                        rfl

theorem cell23_6677018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 3, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 3, 2, 1, 4, 3].length) (baseStart_6677018 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6677018 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6677018 prefixEnd_6677018 := by exact prefixLift 6677018
  have htrace : WordTrace (prefixWord ++ tailWord_6677018) baseStart_6677018 baseEnd_6677018 := by
    simpa [prefixWord, tailWord_6677018, baseEnd_6677018] using wordTrace_append hprefix tailTrace_6677018
  have hstable : (prefixWord ++ tailWord_6677018).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6677018).length < 2 ^ (prefixWord ++ tailWord_6677018).sum := by decide
  have hdescent : baseEnd_6677018 < baseStart_6677018 := by decide
  rcases family_descends (prefixWord ++ tailWord_6677018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6677042 : List Nat := [3, 2, 1, 1, 2, 1, 5, 3, 1, 4]
def baseStart_6677042 : Nat := 118140960795 + 6677042 * 2 ^ 59
def prefixEnd_6677042 : Nat := 4983230072969 + 3 ^ 40 * 6677042 * 2
def baseEnd_6677042 : Nat := 1142843965419323425389283

theorem tailTrace_6677042 : CollatzResearch.WordTrace tailWord_6677042 prefixEnd_6677042 1142843965419323425389283 := by
  unfold tailWord_6677042
  simp only [CollatzResearch.WordTrace]
  refine ⟨60882932169056164207742345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 162354485784149771220646253 60882932169056164207742345)
  ·
    refine ⟨45662199126792123155806759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60882932169056164207742345 45662199126792123155806759)
    ·
      refine ⟨68493298690188184733710139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45662199126792123155806759 68493298690188184733710139)
      ·
        refine ⟨102739948035282277100565209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68493298690188184733710139 102739948035282277100565209)
        ·
          refine ⟨77054961026461707825423907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 102739948035282277100565209 77054961026461707825423907)
          ·
            refine ⟨115582441539692561738135861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77054961026461707825423907 115582441539692561738135861)
            ·
              refine ⟨10835853894346177662950237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 115582441539692561738135861 10835853894346177662950237)
              ·
                refine ⟨4063445210379816623606339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10835853894346177662950237 4063445210379816623606339)
                ·
                  refine ⟨6095167815569724935409509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4063445210379816623606339 6095167815569724935409509)
                  ·
                    refine ⟨1142843965419323425389283, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6095167815569724935409509 1142843965419323425389283)
                    ·
                      rfl

theorem cell23_6677042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 5, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 5, 3, 1, 4].length) (baseStart_6677042 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6677042 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6677042 prefixEnd_6677042 := by exact prefixLift 6677042
  have htrace : WordTrace (prefixWord ++ tailWord_6677042) baseStart_6677042 baseEnd_6677042 := by
    simpa [prefixWord, tailWord_6677042, baseEnd_6677042] using wordTrace_append hprefix tailTrace_6677042
  have hstable : (prefixWord ++ tailWord_6677042).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6677042).length < 2 ^ (prefixWord ++ tailWord_6677042).sum := by decide
  have hdescent : baseEnd_6677042 < baseStart_6677042 := by decide
  rcases family_descends (prefixWord ++ tailWord_6677042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6677068 : List Nat := [2, 2, 1, 3, 1, 2, 2, 2, 3, 5]
def baseStart_6677068 : Nat := 118140960795 + 6677068 * 2 ^ 59
def prefixEnd_6677068 : Nat := 4983230072969 + 3 ^ 40 * 6677068 * 2
def baseEnd_6677068 : Nat := 1142848415584995724814243

theorem tailTrace_6677068 : CollatzResearch.WordTrace tailWord_6677068 prefixEnd_6677068 1142848415584995724814243 := by
  unfold tailWord_6677068
  simp only [CollatzResearch.WordTrace]
  refine ⟨121766338487065231635707929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 162355117982753642180943905 121766338487065231635707929)
  ·
    refine ⟨91324753865298923726780947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 121766338487065231635707929 91324753865298923726780947)
    ·
      refine ⟨136987130797948385590171421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91324753865298923726780947 136987130797948385590171421)
      ·
        refine ⟨51370174049230644596314283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 136987130797948385590171421 51370174049230644596314283)
        ·
          refine ⟨77055261073845966894471425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51370174049230644596314283 77055261073845966894471425)
          ·
            refine ⟨57791445805384475170853569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 77055261073845966894471425 57791445805384475170853569)
            ·
              refine ⟨43343584354038356378140177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 57791445805384475170853569 43343584354038356378140177)
              ·
                refine ⟨32507688265528767283605133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43343584354038356378140177 32507688265528767283605133)
                ·
                  refine ⟨12190383099573287731351925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32507688265528767283605133 12190383099573287731351925)
                  ·
                    refine ⟨1142848415584995724814243, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12190383099573287731351925 1142848415584995724814243)
                    ·
                      rfl

theorem cell23_6677068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 2, 2, 3, 5].length) (baseStart_6677068 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6677068 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6677068 prefixEnd_6677068 := by exact prefixLift 6677068
  have htrace : WordTrace (prefixWord ++ tailWord_6677068) baseStart_6677068 baseEnd_6677068 := by
    simpa [prefixWord, tailWord_6677068, baseEnd_6677068] using wordTrace_append hprefix tailTrace_6677068
  have hstable : (prefixWord ++ tailWord_6677068).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6677068).length < 2 ^ (prefixWord ++ tailWord_6677068).sum := by decide
  have hdescent : baseEnd_6677068 < baseStart_6677068 := by decide
  rcases family_descends (prefixWord ++ tailWord_6677068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6677092 : List Nat := [2, 3, 1, 1, 2, 2, 4, 1, 2, 3, 2]
def baseStart_6677092 : Nat := 118140960795 + 6677092 * 2 ^ 59
def prefixEnd_6677092 : Nat := 4983230072969 + 3 ^ 40 * 6677092 * 2
def baseEnd_6677092 : Nat := 3428557570290695080542619

theorem tailTrace_6677092 : CollatzResearch.WordTrace tailWord_6677092 prefixEnd_6677092 3428557570290695080542619 := by
  unfold tailWord_6677092
  simp only [CollatzResearch.WordTrace]
  refine ⟨121766776163021757685144765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 162355701550695676913526353 121766776163021757685144765)
  ·
    refine ⟨45662541061133159131929287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 121766776163021757685144765 45662541061133159131929287)
    ·
      refine ⟨68493811591699738697893931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45662541061133159131929287 68493811591699738697893931)
      ·
        refine ⟨102740717387549608046840897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68493811591699738697893931 102740717387549608046840897)
        ·
          refine ⟨77055538040662206035130673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 102740717387549608046840897 77055538040662206035130673)
          ·
            refine ⟨57791653530496654526348005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 77055538040662206035130673 57791653530496654526348005)
            ·
              refine ⟨10835935036968122723690251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 57791653530496654526348005 10835935036968122723690251)
              ·
                refine ⟨16253902555452184085535377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10835935036968122723690251 16253902555452184085535377)
                ·
                  refine ⟨12190426916589138064151533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16253902555452184085535377 12190426916589138064151533)
                  ·
                    refine ⟨4571410093720926774056825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12190426916589138064151533 4571410093720926774056825)
                    ·
                      refine ⟨3428557570290695080542619, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4571410093720926774056825 3428557570290695080542619)
                      ·
                        rfl

theorem cell23_6677092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 4, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 4, 1, 2, 3, 2].length) (baseStart_6677092 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6677092 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6677092 prefixEnd_6677092 := by exact prefixLift 6677092
  have htrace : WordTrace (prefixWord ++ tailWord_6677092) baseStart_6677092 baseEnd_6677092 := by
    simpa [prefixWord, tailWord_6677092, baseEnd_6677092] using wordTrace_append hprefix tailTrace_6677092
  have hstable : (prefixWord ++ tailWord_6677092).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6677092).length < 2 ^ (prefixWord ++ tailWord_6677092).sum := by decide
  have hdescent : baseEnd_6677092 < baseStart_6677092 := by decide
  rcases family_descends (prefixWord ++ tailWord_6677092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6677125 : List Nat := [1, 3, 1, 1, 4, 2, 1, 2, 3, 2, 3]
def baseStart_6677125 : Nat := 118140960795 + 6677125 * 2 ^ 59
def prefixEnd_6677125 : Nat := 4983230072969 + 3 ^ 40 * 6677125 * 2
def baseEnd_6677125 : Nat := 3428574515152293451429967

theorem tailTrace_6677125 : CollatzResearch.WordTrace tailWord_6677125 prefixEnd_6677125 3428574515152293451429967 := by
  unfold tailWord_6677125
  simp only [CollatzResearch.WordTrace]
  refine ⟨243534755934923962006240829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162356503956615974670827219 243534755934923962006240829)
  ·
    refine ⟨91325533475596485752340311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 243534755934923962006240829 91325533475596485752340311)
    ·
      refine ⟨136988300213394728628510467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91325533475596485752340311 136988300213394728628510467)
      ·
        refine ⟨205482450320092092942765701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 136988300213394728628510467 205482450320092092942765701)
        ·
          refine ⟨38527959435017267426768569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 205482450320092092942765701 38527959435017267426768569)
          ·
            refine ⟨28895969576262950570076427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38527959435017267426768569 28895969576262950570076427)
            ·
              refine ⟨43343954364394425855114641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28895969576262950570076427 43343954364394425855114641)
              ·
                refine ⟨32507965773295819391335981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43343954364394425855114641 32507965773295819391335981)
                ·
                  refine ⟨12190487164985932271750993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32507965773295819391335981 12190487164985932271750993)
                  ·
                    refine ⟨9142865373739449203813245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12190487164985932271750993 9142865373739449203813245)
                    ·
                      refine ⟨3428574515152293451429967, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9142865373739449203813245 3428574515152293451429967)
                      ·
                        rfl

theorem cell23_6677125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 1, 2, 3, 2, 3].length) (baseStart_6677125 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6677125 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6677125 prefixEnd_6677125 := by exact prefixLift 6677125
  have htrace : WordTrace (prefixWord ++ tailWord_6677125) baseStart_6677125 baseEnd_6677125 := by
    simpa [prefixWord, tailWord_6677125, baseEnd_6677125] using wordTrace_append hprefix tailTrace_6677125
  have hstable : (prefixWord ++ tailWord_6677125).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6677125).length < 2 ^ (prefixWord ++ tailWord_6677125).sum := by decide
  have hdescent : baseEnd_6677125 < baseStart_6677125 := by decide
  rcases family_descends (prefixWord ++ tailWord_6677125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6677156 : List Nat := [2, 3, 1, 2, 2, 1, 4, 3, 1, 2, 2]
def baseStart_6677156 : Nat := 118140960795 + 6677156 * 2 ^ 59
def prefixEnd_6677156 : Nat := 4983230072969 + 3 ^ 40 * 6677156 * 2
def baseEnd_6677156 : Nat := 3428590433052582830142325

theorem tailTrace_6677156 : CollatzResearch.WordTrace tailWord_6677156 prefixEnd_6677156 3428590433052582830142325 := by
  unfold tailWord_6677156
  simp only [CollatzResearch.WordTrace]
  refine ⟨121767943298905827150309661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 162357257731874436200412881 121767943298905827150309661)
  ·
    refine ⟨45662978737089685181366123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 121767943298905827150309661 45662978737089685181366123)
    ·
      refine ⟨68494468105634527772049185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45662978737089685181366123 68494468105634527772049185)
      ·
        refine ⟨51370851079225895829036889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68494468105634527772049185 51370851079225895829036889)
        ·
          refine ⟨38528138309419421871777667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51370851079225895829036889 38528138309419421871777667)
          ·
            refine ⟨57792207464129132807666501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38528138309419421871777667 57792207464129132807666501)
            ·
              refine ⟨10836038899524212401437469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 57792207464129132807666501 10836038899524212401437469)
              ·
                refine ⟨4063514587321579650539051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10836038899524212401437469 4063514587321579650539051)
                ·
                  refine ⟨6095271880982369475808577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4063514587321579650539051 6095271880982369475808577)
                  ·
                    refine ⟨4571453910736777106856433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6095271880982369475808577 4571453910736777106856433)
                    ·
                      refine ⟨3428590433052582830142325, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4571453910736777106856433 3428590433052582830142325)
                      ·
                        rfl

theorem cell23_6677156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 4, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 4, 3, 1, 2, 2].length) (baseStart_6677156 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6677156 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6677156 prefixEnd_6677156 := by exact prefixLift 6677156
  have htrace : WordTrace (prefixWord ++ tailWord_6677156) baseStart_6677156 baseEnd_6677156 := by
    simpa [prefixWord, tailWord_6677156, baseEnd_6677156] using wordTrace_append hprefix tailTrace_6677156
  have hstable : (prefixWord ++ tailWord_6677156).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6677156).length < 2 ^ (prefixWord ++ tailWord_6677156).sum := by decide
  have hdescent : baseEnd_6677156 < baseStart_6677156 := by decide
  rcases family_descends (prefixWord ++ tailWord_6677156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6677162 : List Nat := [3, 1, 5, 2, 1, 1, 10]
def baseStart_6677162 : Nat := 118140960795 + 6677162 * 2 ^ 59
def prefixEnd_6677162 : Nat := 4983230072969 + 3 ^ 40 * 6677162 * 2
def baseEnd_6677162 : Nat := 42328314986870491440337

theorem tailTrace_6677162 : CollatzResearch.WordTrace tailWord_6677162 prefixEnd_6677162 42328314986870491440337 := by
  unfold tailWord_6677162
  simp only [CollatzResearch.WordTrace]
  refine ⟨60884026358947479331334435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 162357403623859944883558493 60884026358947479331334435)
  ·
    refine ⟨91326039538421218997001653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60884026358947479331334435 91326039538421218997001653)
    ·
      refine ⟨8561816206726989280968905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 91326039538421218997001653 8561816206726989280968905)
      ·
        refine ⟨6421362155045241960726679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8561816206726989280968905 6421362155045241960726679)
        ·
          refine ⟨9632043232567862941090019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6421362155045241960726679 9632043232567862941090019)
          ·
            refine ⟨14448064848851794411635029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9632043232567862941090019 14448064848851794411635029)
            ·
              refine ⟨42328314986870491440337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 14448064848851794411635029 42328314986870491440337)
              ·
                rfl

theorem cell23_6677162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 1, 1, 10].length) (baseStart_6677162 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6677162 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6677162 prefixEnd_6677162 := by exact prefixLift 6677162
  have htrace : WordTrace (prefixWord ++ tailWord_6677162) baseStart_6677162 baseEnd_6677162 := by
    simpa [prefixWord, tailWord_6677162, baseEnd_6677162] using wordTrace_append hprefix tailTrace_6677162
  have hstable : (prefixWord ++ tailWord_6677162).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6677162).length < 2 ^ (prefixWord ++ tailWord_6677162).sum := by decide
  have hdescent : baseEnd_6677162 < baseStart_6677162 := by decide
  rcases family_descends (prefixWord ++ tailWord_6677162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6677166 : List Nat := [4, 1, 4, 1, 1, 3, 1, 2, 2, 4]
def baseStart_6677166 : Nat := 118140960795 + 6677166 * 2 ^ 59
def prefixEnd_6677166 : Nat := 4983230072969 + 3 ^ 40 * 6677166 * 2
def baseEnd_6677166 : Nat := 1142865189286375930339093

theorem tailTrace_6677166 : CollatzResearch.WordTrace tailWord_6677166 prefixEnd_6677166 1142865189286375930339093 := by
  unfold tailWord_6677166
  simp only [CollatzResearch.WordTrace]
  refine ⟨30442031415971928251060419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 162357500885183617338988901 30442031415971928251060419)
  ·
    refine ⟨45663047123957892376590629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30442031415971928251060419 45663047123957892376590629)
    ·
      refine ⟨8561821335742104820610743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 45663047123957892376590629 8561821335742104820610743)
      ·
        refine ⟨12842732003613157230916115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8561821335742104820610743 12842732003613157230916115)
        ·
          refine ⟨19264098005419735846374173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12842732003613157230916115 19264098005419735846374173)
          ·
            refine ⟨7224036752032400942390315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19264098005419735846374173 7224036752032400942390315)
            ·
              refine ⟨10836055128048601413585473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7224036752032400942390315 10836055128048601413585473)
              ·
                refine ⟨8127041346036451060189105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10836055128048601413585473 8127041346036451060189105)
                ·
                  refine ⟨6095281009527338295141829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8127041346036451060189105 6095281009527338295141829)
                  ·
                    refine ⟨1142865189286375930339093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6095281009527338295141829 1142865189286375930339093)
                    ·
                      rfl

theorem cell23_6677166_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 3, 1, 2, 2, 4].length) (baseStart_6677166 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6677166 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6677166 prefixEnd_6677166 := by exact prefixLift 6677166
  have htrace : WordTrace (prefixWord ++ tailWord_6677166) baseStart_6677166 baseEnd_6677166 := by
    simpa [prefixWord, tailWord_6677166, baseEnd_6677166] using wordTrace_append hprefix tailTrace_6677166
  have hstable : (prefixWord ++ tailWord_6677166).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6677166).length < 2 ^ (prefixWord ++ tailWord_6677166).sum := by decide
  have hdescent : baseEnd_6677166 < baseStart_6677166 := by decide
  rcases family_descends (prefixWord ++ tailWord_6677166) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6677215 : List Nat := [1, 1, 2, 3, 2, 4, 1, 1, 2, 1, 5]
def baseStart_6677215 : Nat := 118140960795 + 6677215 * 2 ^ 59
def prefixEnd_6677215 : Nat := 4983230072969 + 3 ^ 40 * 6677215 * 2
def baseEnd_6677215 : Nat := 3428620728411198099304553

theorem tailTrace_6677215 : CollatzResearch.WordTrace tailWord_6677215 prefixEnd_6677215 3428620728411198099304553 := by
  unfold tailWord_6677215
  simp only [CollatzResearch.WordTrace]
  refine ⟨243538038504597907377017099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162358692336398604918011399 243538038504597907377017099)
  ·
    refine ⟨365307057756896861065525649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 243538038504597907377017099 365307057756896861065525649)
    ·
      refine ⟨273980293317672645799144237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 365307057756896861065525649 273980293317672645799144237)
      ·
        refine ⟨102742609994127242174679089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 273980293317672645799144237 102742609994127242174679089)
        ·
          refine ⟨77056957495595431631009317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 102742609994127242174679089 77056957495595431631009317)
          ·
            refine ⟨14448179530424143430814247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 77056957495595431631009317 14448179530424143430814247)
            ·
              refine ⟨21672269295636215146221371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14448179530424143430814247 21672269295636215146221371)
              ·
                refine ⟨32508403943454322719332057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21672269295636215146221371 32508403943454322719332057)
                ·
                  refine ⟨24381302957590742039499043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32508403943454322719332057 24381302957590742039499043)
                  ·
                    refine ⟨36571954436386113059248565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24381302957590742039499043 36571954436386113059248565)
                    ·
                      refine ⟨3428620728411198099304553, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36571954436386113059248565 3428620728411198099304553)
                      ·
                        rfl

theorem cell23_6677215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 4, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 4, 1, 1, 2, 1, 5].length) (baseStart_6677215 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6677215 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6677215 prefixEnd_6677215 := by exact prefixLift 6677215
  have htrace : WordTrace (prefixWord ++ tailWord_6677215) baseStart_6677215 baseEnd_6677215 := by
    simpa [prefixWord, tailWord_6677215, baseEnd_6677215] using wordTrace_append hprefix tailTrace_6677215
  have hstable : (prefixWord ++ tailWord_6677215).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6677215).length < 2 ^ (prefixWord ++ tailWord_6677215).sum := by decide
  have hdescent : baseEnd_6677215 < baseStart_6677215 := by decide
  rcases family_descends (prefixWord ++ tailWord_6677215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6677228 : List Nat := [2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 9]
def baseStart_6677228 : Nat := 118140960795 + 6677228 * 2 ^ 59
def prefixEnd_6677228 : Nat := 4983230072969 + 3 ^ 40 * 6677228 * 2
def baseEnd_6677228 : Nat := 3428627403659706548441993

theorem tailTrace_6677228 : CollatzResearch.WordTrace tailWord_6677228 prefixEnd_6677228 3428627403659706548441993 := by
  unfold tailWord_6677228
  simp only [CollatzResearch.WordTrace]
  refine ⟨121769256326775405298620169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 162359008435700540398160225 121769256326775405298620169)
  ·
    refine ⟨91326942245081553973965127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 121769256326775405298620169 91326942245081553973965127)
    ·
      refine ⟨136990413367622330960947691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91326942245081553973965127 136990413367622330960947691)
      ·
        refine ⟨205485620051433496441421537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 136990413367622330960947691 205485620051433496441421537)
        ·
          refine ⟨154114215038575122331066153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 205485620051433496441421537 154114215038575122331066153)
          ·
            refine ⟨115585661278931341748299615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 154114215038575122331066153 115585661278931341748299615)
            ·
              refine ⟨173378491918397012622449423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 115585661278931341748299615 173378491918397012622449423)
              ·
                refine ⟨260067737877595518933674135, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 173378491918397012622449423 260067737877595518933674135)
                ·
                  refine ⟨390101606816393278400511203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 260067737877595518933674135 390101606816393278400511203)
                  ·
                    refine ⟨585152410224589917600766805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 390101606816393278400511203 585152410224589917600766805)
                    ·
                      refine ⟨3428627403659706548441993, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 585152410224589917600766805 3428627403659706548441993)
                      ·
                        rfl

theorem cell23_6677228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 9].length) (baseStart_6677228 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6677228 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6677228 prefixEnd_6677228 := by exact prefixLift 6677228
  have htrace : WordTrace (prefixWord ++ tailWord_6677228) baseStart_6677228 baseEnd_6677228 := by
    simpa [prefixWord, tailWord_6677228, baseEnd_6677228] using wordTrace_append hprefix tailTrace_6677228
  have hstable : (prefixWord ++ tailWord_6677228).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6677228).length < 2 ^ (prefixWord ++ tailWord_6677228).sum := by decide
  have hdescent : baseEnd_6677228 < baseStart_6677228 := by decide
  rcases family_descends (prefixWord ++ tailWord_6677228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6677229 : List Nat := [1, 5, 1, 2, 1, 1, 1, 3, 4, 2, 2]
def baseStart_6677229 : Nat := 118140960795 + 6677229 * 2 ^ 59
def prefixEnd_6677229 : Nat := 4983230072969 + 3 ^ 40 * 6677229 * 2
def baseEnd_6677229 : Nat := 3428627917140361044529489

theorem tailTrace_6677229 : CollatzResearch.WordTrace tailWord_6677229 prefixEnd_6677229 3428627917140361044529489 := by
  unfold tailWord_6677229
  simp only [CollatzResearch.WordTrace]
  refine ⟨243538549126547187768026741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162359032751031458512017827 243538549126547187768026741)
  ·
    refine ⟨22831738980613798853252507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 243538549126547187768026741 22831738980613798853252507)
    ·
      refine ⟨34247608470920698279878761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22831738980613798853252507 34247608470920698279878761)
      ·
        refine ⟨25685706353190523709909071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34247608470920698279878761 25685706353190523709909071)
        ·
          refine ⟨38528559529785785564863607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25685706353190523709909071 38528559529785785564863607)
          ·
            refine ⟨57792839294678678347295411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38528559529785785564863607 57792839294678678347295411)
            ·
              refine ⟨86689258942018017520943117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57792839294678678347295411 86689258942018017520943117)
              ·
                refine ⟨32508472103256756570353669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 86689258942018017520943117 32508472103256756570353669)
                ·
                  refine ⟨6095338519360641856941313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 32508472103256756570353669 6095338519360641856941313)
                  ·
                    refine ⟨4571503889520481392705985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6095338519360641856941313 4571503889520481392705985)
                    ·
                      refine ⟨3428627917140361044529489, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4571503889520481392705985 3428627917140361044529489)
                      ·
                        rfl

theorem cell23_6677229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 1, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 1, 3, 4, 2, 2].length) (baseStart_6677229 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6677229 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6677229 prefixEnd_6677229 := by exact prefixLift 6677229
  have htrace : WordTrace (prefixWord ++ tailWord_6677229) baseStart_6677229 baseEnd_6677229 := by
    simpa [prefixWord, tailWord_6677229, baseEnd_6677229] using wordTrace_append hprefix tailTrace_6677229
  have hstable : (prefixWord ++ tailWord_6677229).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6677229).length < 2 ^ (prefixWord ++ tailWord_6677229).sum := by decide
  have hdescent : baseEnd_6677229 < baseStart_6677229 := by decide
  rcases family_descends (prefixWord ++ tailWord_6677229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6677245 : List Nat := [1, 4, 1, 1, 1, 1, 4, 1, 1, 5, 3]
def baseStart_6677245 : Nat := 118140960795 + 6677245 * 2 ^ 59
def prefixEnd_6677245 : Nat := 4983230072969 + 3 ^ 40 * 6677245 * 2
def baseEnd_6677245 : Nat := 3428636132830832981929415

theorem tailTrace_6677245 : CollatzResearch.WordTrace tailWord_6677245 prefixEnd_6677245 3428636132830832981929415 := by
  unfold tailWord_6677245
  simp only [CollatzResearch.WordTrace]
  refine ⟨243539132694489222500609189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162359421796326148333739459 243539132694489222500609189)
  ·
    refine ⟨45663587380216729218864223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 243539132694489222500609189 45663587380216729218864223)
    ·
      refine ⟨68495381070325093828296335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45663587380216729218864223 68495381070325093828296335)
      ·
        refine ⟨102743071605487640742444503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68495381070325093828296335 102743071605487640742444503)
        ·
          refine ⟨154114607408231461113666755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 102743071605487640742444503 154114607408231461113666755)
          ·
            refine ⟨231171911112347191670500133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 154114607408231461113666755 231171911112347191670500133)
            ·
              refine ⟨43344733333565098438218775, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 231171911112347191670500133 43344733333565098438218775)
              ·
                refine ⟨65017100000347647657328163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43344733333565098438218775 65017100000347647657328163)
                ·
                  refine ⟨97525650000521471485992245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 65017100000347647657328163 97525650000521471485992245)
                  ·
                    refine ⟨9143029687548887951811773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 97525650000521471485992245 9143029687548887951811773)
                    ·
                      refine ⟨3428636132830832981929415, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9143029687548887951811773 3428636132830832981929415)
                      ·
                        rfl

theorem cell23_6677245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 4, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 4, 1, 1, 5, 3].length) (baseStart_6677245 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6677245 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6677245 prefixEnd_6677245 := by exact prefixLift 6677245
  have htrace : WordTrace (prefixWord ++ tailWord_6677245) baseStart_6677245 baseEnd_6677245 := by
    simpa [prefixWord, tailWord_6677245, baseEnd_6677245] using wordTrace_append hprefix tailTrace_6677245
  have hstable : (prefixWord ++ tailWord_6677245).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6677245).length < 2 ^ (prefixWord ++ tailWord_6677245).sum := by decide
  have hdescent : baseEnd_6677245 < baseStart_6677245 := by decide
  rcases family_descends (prefixWord ++ tailWord_6677245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6677265 : List Nat := [1, 2, 2, 1, 1, 3, 3, 3, 2, 5]
def baseStart_6677265 : Nat := 118140960795 + 6677265 * 2 ^ 59
def prefixEnd_6677265 : Nat := 4983230072969 + 3 ^ 40 * 6677265 * 2
def baseEnd_6677265 : Nat := 1142882134147974301226441

theorem tailTrace_6677265 : CollatzResearch.WordTrace tailWord_6677265 prefixEnd_6677265 1142882134147974301226441 := by
  unfold tailWord_6677265
  simp only [CollatzResearch.WordTrace]
  refine ⟨243539862154416765916337249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162359908102944510610891499 243539862154416765916337249)
  ·
    refine ⟨182654896615812574437252937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 243539862154416765916337249 182654896615812574437252937)
    ·
      refine ⟨136991172461859430827939703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 182654896615812574437252937 136991172461859430827939703)
      ·
        refine ⟨205486758692789146241909555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 136991172461859430827939703 205486758692789146241909555)
        ·
          refine ⟨308230138039183719362864333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 205486758692789146241909555 308230138039183719362864333)
          ·
            refine ⟨115586301764693894761074125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 308230138039183719362864333 115586301764693894761074125)
            ·
              refine ⟨43344863161760210535402797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 115586301764693894761074125 43344863161760210535402797)
              ·
                refine ⟨16254323685660078950776049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 43344863161760210535402797 16254323685660078950776049)
                ·
                  refine ⟨12190742764245059213082037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16254323685660078950776049 12190742764245059213082037)
                  ·
                    refine ⟨1142882134147974301226441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12190742764245059213082037 1142882134147974301226441)
                    ·
                      rfl

theorem cell23_6677265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 5].length) (baseStart_6677265 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6677265 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6677265 prefixEnd_6677265 := by exact prefixLift 6677265
  have htrace : WordTrace (prefixWord ++ tailWord_6677265) baseStart_6677265 baseEnd_6677265 := by
    simpa [prefixWord, tailWord_6677265, baseEnd_6677265] using wordTrace_append hprefix tailTrace_6677265
  have hstable : (prefixWord ++ tailWord_6677265).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6677265).length < 2 ^ (prefixWord ++ tailWord_6677265).sum := by decide
  have hdescent : baseEnd_6677265 < baseStart_6677265 := by decide
  rcases family_descends (prefixWord ++ tailWord_6677265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6677282 : List Nat := [3, 3, 1, 1, 2, 2, 2, 2, 2, 5]
def baseStart_6677282 : Nat := 118140960795 + 6677282 * 2 ^ 59
def prefixEnd_6677282 : Nat := 4983230072969 + 3 ^ 40 * 6677282 * 2
def baseEnd_6677282 : Nat := 1142885043871683112388915

theorem tailTrace_6677282 : CollatzResearch.WordTrace tailWord_6677282 prefixEnd_6677282 1142885043871683112388915 := by
  unfold tailWord_6677282
  simp only [CollatzResearch.WordTrace]
  refine ⟨60885120548838794454926525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 162360321463570118546470733 60885120548838794454926525)
  ·
    refine ⟨22831920205814547920597447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 60885120548838794454926525 22831920205814547920597447)
    ·
      refine ⟨34247880308721821880896171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22831920205814547920597447 34247880308721821880896171)
      ·
        refine ⟨51371820463082732821344257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34247880308721821880896171 51371820463082732821344257)
        ·
          refine ⟨38528865347312049616008193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51371820463082732821344257 38528865347312049616008193)
          ·
            refine ⟨28896649010484037212006145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38528865347312049616008193 28896649010484037212006145)
            ·
              refine ⟨21672486757863027909004609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28896649010484037212006145 21672486757863027909004609)
              ·
                refine ⟨16254365068397270931753457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21672486757863027909004609 16254365068397270931753457)
                ·
                  refine ⟨12190773801297953198815093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16254365068397270931753457 12190773801297953198815093)
                  ·
                    refine ⟨1142885043871683112388915, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12190773801297953198815093 1142885043871683112388915)
                    ·
                      rfl

theorem cell23_6677282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 2, 2, 2, 5].length) (baseStart_6677282 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6677282 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6677282 prefixEnd_6677282 := by exact prefixLift 6677282
  have htrace : WordTrace (prefixWord ++ tailWord_6677282) baseStart_6677282 baseEnd_6677282 := by
    simpa [prefixWord, tailWord_6677282, baseEnd_6677282] using wordTrace_append hprefix tailTrace_6677282
  have hstable : (prefixWord ++ tailWord_6677282).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6677282).length < 2 ^ (prefixWord ++ tailWord_6677282).sum := by decide
  have hdescent : baseEnd_6677282 < baseStart_6677282 := by decide
  rcases family_descends (prefixWord ++ tailWord_6677282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6677322 : List Nat := [3, 1, 2, 1, 1, 1, 2, 5, 2, 2, 3]
def baseStart_6677322 : Nat := 118140960795 + 6677322 * 2 ^ 59
def prefixEnd_6677322 : Nat := 4983230072969 + 3 ^ 40 * 6677322 * 2
def baseEnd_6677322 : Nat := 3428675670841229180666561

theorem tailTrace_6677322 : CollatzResearch.WordTrace tailWord_6677322 prefixEnd_6677322 3428675670841229180666561 := by
  unfold tailWord_6677322
  simp only [CollatzResearch.WordTrace]
  refine ⟨60885485278802566162790555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 162361294076806843100774813 60885485278802566162790555)
  ·
    refine ⟨91328227918203849244185833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60885485278802566162790555 91328227918203849244185833)
    ·
      refine ⟨68496170938652886933139375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 91328227918203849244185833 68496170938652886933139375)
      ·
        refine ⟨102744256407979330399709063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68496170938652886933139375 102744256407979330399709063)
        ·
          refine ⟨154116384611968995599563595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 102744256407979330399709063 154116384611968995599563595)
          ·
            refine ⟨231174576917953493399345393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 154116384611968995599563595 231174576917953493399345393)
            ·
              refine ⟨173380932688465120049509045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 231174576917953493399345393 173380932688465120049509045)
              ·
                refine ⟨16254462439543605004641473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 173380932688465120049509045 16254462439543605004641473)
                ·
                  refine ⟨12190846829657703753481105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16254462439543605004641473 12190846829657703753481105)
                  ·
                    refine ⟨9143135122243277815110829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12190846829657703753481105 9143135122243277815110829)
                    ·
                      refine ⟨3428675670841229180666561, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9143135122243277815110829 3428675670841229180666561)
                      ·
                        rfl

theorem cell23_6677322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 2, 5, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 2, 5, 2, 2, 3].length) (baseStart_6677322 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6677322 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6677322 prefixEnd_6677322 := by exact prefixLift 6677322
  have htrace : WordTrace (prefixWord ++ tailWord_6677322) baseStart_6677322 baseEnd_6677322 := by
    simpa [prefixWord, tailWord_6677322, baseEnd_6677322] using wordTrace_append hprefix tailTrace_6677322
  have hstable : (prefixWord ++ tailWord_6677322).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6677322).length < 2 ^ (prefixWord ++ tailWord_6677322).sum := by decide
  have hdescent : baseEnd_6677322 < baseStart_6677322 := by decide
  rcases family_descends (prefixWord ++ tailWord_6677322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6677346 : List Nat := [3, 3, 2, 1, 3, 1, 2, 1, 3, 4]
def baseStart_6677346 : Nat := 118140960795 + 6677346 * 2 ^ 59
def prefixEnd_6677346 : Nat := 4983230072969 + 3 ^ 40 * 6677346 * 2
def baseEnd_6677346 : Nat := 1142895998125645695588817

theorem tailTrace_6677346 : CollatzResearch.WordTrace tailWord_6677346 prefixEnd_6677346 1142895998125645695588817 := by
  unfold tailWord_6677346
  simp only [CollatzResearch.WordTrace]
  refine ⟨60885704116780829187508973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 162361877644748877833357261 60885704116780829187508973)
  ·
    refine ⟨22832139043792810945315865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 60885704116780829187508973 22832139043792810945315865)
    ·
      refine ⟨17124104282844608208986899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22832139043792810945315865 17124104282844608208986899)
      ·
        refine ⟨25686156424266912313480349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17124104282844608208986899 25686156424266912313480349)
        ·
          refine ⟨9632308659100092117555131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25686156424266912313480349 9632308659100092117555131)
          ·
            refine ⟨14448462988650138176332697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9632308659100092117555131 14448462988650138176332697)
            ·
              refine ⟨10836347241487603632249523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14448462988650138176332697 10836347241487603632249523)
              ·
                refine ⟨16254520862231405448374285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10836347241487603632249523 16254520862231405448374285)
                ·
                  refine ⟨6095445323336777043140357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16254520862231405448374285 6095445323336777043140357)
                  ·
                    refine ⟨1142895998125645695588817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6095445323336777043140357 1142895998125645695588817)
                    ·
                      rfl

theorem cell23_6677346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 3, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 3, 1, 2, 1, 3, 4].length) (baseStart_6677346 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6677346 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6677346 prefixEnd_6677346 := by exact prefixLift 6677346
  have htrace : WordTrace (prefixWord ++ tailWord_6677346) baseStart_6677346 baseEnd_6677346 := by
    simpa [prefixWord, tailWord_6677346, baseEnd_6677346] using wordTrace_append hprefix tailTrace_6677346
  have hstable : (prefixWord ++ tailWord_6677346).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6677346).length < 2 ^ (prefixWord ++ tailWord_6677346).sum := by decide
  have hdescent : baseEnd_6677346 < baseStart_6677346 := by decide
  rcases family_descends (prefixWord ++ tailWord_6677346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6677355 : List Nat := [1, 1, 1, 1, 2, 2, 4, 1, 5, 5]
def baseStart_6677355 : Nat := 118140960795 + 6677355 * 2 ^ 59
def prefixEnd_6677355 : Nat := 4983230072969 + 3 ^ 40 * 6677355 * 2
def baseEnd_6677355 : Nat := 1142897538567609183851303

theorem tailTrace_6677355 : CollatzResearch.WordTrace tailWord_6677355 prefixEnd_6677355 1142897538567609183851303 := by
  unfold tailWord_6677355
  simp only [CollatzResearch.WordTrace]
  refine ⟨243543144724090711287113519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162362096482727140858075679 243543144724090711287113519)
  ·
    refine ⟨365314717086136066930670279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 243543144724090711287113519 365314717086136066930670279)
    ·
      refine ⟨547972075629204100396005419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 365314717086136066930670279 547972075629204100396005419)
      ·
        refine ⟨821958113443806150594008129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 547972075629204100396005419 821958113443806150594008129)
        ·
          refine ⟨616468585082854612945506097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 821958113443806150594008129 616468585082854612945506097)
          ·
            refine ⟨462351438812140959709129573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 616468585082854612945506097 462351438812140959709129573)
            ·
              refine ⟨86690894777276429945461795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 462351438812140959709129573 86690894777276429945461795)
              ·
                refine ⟨130036342165914644918192693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 86690894777276429945461795 130036342165914644918192693)
                ·
                  refine ⟨12190907078054497961080565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 130036342165914644918192693 12190907078054497961080565)
                  ·
                    refine ⟨1142897538567609183851303, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12190907078054497961080565 1142897538567609183851303)
                    ·
                      rfl

theorem cell23_6677355_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 4, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 4, 1, 5, 5].length) (baseStart_6677355 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6677355 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6677355 prefixEnd_6677355 := by exact prefixLift 6677355
  have htrace : WordTrace (prefixWord ++ tailWord_6677355) baseStart_6677355 baseEnd_6677355 := by
    simpa [prefixWord, tailWord_6677355, baseEnd_6677355] using wordTrace_append hprefix tailTrace_6677355
  have hstable : (prefixWord ++ tailWord_6677355).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6677355).length < 2 ^ (prefixWord ++ tailWord_6677355).sum := by decide
  have hdescent : baseEnd_6677355 < baseStart_6677355 := by decide
  rcases family_descends (prefixWord ++ tailWord_6677355) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6677369 : List Nat := [1, 2, 1, 3, 2, 3, 2, 2, 3, 1, 3]
def baseStart_6677369 : Nat := 118140960795 + 6677369 * 2 ^ 59
def prefixEnd_6677369 : Nat := 4983230072969 + 3 ^ 40 * 6677369 * 2
def baseEnd_6677369 : Nat := 3428699804431990496778845

theorem tailTrace_6677369 : CollatzResearch.WordTrace tailWord_6677369 prefixEnd_6677369 3428699804431990496778845 := by
  unfold tailWord_6677369
  simp only [CollatzResearch.WordTrace]
  refine ⟨243543655346039991678123161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162362436897359994452082107 243543655346039991678123161)
  ·
    refine ⟨182657741509529993758592371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 243543655346039991678123161 182657741509529993758592371)
    ·
      refine ⟨273986612264294990637888557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 182657741509529993758592371 273986612264294990637888557)
      ·
        refine ⟨102744979599110621489208209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 273986612264294990637888557 102744979599110621489208209)
        ·
          refine ⟨77058734699332966116906157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 102744979599110621489208209 77058734699332966116906157)
          ·
            refine ⟨28897025512249862293839809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 77058734699332966116906157 28897025512249862293839809)
            ·
              refine ⟨21672769134187396720379857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28897025512249862293839809 21672769134187396720379857)
              ·
                refine ⟨16254576850640547540284893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21672769134187396720379857 16254576850640547540284893)
                ·
                  refine ⟨6095466318990205327606835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16254576850640547540284893 6095466318990205327606835)
                  ·
                    refine ⟨9143199478485307991410253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6095466318990205327606835 9143199478485307991410253)
                    ·
                      refine ⟨3428699804431990496778845, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9143199478485307991410253 3428699804431990496778845)
                      ·
                        rfl

theorem cell23_6677369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 2, 2, 3, 1, 3].length) (baseStart_6677369 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6677369 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6677369 prefixEnd_6677369 := by exact prefixLift 6677369
  have htrace : WordTrace (prefixWord ++ tailWord_6677369) baseStart_6677369 baseEnd_6677369 := by
    simpa [prefixWord, tailWord_6677369, baseEnd_6677369] using wordTrace_append hprefix tailTrace_6677369
  have hstable : (prefixWord ++ tailWord_6677369).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6677369).length < 2 ^ (prefixWord ++ tailWord_6677369).sum := by decide
  have hdescent : baseEnd_6677369 < baseStart_6677369 := by decide
  rcases family_descends (prefixWord ++ tailWord_6677369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6677379 : List Nat := [1, 1, 1, 3, 4, 1, 2, 3, 2, 3, 2]
def baseStart_6677379 : Nat := 118140960795 + 6677379 * 2 ^ 59
def prefixEnd_6677379 : Nat := 4983230072969 + 3 ^ 40 * 6677379 * 2
def baseEnd_6677379 : Nat := 3428704939238535457653799

theorem tailTrace_6677379 : CollatzResearch.WordTrace tailWord_6677379 prefixEnd_6677379 3428704939238535457653799 := by
  unfold tailWord_6677379
  simp only [CollatzResearch.WordTrace]
  refine ⟨243544020076003763385987191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162362680050669175590658127 243544020076003763385987191)
  ·
    refine ⟨365316030114005645078980787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 243544020076003763385987191 365316030114005645078980787)
    ·
      refine ⟨547974045171008467618471181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 365316030114005645078980787 547974045171008467618471181)
      ·
        refine ⟨205490266939128175356926693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 547974045171008467618471181 205490266939128175356926693)
        ·
          refine ⟨38529425051086532879423755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 205490266939128175356926693 38529425051086532879423755)
          ·
            refine ⟨57794137576629799319135633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38529425051086532879423755 57794137576629799319135633)
            ·
              refine ⟨43345603182472349489351725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 57794137576629799319135633 43345603182472349489351725)
              ·
                refine ⟨16254601193427131058506897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 43345603182472349489351725 16254601193427131058506897)
                ·
                  refine ⟨12190950895070348293880173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16254601193427131058506897 12190950895070348293880173)
                  ·
                    refine ⟨4571606585651380610205065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12190950895070348293880173 4571606585651380610205065)
                    ·
                      refine ⟨3428704939238535457653799, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4571606585651380610205065 3428704939238535457653799)
                      ·
                        rfl

theorem cell23_6677379_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 2, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 2, 3, 2, 3, 2].length) (baseStart_6677379 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6677379 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6677379 prefixEnd_6677379 := by exact prefixLift 6677379
  have htrace : WordTrace (prefixWord ++ tailWord_6677379) baseStart_6677379 baseEnd_6677379 := by
    simpa [prefixWord, tailWord_6677379, baseEnd_6677379] using wordTrace_append hprefix tailTrace_6677379
  have hstable : (prefixWord ++ tailWord_6677379).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6677379).length < 2 ^ (prefixWord ++ tailWord_6677379).sum := by decide
  have hdescent : baseEnd_6677379 < baseStart_6677379 := by decide
  rcases family_descends (prefixWord ++ tailWord_6677379) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6677392 : List Nat := [2, 1, 1, 1, 1, 1, 2, 2, 4, 6, 2]
def baseStart_6677392 : Nat := 118140960795 + 6677392 * 2 ^ 59
def prefixEnd_6677392 : Nat := 4983230072969 + 3 ^ 40 * 6677392 * 2
def baseEnd_6677392 : Nat := 3428711614487043906791239

theorem tailTrace_6677392 : CollatzResearch.WordTrace tailWord_6677392 prefixEnd_6677392 3428711614487043906791239 := by
  unfold tailWord_6677392
  simp only [CollatzResearch.WordTrace]
  refine ⟨121772247112478333303105215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 162362996149971111070806953 121772247112478333303105215)
  ·
    refine ⟨182658370668717499954657823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121772247112478333303105215 182658370668717499954657823)
    ·
      refine ⟨273987556003076249931986735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 182658370668717499954657823 273987556003076249931986735)
      ·
        refine ⟨410981334004614374897980103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 273987556003076249931986735 410981334004614374897980103)
        ·
          refine ⟨616472001006921562346970155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 410981334004614374897980103 616472001006921562346970155)
          ·
            refine ⟨924708001510382343520455233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 616472001006921562346970155 924708001510382343520455233)
            ·
              refine ⟨693531001132786757640341425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 924708001510382343520455233 693531001132786757640341425)
              ·
                refine ⟨520148250849590068230256069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 693531001132786757640341425 520148250849590068230256069)
                ·
                  refine ⟨97527797034298137793173013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 520148250849590068230256069 97527797034298137793173013)
                  ·
                    refine ⟨4571615485982725209054985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 97527797034298137793173013 4571615485982725209054985)
                    ·
                      refine ⟨3428711614487043906791239, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4571615485982725209054985 3428711614487043906791239)
                      ·
                        rfl

theorem cell23_6677392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 2, 4, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 2, 4, 6, 2].length) (baseStart_6677392 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6677392 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6677392 prefixEnd_6677392 := by exact prefixLift 6677392
  have htrace : WordTrace (prefixWord ++ tailWord_6677392) baseStart_6677392 baseEnd_6677392 := by
    simpa [prefixWord, tailWord_6677392, baseEnd_6677392] using wordTrace_append hprefix tailTrace_6677392
  have hstable : (prefixWord ++ tailWord_6677392).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6677392).length < 2 ^ (prefixWord ++ tailWord_6677392).sum := by decide
  have hdescent : baseEnd_6677392 < baseStart_6677392 := by decide
  rcases family_descends (prefixWord ++ tailWord_6677392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6677396 : List Nat := [2, 4, 2, 1, 1, 1, 3, 2, 2, 3, 2]
def baseStart_6677396 : Nat := 118140960795 + 6677396 * 2 ^ 59
def prefixEnd_6677396 : Nat := 4983230072969 + 3 ^ 40 * 6677396 * 2
def baseEnd_6677396 : Nat := 3428713668409661891141221

theorem tailTrace_6677396 : CollatzResearch.WordTrace tailWord_6677396 prefixEnd_6677396 3428713668409661891141221 := by
  unfold tailWord_6677396
  simp only [CollatzResearch.WordTrace]
  refine ⟨121772320058471087644678021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 162363093411294783526237361 121772320058471087644678021)
  ·
    refine ⟨22832310010963328933377129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 121772320058471087644678021 22832310010963328933377129)
    ·
      refine ⟨17124232508222496700032847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22832310010963328933377129 17124232508222496700032847)
      ·
        refine ⟨25686348762333745050049271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17124232508222496700032847 25686348762333745050049271)
        ·
          refine ⟨38529523143500617575073907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25686348762333745050049271 38529523143500617575073907)
          ·
            refine ⟨57794284715250926362610861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38529523143500617575073907 57794284715250926362610861)
            ·
              refine ⟨21672856768219097385979073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 57794284715250926362610861 21672856768219097385979073)
              ·
                refine ⟨16254642576164323039484305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21672856768219097385979073 16254642576164323039484305)
                ·
                  refine ⟨12190981932123242279613229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16254642576164323039484305 12190981932123242279613229)
                  ·
                    refine ⟨4571618224546215854854961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12190981932123242279613229 4571618224546215854854961)
                    ·
                      refine ⟨3428713668409661891141221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4571618224546215854854961 3428713668409661891141221)
                      ·
                        rfl

theorem cell23_6677396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 3, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 3, 2, 2, 3, 2].length) (baseStart_6677396 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6677396 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6677396 prefixEnd_6677396 := by exact prefixLift 6677396
  have htrace : WordTrace (prefixWord ++ tailWord_6677396) baseStart_6677396 baseEnd_6677396 := by
    simpa [prefixWord, tailWord_6677396, baseEnd_6677396] using wordTrace_append hprefix tailTrace_6677396
  have hstable : (prefixWord ++ tailWord_6677396).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6677396).length < 2 ^ (prefixWord ++ tailWord_6677396).sum := by decide
  have hdescent : baseEnd_6677396 < baseStart_6677396 := by decide
  rcases family_descends (prefixWord ++ tailWord_6677396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6677412 : List Nat := [2, 3, 1, 2, 1, 2, 1, 4, 1, 1, 5]
def baseStart_6677412 : Nat := 118140960795 + 6677412 * 2 ^ 59
def prefixEnd_6677412 : Nat := 4983230072969 + 3 ^ 40 * 6677412 * 2
def baseEnd_6677412 : Nat := 3428721884100133828541147

theorem tailTrace_6677412 : CollatzResearch.WordTrace tailWord_6677412 prefixEnd_6677412 3428721884100133828541147 := by
  unfold tailWord_6677412
  simp only [CollatzResearch.WordTrace]
  refine ⟨121772611842442105010969245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 162363482456589473347958993 121772611842442105010969245)
  ·
    refine ⟨45664729440915789379113467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 121772611842442105010969245 45664729440915789379113467)
    ·
      refine ⟨68497094161373684068670201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45664729440915789379113467 68497094161373684068670201)
      ·
        refine ⟨51372820621030263051502651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68497094161373684068670201 51372820621030263051502651)
        ·
          refine ⟨77059230931545394577253977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51372820621030263051502651 77059230931545394577253977)
          ·
            refine ⟨57794423198659045932940483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 77059230931545394577253977 57794423198659045932940483)
            ·
              refine ⟨86691634797988568899410725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57794423198659045932940483 86691634797988568899410725)
              ·
                refine ⟨16254681524622856668639511, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 86691634797988568899410725 16254681524622856668639511)
                ·
                  refine ⟨24382022286934285002959267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16254681524622856668639511 24382022286934285002959267)
                  ·
                    refine ⟨36573033430401427504438901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24382022286934285002959267 36573033430401427504438901)
                    ·
                      refine ⟨3428721884100133828541147, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36573033430401427504438901 3428721884100133828541147)
                      ·
                        rfl

theorem cell23_6677412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 1, 4, 1, 1, 5].length) (baseStart_6677412 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6677412 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6677412 prefixEnd_6677412 := by exact prefixLift 6677412
  have htrace : WordTrace (prefixWord ++ tailWord_6677412) baseStart_6677412 baseEnd_6677412 := by
    simpa [prefixWord, tailWord_6677412, baseEnd_6677412] using wordTrace_append hprefix tailTrace_6677412
  have hstable : (prefixWord ++ tailWord_6677412).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6677412).length < 2 ^ (prefixWord ++ tailWord_6677412).sum := by decide
  have hdescent : baseEnd_6677412 < baseStart_6677412 := by decide
  rcases family_descends (prefixWord ++ tailWord_6677412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6677429 : List Nat := [1, 3, 3, 2, 1, 1, 3, 1, 3, 2, 3]
def baseStart_6677429 : Nat := 118140960795 + 6677429 * 2 ^ 59
def prefixEnd_6677429 : Nat := 4983230072969 + 3 ^ 40 * 6677429 * 2
def baseEnd_6677429 : Nat := 3428730613271260262028569

theorem tailTrace_6677429 : CollatzResearch.WordTrace tailWord_6677429 prefixEnd_6677429 3428730613271260262028569 := by
  unfold tailWord_6677429
  simp only [CollatzResearch.WordTrace]
  refine ⟨243545843725822621925307341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162363895817215081283538227 243545843725822621925307341)
  ·
    refine ⟨91329691397183483221990253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 243545843725822621925307341 91329691397183483221990253)
    ·
      refine ⟨34248634273943806208246345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 91329691397183483221990253 34248634273943806208246345)
      ·
        refine ⟨25686475705457854656184759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34248634273943806208246345 25686475705457854656184759)
        ·
          refine ⟨38529713558186781984277139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25686475705457854656184759 38529713558186781984277139)
          ·
            refine ⟨57794570337280172976415709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38529713558186781984277139 57794570337280172976415709)
            ·
              refine ⟨21672963876480064866155891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 57794570337280172976415709 21672963876480064866155891)
              ·
                refine ⟨32509445814720097299233837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21672963876480064866155891 32509445814720097299233837)
                ·
                  refine ⟨12191042180520036487212689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32509445814720097299233837 12191042180520036487212689)
                  ·
                    refine ⟨9143281635390027365409517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12191042180520036487212689 9143281635390027365409517)
                    ·
                      refine ⟨3428730613271260262028569, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9143281635390027365409517 3428730613271260262028569)
                      ·
                        rfl

theorem cell23_6677429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 3, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 3, 1, 3, 2, 3].length) (baseStart_6677429 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6677429 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6677429 prefixEnd_6677429 := by exact prefixLift 6677429
  have htrace : WordTrace (prefixWord ++ tailWord_6677429) baseStart_6677429 baseEnd_6677429 := by
    simpa [prefixWord, tailWord_6677429, baseEnd_6677429] using wordTrace_append hprefix tailTrace_6677429
  have hstable : (prefixWord ++ tailWord_6677429).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6677429).length < 2 ^ (prefixWord ++ tailWord_6677429).sum := by decide
  have hdescent : baseEnd_6677429 < baseStart_6677429 := by decide
  rcases family_descends (prefixWord ++ tailWord_6677429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6677435 : List Nat := [1, 1, 1, 1, 1, 2, 2, 2, 4, 2, 6]
def baseStart_6677435 : Nat := 118140960795 + 6677435 * 2 ^ 59
def prefixEnd_6677435 : Nat := 4983230072969 + 3 ^ 40 * 6677435 * 2
def baseEnd_6677435 : Nat := 3428733694155187238553541

theorem tailTrace_6677435 : CollatzResearch.WordTrace tailWord_6677435 prefixEnd_6677435 3428733694155187238553541 := by
  unfold tailWord_6677435
  simp only [CollatzResearch.WordTrace]
  refine ⟨243546062563800884950025759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162364041709200589966683839 243546062563800884950025759)
  ·
    refine ⟨365319093845701327425038639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 243546062563800884950025759 365319093845701327425038639)
    ·
      refine ⟨547978640768551991137557959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 365319093845701327425038639 547978640768551991137557959)
      ·
        refine ⟨821967961152827986706336939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 547978640768551991137557959 821967961152827986706336939)
        ·
          refine ⟨1232951941729241980059505409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 821967961152827986706336939 1232951941729241980059505409)
          ·
            refine ⟨924713956296931485044629057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1232951941729241980059505409 924713956296931485044629057)
            ·
              refine ⟨693535467222698613783471793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 924713956296931485044629057 693535467222698613783471793)
              ·
                refine ⟨520151600417023960337603845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 693535467222698613783471793 520151600417023960337603845)
                ·
                  refine ⟨97528425078191992563300721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 520151600417023960337603845 97528425078191992563300721)
                  ·
                    refine ⟨73146318808643994422475541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 97528425078191992563300721 73146318808643994422475541)
                    ·
                      refine ⟨3428733694155187238553541, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 73146318808643994422475541 3428733694155187238553541)
                      ·
                        rfl

theorem cell23_6677435_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 4, 2, 6].length) (baseStart_6677435 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6677435 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6677435 prefixEnd_6677435 := by exact prefixLift 6677435
  have htrace : WordTrace (prefixWord ++ tailWord_6677435) baseStart_6677435 baseEnd_6677435 := by
    simpa [prefixWord, tailWord_6677435, baseEnd_6677435] using wordTrace_append hprefix tailTrace_6677435
  have hstable : (prefixWord ++ tailWord_6677435).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6677435).length < 2 ^ (prefixWord ++ tailWord_6677435).sum := by decide
  have hdescent : baseEnd_6677435 < baseStart_6677435 := by decide
  rcases family_descends (prefixWord ++ tailWord_6677435) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6677460 : List Nat := [2, 4, 1, 2, 1, 3, 1, 4, 1, 2, 2]
def baseStart_6677460 : Nat := 118140960795 + 6677460 * 2 ^ 59
def prefixEnd_6677460 : Nat := 4983230072969 + 3 ^ 40 * 6677460 * 2
def baseEnd_6677460 : Nat := 3428746531171549640740927

theorem tailTrace_6677460 : CollatzResearch.WordTrace tailWord_6677460 prefixEnd_6677460 3428746531171549640740927 := by
  unfold tailWord_6677460
  simp only [CollatzResearch.WordTrace]
  refine ⟨121773487194355157109842917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 162364649592473542813123889 121773487194355157109842917)
  ·
    refine ⟨22832528848941591958095547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 121773487194355157109842917 22832528848941591958095547)
    ·
      refine ⟨34248793273412387937143321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22832528848941591958095547 34248793273412387937143321)
      ·
        refine ⟨25686594955059290952857491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34248793273412387937143321 25686594955059290952857491)
        ·
          refine ⟨38529892432588936429286237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25686594955059290952857491 38529892432588936429286237)
          ·
            refine ⟨14448709662220851160982339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38529892432588936429286237 14448709662220851160982339)
            ·
              refine ⟨21673064493331276741473509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14448709662220851160982339 21673064493331276741473509)
              ·
                refine ⟨4063699592499614389026283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21673064493331276741473509 4063699592499614389026283)
                ·
                  refine ⟨6095549388749421583539425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4063699592499614389026283 6095549388749421583539425)
                  ·
                    refine ⟨4571662041562066187654569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6095549388749421583539425 4571662041562066187654569)
                    ·
                      refine ⟨3428746531171549640740927, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4571662041562066187654569 3428746531171549640740927)
                      ·
                        rfl

theorem cell23_6677460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 3, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 3, 1, 4, 1, 2, 2].length) (baseStart_6677460 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6677460 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6677460 prefixEnd_6677460 := by exact prefixLift 6677460
  have htrace : WordTrace (prefixWord ++ tailWord_6677460) baseStart_6677460 baseEnd_6677460 := by
    simpa [prefixWord, tailWord_6677460, baseEnd_6677460] using wordTrace_append hprefix tailTrace_6677460
  have hstable : (prefixWord ++ tailWord_6677460).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6677460).length < 2 ^ (prefixWord ++ tailWord_6677460).sum := by decide
  have hdescent : baseEnd_6677460 < baseStart_6677460 := by decide
  rcases family_descends (prefixWord ++ tailWord_6677460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6677552 : List Nat := [2, 1, 1, 1, 2, 4, 1, 3, 1, 7]
def baseStart_6677552 : Nat := 118140960795 + 6677552 * 2 ^ 59
def prefixEnd_6677552 : Nat := 4983230072969 + 3 ^ 40 * 6677552 * 2
def baseEnd_6677552 : Nat := 1142931257130587760263501

theorem tailTrace_6677552 : CollatzResearch.WordTrace tailWord_6677552 prefixEnd_6677552 1142931257130587760263501 := by
  unfold tailWord_6677552
  simp only [CollatzResearch.WordTrace]
  refine ⟨121775164952188506966017455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 162366886602918009288023273 121775164952188506966017455)
  ·
    refine ⟨182662747428282760449026183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121775164952188506966017455 182662747428282760449026183)
    ·
      refine ⟨273994121142424140673539275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 182662747428282760449026183 273994121142424140673539275)
      ·
        refine ⟨410991181713636211010308913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 273994121142424140673539275 410991181713636211010308913)
        ·
          refine ⟨308243386285227158257731685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 410991181713636211010308913 308243386285227158257731685)
          ·
            refine ⟨57795634928480092173324691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 308243386285227158257731685 57795634928480092173324691)
            ·
              refine ⟨86693452392720138259987037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57795634928480092173324691 86693452392720138259987037)
              ·
                refine ⟨32510044647270051847495139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 86693452392720138259987037 32510044647270051847495139)
                ·
                  refine ⟨48765066970905077771242709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32510044647270051847495139 48765066970905077771242709)
                  ·
                    refine ⟨1142931257130587760263501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 48765066970905077771242709 1142931257130587760263501)
                    ·
                      rfl

theorem cell23_6677552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 1, 3, 1, 7].length) (baseStart_6677552 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6677552 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6677552 prefixEnd_6677552 := by exact prefixLift 6677552
  have htrace : WordTrace (prefixWord ++ tailWord_6677552) baseStart_6677552 baseEnd_6677552 := by
    simpa [prefixWord, tailWord_6677552, baseEnd_6677552] using wordTrace_append hprefix tailTrace_6677552
  have hstable : (prefixWord ++ tailWord_6677552).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6677552).length < 2 ^ (prefixWord ++ tailWord_6677552).sum := by decide
  have hdescent : baseEnd_6677552 < baseStart_6677552 := by decide
  rcases family_descends (prefixWord ++ tailWord_6677552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6677559 : List Nat := [1, 1, 3, 1, 2, 2, 1, 2, 1, 7, 2]
def baseStart_6677559 : Nat := 118140960795 + 6677559 * 2 ^ 59
def prefixEnd_6677559 : Nat := 4983230072969 + 3 ^ 40 * 6677559 * 2
def baseEnd_6677559 : Nat := 3428797365756344753402971

theorem tailTrace_6677559 : CollatzResearch.WordTrace tailWord_6677559 prefixEnd_6677559 3428797365756344753402971 := by
  unfold tailWord_6677559
  simp only [CollatzResearch.WordTrace]
  refine ⟨243550585215351654127539731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162367056810234436085026487 243550585215351654127539731)
  ·
    refine ⟨365325877823027481191309597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 243550585215351654127539731 365325877823027481191309597)
    ·
      refine ⟨136997204183635305446741099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 365325877823027481191309597 136997204183635305446741099)
      ·
        refine ⟨205495806275452958170111649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 136997204183635305446741099 205495806275452958170111649)
        ·
          refine ⟨154121854706589718627583737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 205495806275452958170111649 154121854706589718627583737)
          ·
            refine ⟨115591391029942288970687803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 154121854706589718627583737 115591391029942288970687803)
            ·
              refine ⟨173387086544913433456031705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 115591391029942288970687803 173387086544913433456031705)
              ·
                refine ⟨130040314908685075092023779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 173387086544913433456031705 130040314908685075092023779)
                ·
                  refine ⟨195060472363027612638035669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 130040314908685075092023779 195060472363027612638035669)
                  ·
                    refine ⟨4571729821008459671203961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 195060472363027612638035669 4571729821008459671203961)
                    ·
                      refine ⟨3428797365756344753402971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4571729821008459671203961 3428797365756344753402971)
                      ·
                        rfl

theorem cell23_6677559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 1, 2, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 1, 2, 1, 7, 2].length) (baseStart_6677559 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6677559 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6677559 prefixEnd_6677559 := by exact prefixLift 6677559
  have htrace : WordTrace (prefixWord ++ tailWord_6677559) baseStart_6677559 baseEnd_6677559 := by
    simpa [prefixWord, tailWord_6677559, baseEnd_6677559] using wordTrace_append hprefix tailTrace_6677559
  have hstable : (prefixWord ++ tailWord_6677559).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6677559).length < 2 ^ (prefixWord ++ tailWord_6677559).sum := by decide
  have hdescent : baseEnd_6677559 < baseStart_6677559 := by decide
  rcases family_descends (prefixWord ++ tailWord_6677559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6677589 : List Nat := [1, 3, 2, 2, 1, 2, 1, 2, 4, 1, 4]
def baseStart_6677589 : Nat := 118140960795 + 6677589 * 2 ^ 59
def prefixEnd_6677589 : Nat := 4983230072969 + 3 ^ 40 * 6677589 * 2
def baseEnd_6677589 : Nat := 3428812770175979636027833

theorem tailTrace_6677589 : CollatzResearch.WordTrace tailWord_6677589 prefixEnd_6677589 3428812770175979636027833 := by
  unfold tailWord_6677589
  simp only [CollatzResearch.WordTrace]
  refine ⟨243551679405242969251131821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162367786270161979500754547 243551679405242969251131821)
  ·
    refine ⟨91331879776966113469174433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 243551679405242969251131821 91331879776966113469174433)
    ·
      refine ⟨68498909832724585101880825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 91331879776966113469174433 68498909832724585101880825)
      ·
        refine ⟨51374182374543438826410619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68498909832724585101880825 51374182374543438826410619)
        ·
          refine ⟨77061273561815158239615929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51374182374543438826410619 77061273561815158239615929)
          ·
            refine ⟨57795955171361368679711947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 77061273561815158239615929 57795955171361368679711947)
            ·
              refine ⟨86693932757042053019567921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57795955171361368679711947 86693932757042053019567921)
              ·
                refine ⟨65020449567781539764675941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 86693932757042053019567921 65020449567781539764675941)
                ·
                  refine ⟨12191334293959038705876739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 65020449567781539764675941 12191334293959038705876739)
                  ·
                    refine ⟨18287001440938558058815109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12191334293959038705876739 18287001440938558058815109)
                    ·
                      refine ⟨3428812770175979636027833, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18287001440938558058815109 3428812770175979636027833)
                      ·
                        rfl

theorem cell23_6677589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 1, 2, 4, 1, 4].length) (baseStart_6677589 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6677589 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6677589 prefixEnd_6677589 := by exact prefixLift 6677589
  have htrace : WordTrace (prefixWord ++ tailWord_6677589) baseStart_6677589 baseEnd_6677589 := by
    simpa [prefixWord, tailWord_6677589, baseEnd_6677589] using wordTrace_append hprefix tailTrace_6677589
  have hstable : (prefixWord ++ tailWord_6677589).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6677589).length < 2 ^ (prefixWord ++ tailWord_6677589).sum := by decide
  have hdescent : baseEnd_6677589 < baseStart_6677589 := by decide
  rcases family_descends (prefixWord ++ tailWord_6677589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6677599 : List Nat := [1, 1, 2, 3, 1, 1, 4, 1, 5, 4]
def baseStart_6677599 : Nat := 118140960795 + 6677599 * 2 ^ 59
def prefixEnd_6677599 : Nat := 4983230072969 + 3 ^ 40 * 6677599 * 2
def baseEnd_6677599 : Nat := 1142939301660841532300929

theorem tailTrace_6677599 : CollatzResearch.WordTrace tailWord_6677599 prefixEnd_6677599 1142939301660841532300929 := by
  unfold tailWord_6677599
  simp only [CollatzResearch.WordTrace]
  refine ⟨243552044135206740958995851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162368029423471160639330567 243552044135206740958995851)
  ·
    refine ⟨365328066202810111438493777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 243552044135206740958995851 365328066202810111438493777)
    ·
      refine ⟨273996049652107583578870333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 365328066202810111438493777 273996049652107583578870333)
      ·
        refine ⟨102748518619540343842076375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 273996049652107583578870333 102748518619540343842076375)
        ·
          refine ⟨154122777929310515763114563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 102748518619540343842076375 154122777929310515763114563)
          ·
            refine ⟨231184166893965773644671845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 154122777929310515763114563 231184166893965773644671845)
            ·
              refine ⟨43347031292618582558375971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 231184166893965773644671845 43347031292618582558375971)
              ·
                refine ⟨65020546938927873837563957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43347031292618582558375971 65020546938927873837563957)
                ·
                  refine ⟨6095676275524488172271621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 65020546938927873837563957 6095676275524488172271621)
                  ·
                    refine ⟨1142939301660841532300929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6095676275524488172271621 1142939301660841532300929)
                    ·
                      rfl

theorem cell23_6677599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 4, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 4, 1, 5, 4].length) (baseStart_6677599 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6677599 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6677599 prefixEnd_6677599 := by exact prefixLift 6677599
  have htrace : WordTrace (prefixWord ++ tailWord_6677599) baseStart_6677599 baseEnd_6677599 := by
    simpa [prefixWord, tailWord_6677599, baseEnd_6677599] using wordTrace_append hprefix tailTrace_6677599
  have hstable : (prefixWord ++ tailWord_6677599).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6677599).length < 2 ^ (prefixWord ++ tailWord_6677599).sum := by decide
  have hdescent : baseEnd_6677599 < baseStart_6677599 := by decide
  rcases family_descends (prefixWord ++ tailWord_6677599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6677639 : List Nat := [1, 1, 4, 2, 1, 1, 1, 2, 2, 5, 3]
def baseStart_6677639 : Nat := 118140960795 + 6677639 * 2 ^ 59
def prefixEnd_6677639 : Nat := 4983230072969 + 3 ^ 40 * 6677639 * 2
def baseEnd_6677639 : Nat := 3428838444208704440402603

theorem tailTrace_6677639 : CollatzResearch.WordTrace tailWord_6677639 prefixEnd_6677639 3428838444208704440402603 := by
  unfold tailWord_6677639
  simp only [CollatzResearch.WordTrace]
  refine ⟨243553503055061827790451971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162369002036707885193634647 243553503055061827790451971)
  ·
    refine ⟨365330254582592741685677957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 243553503055061827790451971 365330254582592741685677957)
    ·
      refine ⟨68499422734236139066064617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 365330254582592741685677957 68499422734236139066064617)
      ·
        refine ⟨51374567050677104299548463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68499422734236139066064617 51374567050677104299548463)
        ·
          refine ⟨77061850576015656449322695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51374567050677104299548463 77061850576015656449322695)
          ·
            refine ⟨115592775864023484673984043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77061850576015656449322695 115592775864023484673984043)
            ·
              refine ⟨173389163796035227010976065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 115592775864023484673984043 173389163796035227010976065)
              ·
                refine ⟨130041872847026420258232049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 173389163796035227010976065 130041872847026420258232049)
                ·
                  refine ⟨97531404635269815193674037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 130041872847026420258232049 97531404635269815193674037)
                  ·
                    refine ⟨9143569184556545174406941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 97531404635269815193674037 9143569184556545174406941)
                    ·
                      refine ⟨3428838444208704440402603, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9143569184556545174406941 3428838444208704440402603)
                      ·
                        rfl

theorem cell23_6677639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 1, 2, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 1, 2, 2, 5, 3].length) (baseStart_6677639 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6677639 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6677639 prefixEnd_6677639 := by exact prefixLift 6677639
  have htrace : WordTrace (prefixWord ++ tailWord_6677639) baseStart_6677639 baseEnd_6677639 := by
    simpa [prefixWord, tailWord_6677639, baseEnd_6677639] using wordTrace_append hprefix tailTrace_6677639
  have hstable : (prefixWord ++ tailWord_6677639).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6677639).length < 2 ^ (prefixWord ++ tailWord_6677639).sum := by decide
  have hdescent : baseEnd_6677639 < baseStart_6677639 := by decide
  rcases family_descends (prefixWord ++ tailWord_6677639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6677646 : List Nat := [4, 1, 1, 3, 2, 1, 2, 3, 6]
def baseStart_6677646 : Nat := 118140960795 + 6677646 * 2 ^ 59
def prefixEnd_6677646 : Nat := 4983230072969 + 3 ^ 40 * 6677646 * 2
def baseEnd_6677646 : Nat := 380982448730365101446119

theorem tailTrace_6677646 : CollatzResearch.WordTrace tailWord_6677646 prefixEnd_6677646 380982448730365101446119 := by
  unfold tailWord_6677646
  simp only [CollatzResearch.WordTrace]
  refine ⟨30444219795754558498244599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 162369172244024311990637861 30444219795754558498244599)
  ·
    refine ⟨45666329693631837747366899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30444219795754558498244599 45666329693631837747366899)
    ·
      refine ⟨68499494540447756621050349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45666329693631837747366899 68499494540447756621050349)
      ·
        refine ⟨25687310452667908732893881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 68499494540447756621050349 25687310452667908732893881)
        ·
          refine ⟨19265482839500931549670411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25687310452667908732893881 19265482839500931549670411)
          ·
            refine ⟨28898224259251397324505617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19265482839500931549670411 28898224259251397324505617)
            ·
              refine ⟨21673668194438547993379213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28898224259251397324505617 21673668194438547993379213)
              ·
                refine ⟨8127625572914455497517205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21673668194438547993379213 8127625572914455497517205)
                ·
                  refine ⟨380982448730365101446119, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8127625572914455497517205 380982448730365101446119)
                  ·
                    rfl

theorem cell23_6677646_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 2, 3, 6].length) (baseStart_6677646 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6677646 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6677646 prefixEnd_6677646 := by exact prefixLift 6677646
  have htrace : WordTrace (prefixWord ++ tailWord_6677646) baseStart_6677646 baseEnd_6677646 := by
    simpa [prefixWord, tailWord_6677646, baseEnd_6677646] using wordTrace_append hprefix tailTrace_6677646
  have hstable : (prefixWord ++ tailWord_6677646).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6677646).length < 2 ^ (prefixWord ++ tailWord_6677646).sum := by decide
  have hdescent : baseEnd_6677646 < baseStart_6677646 := by decide
  rcases family_descends (prefixWord ++ tailWord_6677646) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6677699 : List Nat := [1, 1, 1, 3, 1, 1, 1, 3, 2, 6, 3]
def baseStart_6677699 : Nat := 118140960795 + 6677699 * 2 ^ 59
def prefixEnd_6677699 : Nat := 4983230072969 + 3 ^ 40 * 6677699 * 2
def baseEnd_6677699 : Nat := 3428869253047974205652327

theorem tailTrace_6677699 : CollatzResearch.WordTrace tailWord_6677699 prefixEnd_6677699 3428869253047974205652327 := by
  unfold tailWord_6677699
  simp only [CollatzResearch.WordTrace]
  refine ⟨243555691434844458037636151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162370460956562972025090767 243555691434844458037636151)
  ·
    refine ⟨365333537152266687056454227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 243555691434844458037636151 365333537152266687056454227)
    ·
      refine ⟨548000305728400030584681341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 365333537152266687056454227 548000305728400030584681341)
      ·
        refine ⟨205500114648150011469255503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 548000305728400030584681341 205500114648150011469255503)
        ·
          refine ⟨308250171972225017203883255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 205500114648150011469255503 308250171972225017203883255)
          ·
            refine ⟨462375257958337525805824883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 308250171972225017203883255 462375257958337525805824883)
            ·
              refine ⟨693562886937506288708737325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 462375257958337525805824883 693562886937506288708737325)
              ·
                refine ⟨260086082601564858265776497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 693562886937506288708737325 260086082601564858265776497)
                ·
                  refine ⟨195064561951173643699332373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 260086082601564858265776497 195064561951173643699332373)
                  ·
                    refine ⟨9143651341461264548406205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 195064561951173643699332373 9143651341461264548406205)
                    ·
                      refine ⟨3428869253047974205652327, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9143651341461264548406205 3428869253047974205652327)
                      ·
                        rfl

theorem cell23_6677699_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 3, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 3, 2, 6, 3].length) (baseStart_6677699 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6677699 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6677699 prefixEnd_6677699 := by exact prefixLift 6677699
  have htrace : WordTrace (prefixWord ++ tailWord_6677699) baseStart_6677699 baseEnd_6677699 := by
    simpa [prefixWord, tailWord_6677699, baseEnd_6677699] using wordTrace_append hprefix tailTrace_6677699
  have hstable : (prefixWord ++ tailWord_6677699).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6677699).length < 2 ^ (prefixWord ++ tailWord_6677699).sum := by decide
  have hdescent : baseEnd_6677699 < baseStart_6677699 := by decide
  rcases family_descends (prefixWord ++ tailWord_6677699) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6677706 : List Nat := [3, 1, 2, 1, 3, 2, 3, 1, 1, 6]
def baseStart_6677706 : Nat := 118140960795 + 6677706 * 2 ^ 59
def prefixEnd_6677706 : Nat := 4983230072969 + 3 ^ 40 * 6677706 * 2
def baseEnd_6677706 : Nat := 1142957615804185226088265

theorem tailTrace_6677706 : CollatzResearch.WordTrace tailWord_6677706 prefixEnd_6677706 1142957615804185226088265 := by
  unfold tailWord_6677706
  simp only [CollatzResearch.WordTrace]
  refine ⟨60888986686454774558285243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 162370631163879398822093981 60888986686454774558285243)
  ·
    refine ⟨91333480029682161837427865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60888986686454774558285243 91333480029682161837427865)
    ·
      refine ⟨68500110022261621378070899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 91333480029682161837427865 68500110022261621378070899)
      ·
        refine ⟨102750165033392432067106349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68500110022261621378070899 102750165033392432067106349)
        ·
          refine ⟨38531311887522162025164881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 102750165033392432067106349 38531311887522162025164881)
          ·
            refine ⟨28898483915641621518873661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38531311887522162025164881 28898483915641621518873661)
            ·
              refine ⟨10836931468365608069577623, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28898483915641621518873661 10836931468365608069577623)
              ·
                refine ⟨16255397202548412104366435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10836931468365608069577623 16255397202548412104366435)
                ·
                  refine ⟨24383095803822618156549653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16255397202548412104366435 24383095803822618156549653)
                  ·
                    refine ⟨1142957615804185226088265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24383095803822618156549653 1142957615804185226088265)
                    ·
                      rfl

theorem cell23_6677706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 3, 1, 1, 6].length) (baseStart_6677706 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6677706 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6677706 prefixEnd_6677706 := by exact prefixLift 6677706
  have htrace : WordTrace (prefixWord ++ tailWord_6677706) baseStart_6677706 baseEnd_6677706 := by
    simpa [prefixWord, tailWord_6677706, baseEnd_6677706] using wordTrace_append hprefix tailTrace_6677706
  have hstable : (prefixWord ++ tailWord_6677706).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6677706).length < 2 ^ (prefixWord ++ tailWord_6677706).sum := by decide
  have hdescent : baseEnd_6677706 < baseStart_6677706 := by decide
  rcases family_descends (prefixWord ++ tailWord_6677706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6677733 : List Nat := [1, 3, 1, 4, 3, 1, 2, 1, 1, 1, 5]
def baseStart_6677733 : Nat := 118140960795 + 6677733 * 2 ^ 59
def prefixEnd_6677733 : Nat := 4983230072969 + 3 ^ 40 * 6677733 * 2
def baseEnd_6677733 : Nat := 3428886711390227072627171

theorem tailTrace_6677733 : CollatzResearch.WordTrace tailWord_6677733 prefixEnd_6677733 3428886711390227072627171 := by
  unfold tailWord_6677733
  simp only [CollatzResearch.WordTrace]
  refine ⟨243556931516721281844373853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162371287677814187896249235 243556931516721281844373853)
  ·
    refine ⟨91333849318770480691640195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 243556931516721281844373853 91333849318770480691640195)
    ·
      refine ⟨137000773978155721037460293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91333849318770480691640195 137000773978155721037460293)
      ·
        refine ⟨25687645120904197694523805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 137000773978155721037460293 25687645120904197694523805)
        ·
          refine ⟨9632866920339074135446427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25687645120904197694523805 9632866920339074135446427)
          ·
            refine ⟨14449300380508611203169641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9632866920339074135446427 14449300380508611203169641)
            ·
              refine ⟨10836975285381458402377231, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14449300380508611203169641 10836975285381458402377231)
              ·
                refine ⟨16255462928072187603565847, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10836975285381458402377231 16255462928072187603565847)
                ·
                  refine ⟨24383194392108281405348771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16255462928072187603565847 24383194392108281405348771)
                  ·
                    refine ⟨36574791588162422108023157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24383194392108281405348771 36574791588162422108023157)
                    ·
                      refine ⟨3428886711390227072627171, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36574791588162422108023157 3428886711390227072627171)
                      ·
                        rfl

theorem cell23_6677733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 3, 1, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 3, 1, 2, 1, 1, 1, 5].length) (baseStart_6677733 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6677733 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6677733 prefixEnd_6677733 := by exact prefixLift 6677733
  have htrace : WordTrace (prefixWord ++ tailWord_6677733) baseStart_6677733 baseEnd_6677733 := by
    simpa [prefixWord, tailWord_6677733, baseEnd_6677733] using wordTrace_append hprefix tailTrace_6677733
  have hstable : (prefixWord ++ tailWord_6677733).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6677733).length < 2 ^ (prefixWord ++ tailWord_6677733).sum := by decide
  have hdescent : baseEnd_6677733 < baseStart_6677733 := by decide
  rcases family_descends (prefixWord ++ tailWord_6677733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6677779 : List Nat := [1, 1, 1, 2, 1, 3, 1, 1, 6, 6]
def baseStart_6677779 : Nat := 118140960795 + 6677779 * 2 ^ 59
def prefixEnd_6677779 : Nat := 4983230072969 + 3 ^ 40 * 6677779 * 2
def baseEnd_6677779 : Nat := 1142970110500111297550653

theorem tailTrace_6677779 : CollatzResearch.WordTrace tailWord_6677779 prefixEnd_6677779 1142970110500111297550653 := by
  unfold tailWord_6677779
  simp only [CollatzResearch.WordTrace]
  refine ⟨243558609274554631700548391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162372406183036421133698927 243558609274554631700548391)
  ·
    refine ⟨365337913911831947550822587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 243558609274554631700548391 365337913911831947550822587)
    ·
      refine ⟨548006870867747921326233881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 365337913911831947550822587 548006870867747921326233881)
      ·
        refine ⟨411005153150810940994675411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 548006870867747921326233881 411005153150810940994675411)
        ·
          refine ⟨616507729726216411492013117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 411005153150810940994675411 616507729726216411492013117)
          ·
            refine ⟨231190398647331154309504919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 616507729726216411492013117 231190398647331154309504919)
            ·
              refine ⟨346785597970996731464257379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 231190398647331154309504919 346785597970996731464257379)
              ·
                refine ⟨520178396956495097196386069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 346785597970996731464257379 520178396956495097196386069)
                ·
                  refine ⟨24383362357335707681080597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 520178396956495097196386069 24383362357335707681080597)
                  ·
                    refine ⟨1142970110500111297550653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24383362357335707681080597 1142970110500111297550653)
                    ·
                      rfl

theorem cell23_6677779_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 1, 6, 6].length) (baseStart_6677779 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6677779 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6677779 prefixEnd_6677779 := by exact prefixLift 6677779
  have htrace : WordTrace (prefixWord ++ tailWord_6677779) baseStart_6677779 baseEnd_6677779 := by
    simpa [prefixWord, tailWord_6677779, baseEnd_6677779] using wordTrace_append hprefix tailTrace_6677779
  have hstable : (prefixWord ++ tailWord_6677779).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6677779).length < 2 ^ (prefixWord ++ tailWord_6677779).sum := by decide
  have hdescent : baseEnd_6677779 < baseStart_6677779 := by decide
  rcases family_descends (prefixWord ++ tailWord_6677779) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6677796 : List Nat := [2, 3, 1, 3, 1, 1, 2, 2, 2, 6]
def baseStart_6677796 : Nat := 118140960795 + 6677796 * 2 ^ 59
def prefixEnd_6677796 : Nat := 4983230072969 + 3 ^ 40 * 6677796 * 2
def baseEnd_6677796 : Nat := 1142973020223820108713127

theorem tailTrace_6677796 : CollatzResearch.WordTrace tailWord_6677796 prefixEnd_6677796 1142973020223820108713127 := by
  unfold tailWord_6677796
  simp only [CollatzResearch.WordTrace]
  refine ⟨121779614657746521801958621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 162372819543662029069278161 121779614657746521801958621)
  ·
    refine ⟨45667355496654945675734483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 121779614657746521801958621 45667355496654945675734483)
    ·
      refine ⟨68501033244982418513601725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45667355496654945675734483 68501033244982418513601725)
      ·
        refine ⟨25687887466868406942600647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 68501033244982418513601725 25687887466868406942600647)
        ·
          refine ⟨38531831200302610413900971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25687887466868406942600647 38531831200302610413900971)
          ·
            refine ⟨57797746800453915620851457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38531831200302610413900971 57797746800453915620851457)
            ·
              refine ⟨43348310100340436715638593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 57797746800453915620851457 43348310100340436715638593)
              ·
                refine ⟨32511232575255327536728945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43348310100340436715638593 32511232575255327536728945)
                ·
                  refine ⟨24383424431441495652546709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32511232575255327536728945 24383424431441495652546709)
                  ·
                    refine ⟨1142973020223820108713127, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24383424431441495652546709 1142973020223820108713127)
                    ·
                      rfl

theorem cell23_6677796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 2, 2, 2, 6].length) (baseStart_6677796 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6677796 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6677796 prefixEnd_6677796 := by exact prefixLift 6677796
  have htrace : WordTrace (prefixWord ++ tailWord_6677796) baseStart_6677796 baseEnd_6677796 := by
    simpa [prefixWord, tailWord_6677796, baseEnd_6677796] using wordTrace_append hprefix tailTrace_6677796
  have hstable : (prefixWord ++ tailWord_6677796).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6677796).length < 2 ^ (prefixWord ++ tailWord_6677796).sum := by decide
  have hdescent : baseEnd_6677796 < baseStart_6677796 := by decide
  rcases family_descends (prefixWord ++ tailWord_6677796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6677819 : List Nat := [1, 1, 1, 1, 1, 2, 1, 1, 5, 2, 7]
def baseStart_6677819 : Nat := 118140960795 + 6677819 * 2 ^ 59
def prefixEnd_6677819 : Nat := 4983230072969 + 3 ^ 40 * 6677819 * 2
def baseEnd_6677819 : Nat := 3428930870726513736151775

theorem tailTrace_6677819 : CollatzResearch.WordTrace tailWord_6677819 prefixEnd_6677819 3428930870726513736151775 := by
  unfold tailWord_6677819
  simp only [CollatzResearch.WordTrace]
  refine ⟨243560068194409718532004511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162373378796273145688003007 243560068194409718532004511)
  ·
    refine ⟨365340102291614577798006767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 243560068194409718532004511 365340102291614577798006767)
    ·
      refine ⟨548010153437421866697010151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 365340102291614577798006767 548010153437421866697010151)
      ·
        refine ⟨822015230156132800045515227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 548010153437421866697010151 822015230156132800045515227)
        ·
          refine ⟨1233022845234199200068272841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 822015230156132800045515227 1233022845234199200068272841)
          ·
            refine ⟨924767133925649400051204631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1233022845234199200068272841 924767133925649400051204631)
            ·
              refine ⟨1387150700888474100076806947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 924767133925649400051204631 1387150700888474100076806947)
              ·
                refine ⟨2080726051332711150115210421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1387150700888474100076806947 2080726051332711150115210421)
                ·
                  refine ⟨195068067312441670323300977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2080726051332711150115210421 195068067312441670323300977)
                  ·
                    refine ⟨146301050484331252742475733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 195068067312441670323300977 146301050484331252742475733)
                    ·
                      refine ⟨3428930870726513736151775, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 146301050484331252742475733 3428930870726513736151775)
                      ·
                        rfl

theorem cell23_6677819_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 5, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 5, 2, 7].length) (baseStart_6677819 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6677819 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6677819 prefixEnd_6677819 := by exact prefixLift 6677819
  have htrace : WordTrace (prefixWord ++ tailWord_6677819) baseStart_6677819 baseEnd_6677819 := by
    simpa [prefixWord, tailWord_6677819, baseEnd_6677819] using wordTrace_append hprefix tailTrace_6677819
  have hstable : (prefixWord ++ tailWord_6677819).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6677819).length < 2 ^ (prefixWord ++ tailWord_6677819).sum := by decide
  have hdescent : baseEnd_6677819 < baseStart_6677819 := by decide
  rcases family_descends (prefixWord ++ tailWord_6677819) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6677820 : List Nat := [2, 2, 2, 2, 1, 4, 2, 1, 1, 4, 2]
def baseStart_6677820 : Nat := 118140960795 + 6677820 * 2 ^ 59
def prefixEnd_6677820 : Nat := 4983230072969 + 3 ^ 40 * 6677820 * 2
def baseEnd_6677820 : Nat := 3428931384207168232239271

theorem tailTrace_6677820 : CollatzResearch.WordTrace tailWord_6677820 prefixEnd_6677820 3428931384207168232239271 := by
  unfold tailWord_6677820
  simp only [CollatzResearch.WordTrace]
  refine ⟨121780052333703047851395457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 162373403111604063801860609 121780052333703047851395457)
  ·
    refine ⟨91335039250277285888546593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 121780052333703047851395457 91335039250277285888546593)
    ·
      refine ⟨68501279437707964416409945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 91335039250277285888546593 68501279437707964416409945)
      ·
        refine ⟨51375959578280973312307459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68501279437707964416409945 51375959578280973312307459)
        ·
          refine ⟨77063939367421459968461189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51375959578280973312307459 77063939367421459968461189)
          ·
            refine ⟨14449488631391523744086473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 77063939367421459968461189 14449488631391523744086473)
            ·
              refine ⟨10837116473543642808064855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14449488631391523744086473 10837116473543642808064855)
              ·
                refine ⟨16255674710315464212097283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10837116473543642808064855 16255674710315464212097283)
                ·
                  refine ⟨24383512065473196318145925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16255674710315464212097283 24383512065473196318145925)
                  ·
                    refine ⟨4571908512276224309652361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24383512065473196318145925 4571908512276224309652361)
                    ·
                      refine ⟨3428931384207168232239271, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4571908512276224309652361 3428931384207168232239271)
                      ·
                        rfl

theorem cell23_6677820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 4, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 4, 2, 1, 1, 4, 2].length) (baseStart_6677820 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6677820 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6677820 prefixEnd_6677820 := by exact prefixLift 6677820
  have htrace : WordTrace (prefixWord ++ tailWord_6677820) baseStart_6677820 baseEnd_6677820 := by
    simpa [prefixWord, tailWord_6677820, baseEnd_6677820] using wordTrace_append hprefix tailTrace_6677820
  have hstable : (prefixWord ++ tailWord_6677820).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6677820).length < 2 ^ (prefixWord ++ tailWord_6677820).sum := by decide
  have hdescent : baseEnd_6677820 < baseStart_6677820 := by decide
  rcases family_descends (prefixWord ++ tailWord_6677820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6677843 : List Nat := [1, 1, 1, 2, 1, 1, 8, 3, 5]
def baseStart_6677843 : Nat := 118140960795 + 6677843 * 2 ^ 59
def prefixEnd_6677843 : Nat := 4983230072969 + 3 ^ 40 * 6677843 * 2
def baseEnd_6677843 : Nat := 380993688251357960250185

theorem tailTrace_6677843 : CollatzResearch.WordTrace tailWord_6677843 prefixEnd_6677843 380993688251357960250185 := by
  unfold tailWord_6677843
  simp only [CollatzResearch.WordTrace]
  refine ⟨243560943546322770630878183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162373962364215180420585455 243560943546322770630878183)
  ·
    refine ⟨365341415319484155946317275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 243560943546322770630878183 365341415319484155946317275)
    ·
      refine ⟨548012122979226233919475913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 365341415319484155946317275 548012122979226233919475913)
      ·
        refine ⟨411009092234419675439606935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 548012122979226233919475913 411009092234419675439606935)
        ·
          refine ⟨616513638351629513159410403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 411009092234419675439606935 616513638351629513159410403)
          ·
            refine ⟨924770457527444269739115605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 616513638351629513159410403 924770457527444269739115605)
            ·
              refine ⟨10837153799149737536005261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 924770457527444269739115605 10837153799149737536005261)
              ·
                refine ⟨4063932674681151576001973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10837153799149737536005261 4063932674681151576001973)
                ·
                  refine ⟨380993688251357960250185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4063932674681151576001973 380993688251357960250185)
                  ·
                    rfl

theorem cell23_6677843_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 8, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 8, 3, 5].length) (baseStart_6677843 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6677843 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6677843 prefixEnd_6677843 := by exact prefixLift 6677843
  have htrace : WordTrace (prefixWord ++ tailWord_6677843) baseStart_6677843 baseEnd_6677843 := by
    simpa [prefixWord, tailWord_6677843, baseEnd_6677843] using wordTrace_append hprefix tailTrace_6677843
  have hstable : (prefixWord ++ tailWord_6677843).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6677843).length < 2 ^ (prefixWord ++ tailWord_6677843).sum := by decide
  have hdescent : baseEnd_6677843 < baseStart_6677843 := by decide
  rcases family_descends (prefixWord ++ tailWord_6677843) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6677890 : List Nat := [3, 4, 2, 1, 1, 1, 2, 1, 1, 7]
def baseStart_6677890 : Nat := 118140960795 + 6677890 * 2 ^ 59
def prefixEnd_6677890 : Nat := 4983230072969 + 3 ^ 40 * 6677890 * 2
def baseEnd_6677890 : Nat := 1142989109284327652787983

theorem tailTrace_6677890 : CollatzResearch.WordTrace tailWord_6677890 prefixEnd_6677890 1142989109284327652787983 := by
  unfold tailWord_6677890
  simp only [CollatzResearch.WordTrace]
  refine ⟨60890664444288124414459781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 162375105184768331771892749 60890664444288124414459781)
  ·
    refine ⟨11416999583304023327711209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 60890664444288124414459781 11416999583304023327711209)
    ·
      refine ⟨8562749687478017495783407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11416999583304023327711209 8562749687478017495783407)
      ·
        refine ⟨12844124531217026243675111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8562749687478017495783407 12844124531217026243675111)
        ·
          refine ⟨19266186796825539365512667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12844124531217026243675111 19266186796825539365512667)
          ·
            refine ⟨28899280195238309048269001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19266186796825539365512667 28899280195238309048269001)
            ·
              refine ⟨21674460146428731786201751, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28899280195238309048269001 21674460146428731786201751)
              ·
                refine ⟨32511690219643097679302627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21674460146428731786201751 32511690219643097679302627)
                ·
                  refine ⟨48767535329464646518953941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32511690219643097679302627 48767535329464646518953941)
                  ·
                    refine ⟨1142989109284327652787983, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 48767535329464646518953941 1142989109284327652787983)
                    ·
                      rfl

theorem cell23_6677890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 2, 1, 1, 7].length) (baseStart_6677890 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6677890 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6677890 prefixEnd_6677890 := by exact prefixLift 6677890
  have htrace : WordTrace (prefixWord ++ tailWord_6677890) baseStart_6677890 baseEnd_6677890 := by
    simpa [prefixWord, tailWord_6677890, baseEnd_6677890] using wordTrace_append hprefix tailTrace_6677890
  have hstable : (prefixWord ++ tailWord_6677890).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6677890).length < 2 ^ (prefixWord ++ tailWord_6677890).sum := by decide
  have hdescent : baseEnd_6677890 < baseStart_6677890 := by decide
  rcases family_descends (prefixWord ++ tailWord_6677890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6677893 : List Nat := [1, 3, 1, 1, 3, 1, 2, 2, 1, 6, 2]
def baseStart_6677893 : Nat := 118140960795 + 6677893 * 2 ^ 59
def prefixEnd_6677893 : Nat := 4983230072969 + 3 ^ 40 * 6677893 * 2
def baseEnd_6677893 : Nat := 3428968868294946446626435

theorem tailTrace_6677893 : CollatzResearch.WordTrace tailWord_6677893 prefixEnd_6677893 3428968868294946446626435 := by
  unfold tailWord_6677893
  simp only [CollatzResearch.WordTrace]
  refine ⟨243562767196141629170198333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162375178130761086113465555 243562767196141629170198333)
  ·
    refine ⟨91336037698553110938824375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 243562767196141629170198333 91336037698553110938824375)
    ·
      refine ⟨137004056547829666408236563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91336037698553110938824375 137004056547829666408236563)
      ·
        refine ⟨205506084821744499612354845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 137004056547829666408236563 205506084821744499612354845)
        ·
          refine ⟨77064781808154187354633067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 205506084821744499612354845 77064781808154187354633067)
          ·
            refine ⟨115597172712231281031949601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77064781808154187354633067 115597172712231281031949601)
            ·
              refine ⟨86697879534173460773962201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 115597172712231281031949601 86697879534173460773962201)
              ·
                refine ⟨65023409650630095580471651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 86697879534173460773962201 65023409650630095580471651)
                ·
                  refine ⟨97535114475945143370707477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 65023409650630095580471651 97535114475945143370707477)
                  ·
                    refine ⟨4571958491059928595501913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 97535114475945143370707477 4571958491059928595501913)
                    ·
                      refine ⟨3428968868294946446626435, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4571958491059928595501913 3428968868294946446626435)
                      ·
                        rfl

theorem cell23_6677893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 2, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 2, 2, 1, 6, 2].length) (baseStart_6677893 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6677893 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6677893 prefixEnd_6677893 := by exact prefixLift 6677893
  have htrace : WordTrace (prefixWord ++ tailWord_6677893) baseStart_6677893 baseEnd_6677893 := by
    simpa [prefixWord, tailWord_6677893, baseEnd_6677893] using wordTrace_append hprefix tailTrace_6677893
  have hstable : (prefixWord ++ tailWord_6677893).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6677893).length < 2 ^ (prefixWord ++ tailWord_6677893).sum := by decide
  have hdescent : baseEnd_6677893 < baseStart_6677893 := by decide
  rcases family_descends (prefixWord ++ tailWord_6677893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6677913 : List Nat := [1, 2, 1, 2, 1, 5, 1, 1, 4, 2, 3]
def baseStart_6677913 : Nat := 118140960795 + 6677913 * 2 ^ 59
def prefixEnd_6677913 : Nat := 4983230072969 + 3 ^ 40 * 6677913 * 2
def baseEnd_6677913 : Nat := 3428979137908036368376343

theorem tailTrace_6677913 : CollatzResearch.WordTrace tailWord_6677913 prefixEnd_6677913 3428979137908036368376343 := by
  unfold tailWord_6677913
  simp only [CollatzResearch.WordTrace]
  refine ⟨243563496656069172585926393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162375664437379448390617595 243563496656069172585926393)
  ·
    refine ⟨182672622492051879439444795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 243563496656069172585926393 182672622492051879439444795)
    ·
      refine ⟨274008933738077819159167193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 182672622492051879439444795 274008933738077819159167193)
      ·
        refine ⟨205506700303558364369375395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 274008933738077819159167193 205506700303558364369375395)
        ·
          refine ⟨308260050455337546554063093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 205506700303558364369375395 308260050455337546554063093)
          ·
            refine ⟨28899379730187894989443415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 308260050455337546554063093 28899379730187894989443415)
            ·
              refine ⟨43349069595281842484165123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28899379730187894989443415 43349069595281842484165123)
              ·
                refine ⟨65023604392922763726247685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43349069595281842484165123 65023604392922763726247685)
                ·
                  refine ⟨12191925823673018198671441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 65023604392922763726247685 12191925823673018198671441)
                  ·
                    refine ⟨9143944367754763649003581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12191925823673018198671441 9143944367754763649003581)
                    ·
                      refine ⟨3428979137908036368376343, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9143944367754763649003581 3428979137908036368376343)
                      ·
                        rfl

theorem cell23_6677913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 1, 1, 4, 2, 3].length) (baseStart_6677913 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6677913 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6677913 prefixEnd_6677913 := by exact prefixLift 6677913
  have htrace : WordTrace (prefixWord ++ tailWord_6677913) baseStart_6677913 baseEnd_6677913 := by
    simpa [prefixWord, tailWord_6677913, baseEnd_6677913] using wordTrace_append hprefix tailTrace_6677913
  have hstable : (prefixWord ++ tailWord_6677913).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6677913).length < 2 ^ (prefixWord ++ tailWord_6677913).sum := by decide
  have hdescent : baseEnd_6677913 < baseStart_6677913 := by decide
  rcases family_descends (prefixWord ++ tailWord_6677913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6677963 : List Nat := [1, 1, 1, 1, 3, 3, 2, 5, 1, 5]
def baseStart_6677963 : Nat := 118140960795 + 6677963 * 2 ^ 59
def prefixEnd_6677963 : Nat := 4983230072969 + 3 ^ 40 * 6677963 * 2
def baseEnd_6677963 : Nat := 1143001603980253724250371

theorem tailTrace_6677963 : CollatzResearch.WordTrace tailWord_6677963 prefixEnd_6677963 1143001603980253724250371 := by
  unfold tailWord_6677963
  simp only [CollatzResearch.WordTrace]
  refine ⟨243565320305888031125246543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162376880203925354083497695 243565320305888031125246543)
  ·
    refine ⟨365347980458832046687869815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 243565320305888031125246543 365347980458832046687869815)
    ·
      refine ⟨548021970688248070031804723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 365347980458832046687869815 548021970688248070031804723)
      ·
        refine ⟨822032956032372105047707085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 548021970688248070031804723 822032956032372105047707085)
        ·
          refine ⟨308262358512139539392890157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 822032956032372105047707085 308262358512139539392890157)
          ·
            refine ⟨115598384442052327272333809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 308262358512139539392890157 115598384442052327272333809)
            ·
              refine ⟨86698788331539245454250357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 115598384442052327272333809 86698788331539245454250357)
              ·
                refine ⟨8128011406081804261335971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 86698788331539245454250357 8128011406081804261335971)
                ·
                  refine ⟨12192017109122706392003957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8128011406081804261335971 12192017109122706392003957)
                  ·
                    refine ⟨1143001603980253724250371, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12192017109122706392003957 1143001603980253724250371)
                    ·
                      rfl

theorem cell23_6677963_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 2, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 2, 5, 1, 5].length) (baseStart_6677963 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6677963 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6677963 prefixEnd_6677963 := by exact prefixLift 6677963
  have htrace : WordTrace (prefixWord ++ tailWord_6677963) baseStart_6677963 baseEnd_6677963 := by
    simpa [prefixWord, tailWord_6677963, baseEnd_6677963] using wordTrace_append hprefix tailTrace_6677963
  have hstable : (prefixWord ++ tailWord_6677963).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6677963).length < 2 ^ (prefixWord ++ tailWord_6677963).sum := by decide
  have hdescent : baseEnd_6677963 < baseStart_6677963 := by decide
  rcases family_descends (prefixWord ++ tailWord_6677963) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6677983 : List Nat := [1, 1, 2, 3, 3, 1, 1, 1, 5, 1, 4]
def baseStart_6677983 : Nat := 118140960795 + 6677983 * 2 ^ 59
def prefixEnd_6677983 : Nat := 4983230072969 + 3 ^ 40 * 6677983 * 2
def baseEnd_6677983 : Nat := 3429015081553851094501021

theorem tailTrace_6677983 : CollatzResearch.WordTrace tailWord_6677983 prefixEnd_6677983 3429015081553851094501021 := by
  unfold tailWord_6677983
  simp only [CollatzResearch.WordTrace]
  refine ⟨243566049765815574540974603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162377366510543716360649735 243566049765815574540974603)
  ·
    refine ⟨365349074648723361811461905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 243566049765815574540974603 365349074648723361811461905)
    ·
      refine ⟨274011805986542521358596429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 365349074648723361811461905 274011805986542521358596429)
      ·
        refine ⟨102754427244953445509473661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 274011805986542521358596429 102754427244953445509473661)
        ·
          refine ⟨38532910216857542066052623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 102754427244953445509473661 38532910216857542066052623)
          ·
            refine ⟨57799365325286313099078935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38532910216857542066052623 57799365325286313099078935)
            ·
              refine ⟨86699047987929469648618403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57799365325286313099078935 86699047987929469648618403)
              ·
                refine ⟨130048571981894204472927605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 86699047987929469648618403 130048571981894204472927605)
                ·
                  refine ⟨12192053623302581669336963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 130048571981894204472927605 12192053623302581669336963)
                  ·
                    refine ⟨18288080434953872504005445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12192053623302581669336963 18288080434953872504005445)
                    ·
                      refine ⟨3429015081553851094501021, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18288080434953872504005445 3429015081553851094501021)
                      ·
                        rfl

theorem cell23_6677983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 1, 1, 5, 1, 4].length) (baseStart_6677983 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6677983 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6677983 prefixEnd_6677983 := by exact prefixLift 6677983
  have htrace : WordTrace (prefixWord ++ tailWord_6677983) baseStart_6677983 baseEnd_6677983 := by
    simpa [prefixWord, tailWord_6677983, baseEnd_6677983] using wordTrace_append hprefix tailTrace_6677983
  have hstable : (prefixWord ++ tailWord_6677983).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6677983).length < 2 ^ (prefixWord ++ tailWord_6677983).sum := by decide
  have hdescent : baseEnd_6677983 < baseStart_6677983 := by decide
  rcases family_descends (prefixWord ++ tailWord_6677983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6678014 : List Nat := [4, 2, 2, 3, 1, 1, 1, 3, 1, 5]
def baseStart_6678014 : Nat := 118140960795 + 6678014 * 2 ^ 59
def prefixEnd_6678014 : Nat := 4983230072969 + 3 ^ 40 * 6678014 * 2
def baseEnd_6678014 : Nat := 1143010333151380157737793

theorem tailTrace_6678014 : CollatzResearch.WordTrace tailWord_6678014 prefixEnd_6678014 1143010333151380157737793 := by
  unfold tailWord_6678014
  simp only [CollatzResearch.WordTrace]
  refine ⟨30445897553587908354419137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 162378120285802177890235397 30445897553587908354419137)
  ·
    refine ⟨22834423165190931265814353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30445897553587908354419137 22834423165190931265814353)
    ·
      refine ⟨17125817373893198449360765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22834423165190931265814353 17125817373893198449360765)
      ·
        refine ⟨6422181515209949418510287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17125817373893198449360765 6422181515209949418510287)
        ·
          refine ⟨9633272272814924127765431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6422181515209949418510287 9633272272814924127765431)
          ·
            refine ⟨14449908409222386191648147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9633272272814924127765431 14449908409222386191648147)
            ·
              refine ⟨21674862613833579287472221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14449908409222386191648147 21674862613833579287472221)
              ·
                refine ⟨8128073480187592232802083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21674862613833579287472221 8128073480187592232802083)
                ·
                  refine ⟨12192110220281388349203125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8128073480187592232802083 12192110220281388349203125)
                  ·
                    refine ⟨1143010333151380157737793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12192110220281388349203125 1143010333151380157737793)
                    ·
                      rfl

theorem cell23_6678014_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 1, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 1, 1, 1, 3, 1, 5].length) (baseStart_6678014 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6678014 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6678014 prefixEnd_6678014 := by exact prefixLift 6678014
  have htrace : WordTrace (prefixWord ++ tailWord_6678014) baseStart_6678014 baseEnd_6678014 := by
    simpa [prefixWord, tailWord_6678014, baseEnd_6678014] using wordTrace_append hprefix tailTrace_6678014
  have hstable : (prefixWord ++ tailWord_6678014).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6678014).length < 2 ^ (prefixWord ++ tailWord_6678014).sum := by decide
  have hdescent : baseEnd_6678014 < baseStart_6678014 := by decide
  rcases family_descends (prefixWord ++ tailWord_6678014) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6678017 : List Nat := [1, 2, 4, 1, 4, 1, 1, 3, 1, 1, 4]
def baseStart_6678017 : Nat := 118140960795 + 6678017 * 2 ^ 59
def prefixEnd_6678017 : Nat := 4983230072969 + 3 ^ 40 * 6678017 * 2
def baseEnd_6678017 : Nat := 3429032539896103961475865

theorem tailTrace_6678017 : CollatzResearch.WordTrace tailWord_6678017 prefixEnd_6678017 3429032539896103961475865 := by
  unfold tailWord_6678017
  simp only [CollatzResearch.WordTrace]
  refine ⟨243567289847692398347712305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162378193231794932231808203 243567289847692398347712305)
  ·
    refine ⟨182675467385769298760784229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 243567289847692398347712305 182675467385769298760784229)
    ·
      refine ⟨34251650134831743517647043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 182675467385769298760784229 34251650134831743517647043)
      ·
        refine ⟨51377475202247615276470565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34251650134831743517647043 51377475202247615276470565)
        ·
          refine ⟨9633276600421427864338231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 51377475202247615276470565 9633276600421427864338231)
          ·
            refine ⟨14449914900632141796507347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9633276600421427864338231 14449914900632141796507347)
            ·
              refine ⟨21674872350948212694761021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14449914900632141796507347 21674872350948212694761021)
              ·
                refine ⟨8128077131605579760535383, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21674872350948212694761021 8128077131605579760535383)
                ·
                  refine ⟨12192115697408369640803075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8128077131605579760535383 12192115697408369640803075)
                  ·
                    refine ⟨18288173546112554461204613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12192115697408369640803075 18288173546112554461204613)
                    ·
                      refine ⟨3429032539896103961475865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18288173546112554461204613 3429032539896103961475865)
                      ·
                        rfl

theorem cell23_6678017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 4, 1, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 4, 1, 1, 3, 1, 1, 4].length) (baseStart_6678017 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6678017 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6678017 prefixEnd_6678017 := by exact prefixLift 6678017
  have htrace : WordTrace (prefixWord ++ tailWord_6678017) baseStart_6678017 baseEnd_6678017 := by
    simpa [prefixWord, tailWord_6678017, baseEnd_6678017] using wordTrace_append hprefix tailTrace_6678017
  have hstable : (prefixWord ++ tailWord_6678017).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6678017).length < 2 ^ (prefixWord ++ tailWord_6678017).sum := by decide
  have hdescent : baseEnd_6678017 < baseStart_6678017 := by decide
  rcases family_descends (prefixWord ++ tailWord_6678017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6678023 : List Nat := [1, 1, 4, 3, 2, 2, 10]
def baseStart_6678023 : Nat := 118140960795 + 6678023 * 2 ^ 59
def prefixEnd_6678023 : Nat := 4983230072969 + 3 ^ 40 * 6678023 * 2
def baseEnd_6678023 : Nat := 42333773096049764666677

theorem tailTrace_6678023 : CollatzResearch.WordTrace tailWord_6678023 prefixEnd_6678023 42333773096049764666677 := by
  unfold tailWord_6678023
  simp only [CollatzResearch.WordTrace]
  refine ⟨243567508685670661372430723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162378339123780440914953815 243567508685670661372430723)
  ·
    refine ⟨365351263028505992058646085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 243567508685670661372430723 365351263028505992058646085)
    ·
      refine ⟨68503361817844873510996141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 365351263028505992058646085 68503361817844873510996141)
      ·
        refine ⟨25688760681691827566623553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 68503361817844873510996141 25688760681691827566623553)
        ·
          refine ⟨19266570511268870674967665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25688760681691827566623553 19266570511268870674967665)
          ·
            refine ⟨14449927883451653006225749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19266570511268870674967665 14449927883451653006225749)
            ·
              refine ⟨42333773096049764666677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 14449927883451653006225749 42333773096049764666677)
              ·
                rfl

theorem cell23_6678023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 2, 10].length) (baseStart_6678023 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6678023 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6678023 prefixEnd_6678023 := by exact prefixLift 6678023
  have htrace : WordTrace (prefixWord ++ tailWord_6678023) baseStart_6678023 baseEnd_6678023 := by
    simpa [prefixWord, tailWord_6678023, baseEnd_6678023] using wordTrace_append hprefix tailTrace_6678023
  have hstable : (prefixWord ++ tailWord_6678023).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6678023).length < 2 ^ (prefixWord ++ tailWord_6678023).sum := by decide
  have hdescent : baseEnd_6678023 < baseStart_6678023 := by decide
  rcases family_descends (prefixWord ++ tailWord_6678023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6678113 : List Nat := [1, 2, 3, 1, 1, 3, 2, 1, 9]
def baseStart_6678113 : Nat := 118140960795 + 6678113 * 2 ^ 59
def prefixEnd_6678113 : Nat := 4983230072969 + 3 ^ 40 * 6678113 * 2
def baseEnd_6678113 : Nat := 381009092670992842875047

theorem tailTrace_6678113 : CollatzResearch.WordTrace tailWord_6678113 prefixEnd_6678113 381009092670992842875047 := by
  unfold tailWord_6678113
  simp only [CollatzResearch.WordTrace]
  refine ⟨243570791255344606743206993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162380527503563071162137995 243570791255344606743206993)
  ·
    refine ⟨182678093441508455057405245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 243570791255344606743206993 182678093441508455057405245)
    ·
      refine ⟨68504285040565670646526967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 182678093441508455057405245 68504285040565670646526967)
      ·
        refine ⟨102756427560848505969790451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68504285040565670646526967 102756427560848505969790451)
        ·
          refine ⟨154134641341272758954685677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 102756427560848505969790451 154134641341272758954685677)
          ·
            refine ⟨57800490502977284608007129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 154134641341272758954685677 57800490502977284608007129)
            ·
              refine ⟨43350367877232963456005347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 57800490502977284608007129 43350367877232963456005347)
              ·
                refine ⟨65025551815849445184008021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43350367877232963456005347 65025551815849445184008021)
                ·
                  refine ⟨381009092670992842875047, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 65025551815849445184008021 381009092670992842875047)
                  ·
                    rfl

theorem cell23_6678113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 2, 1, 9].length) (baseStart_6678113 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6678113 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6678113 prefixEnd_6678113 := by exact prefixLift 6678113
  have htrace : WordTrace (prefixWord ++ tailWord_6678113) baseStart_6678113 baseEnd_6678113 := by
    simpa [prefixWord, tailWord_6678113, baseEnd_6678113] using wordTrace_append hprefix tailTrace_6678113
  have hstable : (prefixWord ++ tailWord_6678113).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6678113).length < 2 ^ (prefixWord ++ tailWord_6678113).sum := by decide
  have hdescent : baseEnd_6678113 < baseStart_6678113 := by decide
  rcases family_descends (prefixWord ++ tailWord_6678113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6678140 : List Nat := [2, 2, 2, 1, 1, 2, 1, 4, 2, 3, 3]
def baseStart_6678140 : Nat := 118140960795 + 6678140 * 2 ^ 59
def prefixEnd_6678140 : Nat := 4983230072969 + 3 ^ 40 * 6678140 * 2
def baseEnd_6678140 : Nat := 3429095698016606980237799

theorem tailTrace_6678140 : CollatzResearch.WordTrace tailWord_6678140 prefixEnd_6678140 3429095698016606980237799 := by
  unfold tailWord_6678140
  simp only [CollatzResearch.WordTrace]
  refine ⟨121785888013123395177219937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 162381184017497860236293249 121785888013123395177219937)
  ·
    refine ⟨91339416009842546382914953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 121785888013123395177219937 91339416009842546382914953)
    ·
      refine ⟨68504562007381909787186215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 91339416009842546382914953 68504562007381909787186215)
      ·
        refine ⟨102756843011072864680779323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68504562007381909787186215 102756843011072864680779323)
        ·
          refine ⟨154135264516609297021168985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 102756843011072864680779323 154135264516609297021168985)
          ·
            refine ⟨115601448387456972765876739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 154135264516609297021168985 115601448387456972765876739)
            ·
              refine ⟨173402172581185459148815109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 115601448387456972765876739 173402172581185459148815109)
              ·
                refine ⟨32512907358972273590402833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 173402172581185459148815109 32512907358972273590402833)
                ·
                  refine ⟨24384680519229205192802125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32512907358972273590402833 24384680519229205192802125)
                  ·
                    refine ⟨9144255194710951947300797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24384680519229205192802125 9144255194710951947300797)
                    ·
                      refine ⟨3429095698016606980237799, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9144255194710951947300797 3429095698016606980237799)
                      ·
                        rfl

theorem cell23_6678140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 1, 4, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 1, 4, 2, 3, 3].length) (baseStart_6678140 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6678140 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6678140 prefixEnd_6678140 := by exact prefixLift 6678140
  have htrace : WordTrace (prefixWord ++ tailWord_6678140) baseStart_6678140 baseEnd_6678140 := by
    simpa [prefixWord, tailWord_6678140, baseEnd_6678140] using wordTrace_append hprefix tailTrace_6678140
  have hstable : (prefixWord ++ tailWord_6678140).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6678140).length < 2 ^ (prefixWord ++ tailWord_6678140).sum := by decide
  have hdescent : baseEnd_6678140 < baseStart_6678140 := by decide
  rcases family_descends (prefixWord ++ tailWord_6678140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6678141 : List Nat := [1, 4, 1, 1, 4, 2, 2, 2, 2, 2, 2]
def baseStart_6678141 : Nat := 118140960795 + 6678141 * 2 ^ 59
def prefixEnd_6678141 : Nat := 4983230072969 + 3 ^ 40 * 6678141 * 2
def baseEnd_6678141 : Nat := 3429096211497261476325295

theorem tailTrace_6678141 : CollatzResearch.WordTrace tailWord_6678141 prefixEnd_6678141 3429096211497261476325295 := by
  unfold tailWord_6678141
  simp only [CollatzResearch.WordTrace]
  refine ⟨243571812499243167525226277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162381208332828778350150851 243571812499243167525226277)
  ·
    refine ⟨45669714843608093910979927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 243571812499243167525226277 45669714843608093910979927)
    ·
      refine ⟨68504572265412140866469891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45669714843608093910979927 68504572265412140866469891)
      ·
        refine ⟨102756858398118211299704837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68504572265412140866469891 102756858398118211299704837)
        ·
          refine ⟨19266910949647164618694657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 102756858398118211299704837 19266910949647164618694657)
          ·
            refine ⟨14450183212235373464020993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19266910949647164618694657 14450183212235373464020993)
            ·
              refine ⟨10837637409176530098015745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14450183212235373464020993 10837637409176530098015745)
              ·
                refine ⟨8128228056882397573511809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10837637409176530098015745 8128228056882397573511809)
                ·
                  refine ⟨6096171042661798180133857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8128228056882397573511809 6096171042661798180133857)
                  ·
                    refine ⟨4572128281996348635100393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6096171042661798180133857 4572128281996348635100393)
                    ·
                      refine ⟨3429096211497261476325295, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4572128281996348635100393 3429096211497261476325295)
                      ·
                        rfl

theorem cell23_6678141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 2, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 2, 2, 2, 2, 2, 2].length) (baseStart_6678141 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6678141 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6678141 prefixEnd_6678141 := by exact prefixLift 6678141
  have htrace : WordTrace (prefixWord ++ tailWord_6678141) baseStart_6678141 baseEnd_6678141 := by
    simpa [prefixWord, tailWord_6678141, baseEnd_6678141] using wordTrace_append hprefix tailTrace_6678141
  have hstable : (prefixWord ++ tailWord_6678141).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6678141).length < 2 ^ (prefixWord ++ tailWord_6678141).sum := by decide
  have hdescent : baseEnd_6678141 < baseStart_6678141 := by decide
  rcases family_descends (prefixWord ++ tailWord_6678141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6678177 : List Nat := [1, 2, 3, 3, 2, 1, 3, 1, 2, 5]
def baseStart_6678177 : Nat := 118140960795 + 6678177 * 2 ^ 59
def prefixEnd_6678177 : Nat := 4983230072969 + 3 ^ 40 * 6678177 * 2
def baseEnd_6678177 : Nat := 1143038232266941111825043

theorem tailTrace_6678177 : CollatzResearch.WordTrace tailWord_6678177 prefixEnd_6678177 1143038232266941111825043 := by
  unfold tailWord_6678177
  simp only [CollatzResearch.WordTrace]
  refine ⟨243573125527112745673536785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162382083684741830449024523 243573125527112745673536785)
  ·
    refine ⟨182679844145334559255152589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 243573125527112745673536785 182679844145334559255152589)
    ·
      refine ⟨68504941554500459720682221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 182679844145334559255152589 68504941554500459720682221)
      ·
        refine ⟨25689353082937672395255833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 68504941554500459720682221 25689353082937672395255833)
        ·
          refine ⟨19267014812203254296441875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25689353082937672395255833 19267014812203254296441875)
          ·
            refine ⟨28900522218304881444662813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19267014812203254296441875 28900522218304881444662813)
            ·
              refine ⟨10837695831864330541748555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28900522218304881444662813 10837695831864330541748555)
              ·
                refine ⟨16256543747796495812622833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10837695831864330541748555 16256543747796495812622833)
                ·
                  refine ⟨12192407810847371859467125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16256543747796495812622833 12192407810847371859467125)
                  ·
                    refine ⟨1143038232266941111825043, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12192407810847371859467125 1143038232266941111825043)
                    ·
                      rfl

theorem cell23_6678177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 3, 1, 2, 5].length) (baseStart_6678177 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6678177 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6678177 prefixEnd_6678177 := by exact prefixLift 6678177
  have htrace : WordTrace (prefixWord ++ tailWord_6678177) baseStart_6678177 baseEnd_6678177 := by
    simpa [prefixWord, tailWord_6678177, baseEnd_6678177] using wordTrace_append hprefix tailTrace_6678177
  have hstable : (prefixWord ++ tailWord_6678177).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6678177).length < 2 ^ (prefixWord ++ tailWord_6678177).sum := by decide
  have hdescent : baseEnd_6678177 < baseStart_6678177 := by decide
  rcases family_descends (prefixWord ++ tailWord_6678177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6678207 : List Nat := [1, 1, 2, 2, 2, 3, 4, 1, 3, 4]
def baseStart_6678207 : Nat := 118140960795 + 6678207 * 2 ^ 59
def prefixEnd_6678207 : Nat := 4983230072969 + 3 ^ 40 * 6678207 * 2
def baseEnd_6678207 : Nat := 1143043367073486072699997

theorem tailTrace_6678207 : CollatzResearch.WordTrace tailWord_6678207 prefixEnd_6678207 1143043367073486072699997 := by
  unfold tailWord_6678207
  simp only [CollatzResearch.WordTrace]
  refine ⟨243574219717004060797128875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162382813144669373864752583 243574219717004060797128875)
  ·
    refine ⟨365361329575506091195693313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 243574219717004060797128875 365361329575506091195693313)
    ·
      refine ⟨274020997181629568396769985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 365361329575506091195693313 274020997181629568396769985)
      ·
        refine ⟨205515747886222176297577489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 274020997181629568396769985 205515747886222176297577489)
        ·
          refine ⟨154136810914666632223183117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 205515747886222176297577489 154136810914666632223183117)
          ·
            refine ⟨57801304092999987083693669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 154136810914666632223183117 57801304092999987083693669)
            ·
              refine ⟨10837744517437497578192563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 57801304092999987083693669 10837744517437497578192563)
              ·
                refine ⟨16256616776156246367288845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10837744517437497578192563 16256616776156246367288845)
                ·
                  refine ⟨6096231291058592387733317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16256616776156246367288845 6096231291058592387733317)
                  ·
                    refine ⟨1143043367073486072699997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6096231291058592387733317 1143043367073486072699997)
                    ·
                      rfl

theorem cell23_6678207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 4, 1, 3, 4].length) (baseStart_6678207 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6678207 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6678207 prefixEnd_6678207 := by exact prefixLift 6678207
  have htrace : WordTrace (prefixWord ++ tailWord_6678207) baseStart_6678207 baseEnd_6678207 := by
    simpa [prefixWord, tailWord_6678207, baseEnd_6678207] using wordTrace_append hprefix tailTrace_6678207
  have hstable : (prefixWord ++ tailWord_6678207).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6678207).length < 2 ^ (prefixWord ++ tailWord_6678207).sum := by decide
  have hdescent : baseEnd_6678207 < baseStart_6678207 := by decide
  rcases family_descends (prefixWord ++ tailWord_6678207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6678287 : List Nat := [1, 1, 2, 1, 1, 1, 4, 6, 1, 1, 4]
def baseStart_6678287 : Nat := 118140960795 + 6678287 * 2 ^ 59
def prefixEnd_6678287 : Nat := 4983230072969 + 3 ^ 40 * 6678287 * 2
def baseEnd_6678287 : Nat := 3429171179672817905099623

theorem tailTrace_6678287 : CollatzResearch.WordTrace tailWord_6678287 prefixEnd_6678287 3429171179672817905099623 := by
  unfold tailWord_6678287
  simp only [CollatzResearch.WordTrace]
  refine ⟨243577137556714234460041115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162384758371142822973360743 243577137556714234460041115)
  ·
    refine ⟨365365706335071351690061673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 243577137556714234460041115 365365706335071351690061673)
    ·
      refine ⟨274024279751303513767546255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 365365706335071351690061673 274024279751303513767546255)
      ·
        refine ⟨411036419626955270651319383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 274024279751303513767546255 411036419626955270651319383)
        ·
          refine ⟨616554629440432905976979075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 411036419626955270651319383 616554629440432905976979075)
          ·
            refine ⟨924831944160649358965468613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 616554629440432905976979075 924831944160649358965468613)
            ·
              refine ⟨173405989530121754806025365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 924831944160649358965468613 173405989530121754806025365)
              ·
                refine ⟨8128405759224457256532439, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 173405989530121754806025365 8128405759224457256532439)
                ·
                  refine ⟨12192608638836685884798659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8128405759224457256532439 12192608638836685884798659)
                  ·
                    refine ⟨18288912958255028827197989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12192608638836685884798659 18288912958255028827197989)
                    ·
                      refine ⟨3429171179672817905099623, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18288912958255028827197989 3429171179672817905099623)
                      ·
                        rfl

theorem cell23_6678287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 4, 6, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 4, 6, 1, 1, 4].length) (baseStart_6678287 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6678287 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6678287 prefixEnd_6678287 := by exact prefixLift 6678287
  have htrace : WordTrace (prefixWord ++ tailWord_6678287) baseStart_6678287 baseEnd_6678287 := by
    simpa [prefixWord, tailWord_6678287, baseEnd_6678287] using wordTrace_append hprefix tailTrace_6678287
  have hstable : (prefixWord ++ tailWord_6678287).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6678287).length < 2 ^ (prefixWord ++ tailWord_6678287).sum := by decide
  have hdescent : baseEnd_6678287 < baseStart_6678287 := by decide
  rcases family_descends (prefixWord ++ tailWord_6678287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6678307 : List Nat := [1, 1, 1, 4, 2, 1, 5, 1, 1, 1, 5]
def baseStart_6678307 : Nat := 118140960795 + 6678307 * 2 ^ 59
def prefixEnd_6678307 : Nat := 4983230072969 + 3 ^ 40 * 6678307 * 2
def baseEnd_6678307 : Nat := 3429181449285907826849531

theorem tailTrace_6678307 : CollatzResearch.WordTrace tailWord_6678307 prefixEnd_6678307 3429181449285907826849531 := by
  unfold tailWord_6678307
  simp only [CollatzResearch.WordTrace]
  refine ⟨243577867016641777875769175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162385244677761185250512783 243577867016641777875769175)
  ·
    refine ⟨365366800524962666813653763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 243577867016641777875769175 365366800524962666813653763)
    ·
      refine ⟨548050200787444000220480645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 365366800524962666813653763 548050200787444000220480645)
      ·
        refine ⟨102759412647645750041340121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 548050200787444000220480645 102759412647645750041340121)
        ·
          refine ⟨77069559485734312531005091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 102759412647645750041340121 77069559485734312531005091)
          ·
            refine ⟨115604339228601468796507637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77069559485734312531005091 115604339228601468796507637)
            ·
              refine ⟨10837906802681387699672591, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 115604339228601468796507637 10837906802681387699672591)
              ·
                refine ⟨16256860204022081549508887, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10837906802681387699672591 16256860204022081549508887)
                ·
                  refine ⟨24385290306033122324263331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16256860204022081549508887 24385290306033122324263331)
                  ·
                    refine ⟨36577935459049683486394997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24385290306033122324263331 36577935459049683486394997)
                    ·
                      refine ⟨3429181449285907826849531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36577935459049683486394997 3429181449285907826849531)
                      ·
                        rfl

theorem cell23_6678307_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 5, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 5, 1, 1, 1, 5].length) (baseStart_6678307 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6678307 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6678307 prefixEnd_6678307 := by exact prefixLift 6678307
  have htrace : WordTrace (prefixWord ++ tailWord_6678307) baseStart_6678307 baseEnd_6678307 := by
    simpa [prefixWord, tailWord_6678307, baseEnd_6678307] using wordTrace_append hprefix tailTrace_6678307
  have hstable : (prefixWord ++ tailWord_6678307).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6678307).length < 2 ^ (prefixWord ++ tailWord_6678307).sum := by decide
  have hdescent : baseEnd_6678307 < baseStart_6678307 := by decide
  rcases family_descends (prefixWord ++ tailWord_6678307) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6678334 : List Nat := [4, 2, 1, 2, 2, 1, 1, 3, 1, 2, 4]
def baseStart_6678334 : Nat := 118140960795 + 6678334 * 2 ^ 59
def prefixEnd_6678334 : Nat := 4983230072969 + 3 ^ 40 * 6678334 * 2
def baseEnd_6678334 : Nat := 3429195313263579221211907

theorem tailTrace_6678334 : CollatzResearch.WordTrace tailWord_6678334 prefixEnd_6678334 3429195313263579221211907 := by
  unfold tailWord_6678334
  simp only [CollatzResearch.WordTrace]
  refine ⟨30447356473442995185875257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 162385901191695974324668037 30447356473442995185875257)
  ·
    refine ⟨22835517355082246389406443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30447356473442995185875257 22835517355082246389406443)
    ·
      refine ⟨34253276032623369584109665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22835517355082246389406443 34253276032623369584109665)
      ·
        refine ⟨25689957024467527188082249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34253276032623369584109665 25689957024467527188082249)
        ·
          refine ⟨19267467768350645391061687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25689957024467527188082249 19267467768350645391061687)
          ·
            refine ⟨28901201652525968086592531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19267467768350645391061687 28901201652525968086592531)
            ·
              refine ⟨43351802478788952129888797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28901201652525968086592531 43351802478788952129888797)
              ·
                refine ⟨16256925929545857048708299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 43351802478788952129888797 16256925929545857048708299)
                ·
                  refine ⟨24385388894318785573062449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16256925929545857048708299 24385388894318785573062449)
                  ·
                    refine ⟨18289041670739089179796837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24385388894318785573062449 18289041670739089179796837)
                    ·
                      refine ⟨3429195313263579221211907, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18289041670739089179796837 3429195313263579221211907)
                      ·
                        rfl

theorem cell23_6678334_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 1, 3, 1, 2, 4].length) (baseStart_6678334 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6678334 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6678334 prefixEnd_6678334 := by exact prefixLift 6678334
  have htrace : WordTrace (prefixWord ++ tailWord_6678334) baseStart_6678334 baseEnd_6678334 := by
    simpa [prefixWord, tailWord_6678334, baseEnd_6678334] using wordTrace_append hprefix tailTrace_6678334
  have hstable : (prefixWord ++ tailWord_6678334).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6678334).length < 2 ^ (prefixWord ++ tailWord_6678334).sum := by decide
  have hdescent : baseEnd_6678334 < baseStart_6678334 := by decide
  rcases family_descends (prefixWord ++ tailWord_6678334) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6678354 : List Nat := [3, 2, 2, 1, 1, 3, 2, 2, 1, 3, 3]
def baseStart_6678354 : Nat := 118140960795 + 6678354 * 2 ^ 59
def prefixEnd_6678354 : Nat := 4983230072969 + 3 ^ 40 * 6678354 * 2
def baseEnd_6678354 : Nat := 3429205582876669142961815

theorem tailTrace_6678354 : CollatzResearch.WordTrace tailWord_6678354 prefixEnd_6678354 3429205582876669142961815 := by
  unfold tailWord_6678354
  simp only [CollatzResearch.WordTrace]
  refine ⟨60894895311867876225682529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 162386387498314336601820077 60894895311867876225682529)
  ·
    refine ⟨45671171483900907169261897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60894895311867876225682529 45671171483900907169261897)
    ·
      refine ⟨34253378612925680376946423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45671171483900907169261897 34253378612925680376946423)
      ·
        refine ⟨51380067919388520565419635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34253378612925680376946423 51380067919388520565419635)
        ·
          refine ⟨77070101879082780848129453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51380067919388520565419635 77070101879082780848129453)
          ·
            refine ⟨28901288204656042818048545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 77070101879082780848129453 28901288204656042818048545)
            ·
              refine ⟨21675966153492032113536409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28901288204656042818048545 21675966153492032113536409)
              ·
                refine ⟨16256974615119024085152307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21675966153492032113536409 16256974615119024085152307)
                ·
                  refine ⟨24385461922678536127728461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16256974615119024085152307 24385461922678536127728461)
                  ·
                    refine ⟨9144548221004451047898173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24385461922678536127728461 9144548221004451047898173)
                    ·
                      refine ⟨3429205582876669142961815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9144548221004451047898173 3429205582876669142961815)
                      ·
                        rfl

theorem cell23_6678354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 2, 2, 1, 3, 3].length) (baseStart_6678354 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6678354 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6678354 prefixEnd_6678354 := by exact prefixLift 6678354
  have htrace : WordTrace (prefixWord ++ tailWord_6678354) baseStart_6678354 baseEnd_6678354 := by
    simpa [prefixWord, tailWord_6678354, baseEnd_6678354] using wordTrace_append hprefix tailTrace_6678354
  have hstable : (prefixWord ++ tailWord_6678354).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6678354).length < 2 ^ (prefixWord ++ tailWord_6678354).sum := by decide
  have hdescent : baseEnd_6678354 < baseStart_6678354 := by decide
  rcases family_descends (prefixWord ++ tailWord_6678354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6678371 : List Nat := [1, 1, 1, 5, 4, 1, 1, 1, 4, 1, 3]
def baseStart_6678371 : Nat := 118140960795 + 6678371 * 2 ^ 59
def prefixEnd_6678371 : Nat := 4983230072969 + 3 ^ 40 * 6678371 * 2
def baseEnd_6678371 : Nat := 3429214312047795576449237

theorem tailTrace_6678371 : CollatzResearch.WordTrace tailWord_6678371 prefixEnd_6678371 3429214312047795576449237 := by
  unfold tailWord_6678371
  simp only [CollatzResearch.WordTrace]
  refine ⟨243580201288409916806098967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162386800858939944537399311 243580201288409916806098967)
  ·
    refine ⟨365370301932614875209148451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 243580201288409916806098967 365370301932614875209148451)
    ·
      refine ⟨548055452898922312813722677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 365370301932614875209148451 548055452898922312813722677)
      ·
        refine ⟨51380198709273966826286501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 548055452898922312813722677 51380198709273966826286501)
        ·
          refine ⟨9633787257988868779928719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 51380198709273966826286501 9633787257988868779928719)
          ·
            refine ⟨14450680886983303169893079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9633787257988868779928719 14450680886983303169893079)
            ·
              refine ⟨21676021330474954754839619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14450680886983303169893079 21676021330474954754839619)
              ·
                refine ⟨32514031995712432132259429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21676021330474954754839619 32514031995712432132259429)
                ·
                  refine ⟨6096380999196081024798643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 32514031995712432132259429 6096380999196081024798643)
                  ·
                    refine ⟨9144571498794121537197965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6096380999196081024798643 9144571498794121537197965)
                    ·
                      refine ⟨3429214312047795576449237, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9144571498794121537197965 3429214312047795576449237)
                      ·
                        rfl

theorem cell23_6678371_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 4, 1, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 4, 1, 1, 1, 4, 1, 3].length) (baseStart_6678371 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6678371 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6678371 prefixEnd_6678371 := by exact prefixLift 6678371
  have htrace : WordTrace (prefixWord ++ tailWord_6678371) baseStart_6678371 baseEnd_6678371 := by
    simpa [prefixWord, tailWord_6678371, baseEnd_6678371] using wordTrace_append hprefix tailTrace_6678371
  have hstable : (prefixWord ++ tailWord_6678371).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6678371).length < 2 ^ (prefixWord ++ tailWord_6678371).sum := by decide
  have hdescent : baseEnd_6678371 < baseStart_6678371 := by decide
  rcases family_descends (prefixWord ++ tailWord_6678371) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6678397 : List Nat := [1, 4, 1, 1, 2, 1, 1, 4, 2, 1, 5]
def baseStart_6678397 : Nat := 118140960795 + 6678397 * 2 ^ 59
def prefixEnd_6678397 : Nat := 4983230072969 + 3 ^ 40 * 6678397 * 2
def baseEnd_6678397 : Nat := 3429227662544812474724117

theorem tailTrace_6678397 : CollatzResearch.WordTrace tailWord_6678397 prefixEnd_6678397 3429227662544812474724117 := by
  unfold tailWord_6678397
  simp only [CollatzResearch.WordTrace]
  refine ⟨243581149586315723246545445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162387433057543815497696963 243581149586315723246545445)
  ·
    refine ⟨45671465547434198108727271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 243581149586315723246545445 45671465547434198108727271)
    ·
      refine ⟨68507198321151297163090907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45671465547434198108727271 68507198321151297163090907)
      ·
        refine ⟨102760797481726945744636361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68507198321151297163090907 102760797481726945744636361)
        ·
          refine ⟨77070598111295209308477271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 102760797481726945744636361 77070598111295209308477271)
          ·
            refine ⟨115605897166942813962715907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77070598111295209308477271 115605897166942813962715907)
            ·
              refine ⟨173408845750414220944073861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 115605897166942813962715907 173408845750414220944073861)
              ·
                refine ⟨32514158578202666427013849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 173408845750414220944073861 32514158578202666427013849)
                ·
                  refine ⟨24385618933651999820260387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32514158578202666427013849 24385618933651999820260387)
                  ·
                    refine ⟨36578428400477999730390581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24385618933651999820260387 36578428400477999730390581)
                    ·
                      refine ⟨3429227662544812474724117, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36578428400477999730390581 3429227662544812474724117)
                      ·
                        rfl

theorem cell23_6678397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 1, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 1, 4, 2, 1, 5].length) (baseStart_6678397 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6678397 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6678397 prefixEnd_6678397 := by exact prefixLift 6678397
  have htrace : WordTrace (prefixWord ++ tailWord_6678397) baseStart_6678397 baseEnd_6678397 := by
    simpa [prefixWord, tailWord_6678397, baseEnd_6678397] using wordTrace_append hprefix tailTrace_6678397
  have hstable : (prefixWord ++ tailWord_6678397).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6678397).length < 2 ^ (prefixWord ++ tailWord_6678397).sum := by decide
  have hdescent : baseEnd_6678397 < baseStart_6678397 := by decide
  rcases family_descends (prefixWord ++ tailWord_6678397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6678428 : List Nat := [2, 2, 3, 3, 1, 1, 2, 1, 4, 2, 2]
def baseStart_6678428 : Nat := 118140960795 + 6678428 * 2 ^ 59
def prefixEnd_6678428 : Nat := 4983230072969 + 3 ^ 40 * 6678428 * 2
def baseEnd_6678428 : Nat := 3429243580445101853436475

theorem tailTrace_6678428 : CollatzResearch.WordTrace tailWord_6678428 prefixEnd_6678428 3429243580445101853436475 := by
  unfold tailWord_6678428
  simp only [CollatzResearch.WordTrace]
  refine ⟨121791140124601707770461969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 162388186832802277027282625 121791140124601707770461969)
  ·
    refine ⟨91343355093451280827846477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 121791140124601707770461969 91343355093451280827846477)
    ·
      refine ⟨34253758160044230310442429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 91343355093451280827846477 34253758160044230310442429)
      ·
        refine ⟨12845159310016586366415911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34253758160044230310442429 12845159310016586366415911)
        ·
          refine ⟨19267738965024879549623867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12845159310016586366415911 19267738965024879549623867)
          ·
            refine ⟨28901608447537319324435801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19267738965024879549623867 28901608447537319324435801)
            ·
              refine ⟨21676206335652989493326851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28901608447537319324435801 21676206335652989493326851)
              ·
                refine ⟨32514309503479484239990277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21676206335652989493326851 32514309503479484239990277)
                ·
                  refine ⟨6096433031902403294998177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 32514309503479484239990277 6096433031902403294998177)
                  ·
                    refine ⟨4572324773926802471248633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6096433031902403294998177 4572324773926802471248633)
                    ·
                      refine ⟨3429243580445101853436475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4572324773926802471248633 3429243580445101853436475)
                      ·
                        rfl

theorem cell23_6678428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 2, 1, 4, 2, 2].length) (baseStart_6678428 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6678428 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6678428 prefixEnd_6678428 := by exact prefixLift 6678428
  have htrace : WordTrace (prefixWord ++ tailWord_6678428) baseStart_6678428 baseEnd_6678428 := by
    simpa [prefixWord, tailWord_6678428, baseEnd_6678428] using wordTrace_append hprefix tailTrace_6678428
  have hstable : (prefixWord ++ tailWord_6678428).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6678428).length < 2 ^ (prefixWord ++ tailWord_6678428).sum := by decide
  have hdescent : baseEnd_6678428 < baseStart_6678428 := by decide
  rcases family_descends (prefixWord ++ tailWord_6678428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6678447 : List Nat := [1, 1, 2, 1, 2, 2, 3, 2, 4, 5]
def baseStart_6678447 : Nat := 118140960795 + 6678447 * 2 ^ 59
def prefixEnd_6678447 : Nat := 4983230072969 + 3 ^ 40 * 6678447 * 2
def baseEnd_6678447 : Nat := 1143084445525845759699629

theorem tailTrace_6678447 : CollatzResearch.WordTrace tailWord_6678447 prefixEnd_6678447 1143084445525845759699629 := by
  unfold tailWord_6678447
  simp only [CollatzResearch.WordTrace]
  refine ⟨243582973236134581785865595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162388648824089721190577063 243582973236134581785865595)
  ·
    refine ⟨365374459854201872678798393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 243582973236134581785865595 365374459854201872678798393)
    ·
      refine ⟨274030844890651404509098795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 365374459854201872678798393 274030844890651404509098795)
      ·
        refine ⟨411046267335977106763648193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 274030844890651404509098795 411046267335977106763648193)
        ·
          refine ⟨308284700501982830072736145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 411046267335977106763648193 308284700501982830072736145)
          ·
            refine ⟨231213525376487122554552109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 308284700501982830072736145 231213525376487122554552109)
            ·
              refine ⟨86705072016182670957957041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 231213525376487122554552109 86705072016182670957957041)
              ·
                refine ⟨65028804012137003218467781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 86705072016182670957957041 65028804012137003218467781)
                ·
                  refine ⟨12192900752275688103462709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 65028804012137003218467781 12192900752275688103462709)
                  ·
                    refine ⟨1143084445525845759699629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12192900752275688103462709 1143084445525845759699629)
                    ·
                      rfl

theorem cell23_6678447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 3, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 3, 2, 4, 5].length) (baseStart_6678447 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6678447 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6678447 prefixEnd_6678447 := by exact prefixLift 6678447
  have htrace : WordTrace (prefixWord ++ tailWord_6678447) baseStart_6678447 baseEnd_6678447 := by
    simpa [prefixWord, tailWord_6678447, baseEnd_6678447] using wordTrace_append hprefix tailTrace_6678447
  have hstable : (prefixWord ++ tailWord_6678447).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6678447).length < 2 ^ (prefixWord ++ tailWord_6678447).sum := by decide
  have hdescent : baseEnd_6678447 < baseStart_6678447 := by decide
  rcases family_descends (prefixWord ++ tailWord_6678447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6678457 : List Nat := [1, 2, 1, 4, 2, 1, 1, 2, 1, 1, 7]
def baseStart_6678457 : Nat := 118140960795 + 6678457 * 2 ^ 59
def prefixEnd_6678457 : Nat := 4983230072969 + 3 ^ 40 * 6678457 * 2
def baseEnd_6678457 : Nat := 3429258471384082239973841

theorem tailTrace_6678457 : CollatzResearch.WordTrace tailWord_6678457 prefixEnd_6678457 3429258471384082239973841 := by
  unfold tailWord_6678457
  simp only [CollatzResearch.WordTrace]
  refine ⟨243583337966098353493729625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162388891977398902329153083 243583337966098353493729625)
  ·
    refine ⟨182687503474573765120297219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 243583337966098353493729625 182687503474573765120297219)
    ·
      refine ⟨274031255211860647680445829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 182687503474573765120297219 274031255211860647680445829)
      ·
        refine ⟨51380860352223871440083593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 274031255211860647680445829 51380860352223871440083593)
        ·
          refine ⟨38535645264167903580062695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51380860352223871440083593 38535645264167903580062695)
          ·
            refine ⟨57803467896251855370094043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38535645264167903580062695 57803467896251855370094043)
            ·
              refine ⟨86705201844377783055141065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57803467896251855370094043 86705201844377783055141065)
              ·
                refine ⟨65028901383283337291355799, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 86705201844377783055141065 65028901383283337291355799)
                ·
                  refine ⟨97543352074925005937033699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 65028901383283337291355799 97543352074925005937033699)
                  ·
                    refine ⟨146315028112387508905550549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 97543352074925005937033699 146315028112387508905550549)
                    ·
                      refine ⟨3429258471384082239973841, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 146315028112387508905550549 3429258471384082239973841)
                      ·
                        rfl

theorem cell23_6678457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 1, 2, 1, 1, 7].length) (baseStart_6678457 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6678457 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6678457 prefixEnd_6678457 := by exact prefixLift 6678457
  have htrace : WordTrace (prefixWord ++ tailWord_6678457) baseStart_6678457 baseEnd_6678457 := by
    simpa [prefixWord, tailWord_6678457, baseEnd_6678457] using wordTrace_append hprefix tailTrace_6678457
  have hstable : (prefixWord ++ tailWord_6678457).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6678457).length < 2 ^ (prefixWord ++ tailWord_6678457).sum := by decide
  have hdescent : baseEnd_6678457 < baseStart_6678457 := by decide
  rcases family_descends (prefixWord ++ tailWord_6678457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6678464 : List Nat := [2, 1, 1, 2, 3, 2, 4, 1, 2, 5]
def baseStart_6678464 : Nat := 118140960795 + 6678464 * 2 ^ 59
def prefixEnd_6678464 : Nat := 4983230072969 + 3 ^ 40 * 6678464 * 2
def baseEnd_6678464 : Nat := 1143087355249554570862103

theorem tailTrace_6678464 : CollatzResearch.WordTrace tailWord_6678464 prefixEnd_6678464 1143087355249554570862103 := by
  unfold tailWord_6678464
  simp only [CollatzResearch.WordTrace]
  refine ⟨121791796638536496844617223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 162389062184715329126156297 121791796638536496844617223)
  ·
    refine ⟨182687694957804745266925835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121791796638536496844617223 182687694957804745266925835)
    ·
      refine ⟨274031542436707117900388753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 182687694957804745266925835 274031542436707117900388753)
      ·
        refine ⟨205523656827530338425291565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 274031542436707117900388753 205523656827530338425291565)
        ·
          refine ⟨77071371310323876909484337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 205523656827530338425291565 77071371310323876909484337)
          ·
            refine ⟨57803528482742907682113253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 77071371310323876909484337 57803528482742907682113253)
            ·
              refine ⟨10838161590514295190396235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 57803528482742907682113253 10838161590514295190396235)
              ·
                refine ⟨16257242385771442785594353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10838161590514295190396235 16257242385771442785594353)
                ·
                  refine ⟨12192931789328582089195765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16257242385771442785594353 12192931789328582089195765)
                  ·
                    refine ⟨1143087355249554570862103, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12192931789328582089195765 1143087355249554570862103)
                    ·
                      rfl

theorem cell23_6678464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 4, 1, 2, 5].length) (baseStart_6678464 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6678464 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6678464 prefixEnd_6678464 := by exact prefixLift 6678464
  have htrace : WordTrace (prefixWord ++ tailWord_6678464) baseStart_6678464 baseEnd_6678464 := by
    simpa [prefixWord, tailWord_6678464, baseEnd_6678464] using wordTrace_append hprefix tailTrace_6678464
  have hstable : (prefixWord ++ tailWord_6678464).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6678464).length < 2 ^ (prefixWord ++ tailWord_6678464).sum := by decide
  have hdescent : baseEnd_6678464 < baseStart_6678464 := by decide
  rcases family_descends (prefixWord ++ tailWord_6678464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6678487 : List Nat := [1, 1, 3, 2, 1, 1, 3, 1, 2, 3, 5]
def baseStart_6678487 : Nat := 118140960795 + 6678487 * 2 ^ 59
def prefixEnd_6678487 : Nat := 4983230072969 + 3 ^ 40 * 6678487 * 2
def baseEnd_6678487 : Nat := 3429273875803717122598703

theorem tailTrace_6678487 : CollatzResearch.WordTrace tailWord_6678487 prefixEnd_6678487 3429273875803717122598703 := by
  unfold tailWord_6678487
  simp only [CollatzResearch.WordTrace]
  refine ⟨243584432155989668617321715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162389621437326445744881143 243584432155989668617321715)
  ·
    refine ⟨365376648233984502925982573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 243584432155989668617321715 365376648233984502925982573)
    ·
      refine ⟨137016243087744188597243465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 365376648233984502925982573 137016243087744188597243465)
      ·
        refine ⟨102762182315808141447932599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 137016243087744188597243465 102762182315808141447932599)
        ·
          refine ⟨154143273473712212171898899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 102762182315808141447932599 154143273473712212171898899)
          ·
            refine ⟨231214910210568318257848349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 154143273473712212171898899 231214910210568318257848349)
            ·
              refine ⟨86705591328963119346693131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 231214910210568318257848349 86705591328963119346693131)
              ·
                refine ⟨130058386993444679020039697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 86705591328963119346693131 130058386993444679020039697)
                ·
                  refine ⟨97543790245083509265029773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 130058386993444679020039697 97543790245083509265029773)
                  ·
                    refine ⟨36578921341906315974386165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 97543790245083509265029773 36578921341906315974386165)
                    ·
                      refine ⟨3429273875803717122598703, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36578921341906315974386165 3429273875803717122598703)
                      ·
                        rfl

theorem cell23_6678487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 3, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 3, 1, 2, 3, 5].length) (baseStart_6678487 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6678487 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6678487 prefixEnd_6678487 := by exact prefixLift 6678487
  have htrace : WordTrace (prefixWord ++ tailWord_6678487) baseStart_6678487 baseEnd_6678487 := by
    simpa [prefixWord, tailWord_6678487, baseEnd_6678487] using wordTrace_append hprefix tailTrace_6678487
  have hstable : (prefixWord ++ tailWord_6678487).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6678487).length < 2 ^ (prefixWord ++ tailWord_6678487).sum := by decide
  have hdescent : baseEnd_6678487 < baseStart_6678487 := by decide
  rcases family_descends (prefixWord ++ tailWord_6678487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6678504 : List Nat := [2, 1, 4, 1, 1, 1, 1, 4, 1, 4, 3]
def baseStart_6678504 : Nat := 118140960795 + 6678504 * 2 ^ 59
def prefixEnd_6678504 : Nat := 4983230072969 + 3 ^ 40 * 6678504 * 2
def baseEnd_6678504 : Nat := 3429282604974843556086125

theorem tailTrace_6678504 : CollatzResearch.WordTrace tailWord_6678504 prefixEnd_6678504 3429282604974843556086125 := by
  unfold tailWord_6678504
  simp only [CollatzResearch.WordTrace]
  refine ⟨121792526098464040260345283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 162390034797952053680460377 121792526098464040260345283)
  ·
    refine ⟨182688789147696060390517925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121792526098464040260345283 182688789147696060390517925)
    ·
      refine ⟨34254147965193011323222111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 182688789147696060390517925 34254147965193011323222111)
      ·
        refine ⟨51381221947789516984833167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34254147965193011323222111 51381221947789516984833167)
        ·
          refine ⟨77071832921684275477249751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51381221947789516984833167 77071832921684275477249751)
          ·
            refine ⟨115607749382526413215874627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77071832921684275477249751 115607749382526413215874627)
            ·
              refine ⟨173411624073789619823811941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 115607749382526413215874627 173411624073789619823811941)
              ·
                refine ⟨32514679513835553716964739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 173411624073789619823811941 32514679513835553716964739)
                ·
                  refine ⟨48772019270753330575447109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32514679513835553716964739 48772019270753330575447109)
                  ·
                    refine ⟨9144753613266249482896333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 48772019270753330575447109 9144753613266249482896333)
                    ·
                      refine ⟨3429282604974843556086125, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9144753613266249482896333 3429282604974843556086125)
                      ·
                        rfl

theorem cell23_6678504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 1, 4, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 1, 4, 1, 4, 3].length) (baseStart_6678504 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6678504 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6678504 prefixEnd_6678504 := by exact prefixLift 6678504
  have htrace : WordTrace (prefixWord ++ tailWord_6678504) baseStart_6678504 baseEnd_6678504 := by
    simpa [prefixWord, tailWord_6678504, baseEnd_6678504] using wordTrace_append hprefix tailTrace_6678504
  have hstable : (prefixWord ++ tailWord_6678504).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6678504).length < 2 ^ (prefixWord ++ tailWord_6678504).sum := by decide
  have hdescent : baseEnd_6678504 < baseStart_6678504 := by decide
  rcases family_descends (prefixWord ++ tailWord_6678504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6678521 : List Nat := [1, 2, 1, 3, 1, 4, 3, 1, 2, 2, 3]
def baseStart_6678521 : Nat := 118140960795 + 6678521 * 2 ^ 59
def prefixEnd_6678521 : Nat := 4983230072969 + 3 ^ 40 * 6678521 * 2
def baseEnd_6678521 : Nat := 3429291334145969989573547

theorem tailTrace_6678521 : CollatzResearch.WordTrace tailWord_6678521 prefixEnd_6678521 3429291334145969989573547 := by
  unfold tailWord_6678521
  simp only [CollatzResearch.WordTrace]
  refine ⟨243585672237866492424059417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162390448158577661616039611 243585672237866492424059417)
  ·
    refine ⟨182689254178399869318044563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 243585672237866492424059417 182689254178399869318044563)
    ·
      refine ⟨274033881267599803977066845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 182689254178399869318044563 274033881267599803977066845)
      ·
        refine ⟨102762705475349926491400067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 274033881267599803977066845 102762705475349926491400067)
        ·
          refine ⟨154144058213024889737100101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 102762705475349926491400067 154144058213024889737100101)
          ·
            refine ⟨28902010914942166825706269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 154144058213024889737100101 28902010914942166825706269)
            ·
              refine ⟨10838254093103312559639851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28902010914942166825706269 10838254093103312559639851)
              ·
                refine ⟨16257381139654968839459777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10838254093103312559639851 16257381139654968839459777)
                ·
                  refine ⟨12193035854741226629594833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16257381139654968839459777 12193035854741226629594833)
                  ·
                    refine ⟨9144776891055919972196125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12193035854741226629594833 9144776891055919972196125)
                    ·
                      refine ⟨3429291334145969989573547, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9144776891055919972196125 3429291334145969989573547)
                      ·
                        rfl

theorem cell23_6678521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 3, 1, 2, 2, 3].length) (baseStart_6678521 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6678521 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6678521 prefixEnd_6678521 := by exact prefixLift 6678521
  have htrace : WordTrace (prefixWord ++ tailWord_6678521) baseStart_6678521 baseEnd_6678521 := by
    simpa [prefixWord, tailWord_6678521, baseEnd_6678521] using wordTrace_append hprefix tailTrace_6678521
  have hstable : (prefixWord ++ tailWord_6678521).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6678521).length < 2 ^ (prefixWord ++ tailWord_6678521).sum := by decide
  have hdescent : baseEnd_6678521 < baseStart_6678521 := by decide
  rcases family_descends (prefixWord ++ tailWord_6678521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6678527 : List Nat := [1, 1, 2, 2, 1, 2, 1, 2, 3, 2, 6]
def baseStart_6678527 : Nat := 118140960795 + 6678527 * 2 ^ 59
def prefixEnd_6678527 : Nat := 4983230072969 + 3 ^ 40 * 6678527 * 2
def baseEnd_6678527 : Nat := 3429294415029896966098519

theorem tailTrace_6678527 : CollatzResearch.WordTrace tailWord_6678527 prefixEnd_6678527 3429294415029896966098519 := by
  unfold tailWord_6678527
  simp only [CollatzResearch.WordTrace]
  refine ⟨243585891075844755448777835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162390594050563170299185223 243585891075844755448777835)
  ·
    refine ⟨365378836613767133173166753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 243585891075844755448777835 365378836613767133173166753)
    ·
      refine ⟨274034127460325349879875065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 365378836613767133173166753 274034127460325349879875065)
      ·
        refine ⟨205525595595244012409906299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 274034127460325349879875065 205525595595244012409906299)
        ·
          refine ⟨308288393392866018614859449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 205525595595244012409906299 308288393392866018614859449)
          ·
            refine ⟨231216295044649513961144587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 308288393392866018614859449 231216295044649513961144587)
            ·
              refine ⟨346824442566974270941716881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 231216295044649513961144587 346824442566974270941716881)
              ·
                refine ⟨260118331925230703206287661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 346824442566974270941716881 260118331925230703206287661)
                ·
                  refine ⟨97544374471961513702357873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 260118331925230703206287661 97544374471961513702357873)
                  ·
                    refine ⟨73158280853971135276768405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 97544374471961513702357873 73158280853971135276768405)
                    ·
                      refine ⟨3429294415029896966098519, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 73158280853971135276768405 3429294415029896966098519)
                      ·
                        rfl

theorem cell23_6678527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 2, 3, 2, 6].length) (baseStart_6678527 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6678527 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6678527 prefixEnd_6678527 := by exact prefixLift 6678527
  have htrace : WordTrace (prefixWord ++ tailWord_6678527) baseStart_6678527 baseEnd_6678527 := by
    simpa [prefixWord, tailWord_6678527, baseEnd_6678527] using wordTrace_append hprefix tailTrace_6678527
  have hstable : (prefixWord ++ tailWord_6678527).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6678527).length < 2 ^ (prefixWord ++ tailWord_6678527).sum := by decide
  have hdescent : baseEnd_6678527 < baseStart_6678527 := by decide
  rcases family_descends (prefixWord ++ tailWord_6678527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6678591 : List Nat := [1, 1, 2, 2, 3, 1, 4, 3, 1, 1, 4]
def baseStart_6678591 : Nat := 118140960795 + 6678591 * 2 ^ 59
def prefixEnd_6678591 : Nat := 4983230072969 + 3 ^ 40 * 6678591 * 2
def baseEnd_6678591 : Nat := 3429327277791784715698225

theorem tailTrace_6678591 : CollatzResearch.WordTrace tailWord_6678591 prefixEnd_6678591 3429327277791784715698225 := by
  unfold tailWord_6678591
  simp only [CollatzResearch.WordTrace]
  refine ⟨243588225347612894379107627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162392150231741929586071751 243588225347612894379107627)
  ·
    refine ⟨365382338021419341568661441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 243588225347612894379107627 365382338021419341568661441)
    ·
      refine ⟨274036753516064506176496081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 365382338021419341568661441 274036753516064506176496081)
      ·
        refine ⟨205527565137048379632372061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 274036753516064506176496081 205527565137048379632372061)
        ·
          refine ⟨77072836926393142362139523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 205527565137048379632372061 77072836926393142362139523)
          ·
            refine ⟨115609255389589713543209285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77072836926393142362139523 115609255389589713543209285)
            ·
              refine ⟨21676735385548071289351741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 115609255389589713543209285 21676735385548071289351741)
              ·
                refine ⟨8128775769580526733506903, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21676735385548071289351741 8128775769580526733506903)
                ·
                  refine ⟨12193163654370790100260355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8128775769580526733506903 12193163654370790100260355)
                  ·
                    refine ⟨18289745481556185150390533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12193163654370790100260355 18289745481556185150390533)
                    ·
                      refine ⟨3429327277791784715698225, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18289745481556185150390533 3429327277791784715698225)
                      ·
                        rfl

theorem cell23_6678591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 4, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 4, 3, 1, 1, 4].length) (baseStart_6678591 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6678591 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6678591 prefixEnd_6678591 := by exact prefixLift 6678591
  have htrace : WordTrace (prefixWord ++ tailWord_6678591) baseStart_6678591 baseEnd_6678591 := by
    simpa [prefixWord, tailWord_6678591, baseEnd_6678591] using wordTrace_append hprefix tailTrace_6678591
  have hstable : (prefixWord ++ tailWord_6678591).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6678591).length < 2 ^ (prefixWord ++ tailWord_6678591).sum := by decide
  have hdescent : baseEnd_6678591 < baseStart_6678591 := by decide
  rcases family_descends (prefixWord ++ tailWord_6678591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6678601 : List Nat := [1, 2, 1, 1, 2, 2, 4, 4, 2, 4]
def baseStart_6678601 : Nat := 118140960795 + 6678601 * 2 ^ 59
def prefixEnd_6678601 : Nat := 4983230072969 + 3 ^ 40 * 6678601 * 2
def baseEnd_6678601 : Nat := 1143110804199443225524393

theorem tailTrace_6678601 : CollatzResearch.WordTrace tailWord_6678601 prefixEnd_6678601 1143110804199443225524393 := by
  unfold tailWord_6678601
  simp only [CollatzResearch.WordTrace]
  refine ⟨243588590077576666086971657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162392393385051110724647771 243588590077576666086971657)
  ·
    refine ⟨182691442558182499565228743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 243588590077576666086971657 182691442558182499565228743)
    ·
      refine ⟨274037163837273749347843115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 182691442558182499565228743 274037163837273749347843115)
      ·
        refine ⟨411055745755910624021764673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 274037163837273749347843115 411055745755910624021764673)
        ·
          refine ⟨308291809316932968016323505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 411055745755910624021764673 308291809316932968016323505)
          ·
            refine ⟨231218856987699726012242629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 308291809316932968016323505 231218856987699726012242629)
            ·
              refine ⟨43353535685193698627295493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 231218856987699726012242629 43353535685193698627295493)
              ·
                refine ⟨8128787940973818492617905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 43353535685193698627295493 8128787940973818492617905)
                ·
                  refine ⟨6096590955730363869463429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8128787940973818492617905 6096590955730363869463429)
                  ·
                    refine ⟨1143110804199443225524393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6096590955730363869463429 1143110804199443225524393)
                    ·
                      rfl

theorem cell23_6678601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 4, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 4, 4, 2, 4].length) (baseStart_6678601 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6678601 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6678601 prefixEnd_6678601 := by exact prefixLift 6678601
  have htrace : WordTrace (prefixWord ++ tailWord_6678601) baseStart_6678601 baseEnd_6678601 := by
    simpa [prefixWord, tailWord_6678601, baseEnd_6678601] using wordTrace_append hprefix tailTrace_6678601
  have hstable : (prefixWord ++ tailWord_6678601).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6678601).length < 2 ^ (prefixWord ++ tailWord_6678601).sum := by decide
  have hdescent : baseEnd_6678601 < baseStart_6678601 := by decide
  rcases family_descends (prefixWord ++ tailWord_6678601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6678604 : List Nat := [2, 2, 1, 3, 1, 1, 3, 2, 1, 1, 6]
def baseStart_6678604 : Nat := 118140960795 + 6678604 * 2 ^ 59
def prefixEnd_6678604 : Nat := 4983230072969 + 3 ^ 40 * 6678604 * 2
def baseEnd_6678604 : Nat := 3429333953040293164835665

theorem tailTrace_6678604 : CollatzResearch.WordTrace tailWord_6678604 prefixEnd_6678604 3429333953040293164835665 := by
  unfold tailWord_6678604
  simp only [CollatzResearch.WordTrace]
  refine ⟨121794349748282898799665433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 162392466331043865066220577 121794349748282898799665433)
  ·
    refine ⟨91345762311212174099749075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 121794349748282898799665433 91345762311212174099749075)
    ·
      refine ⟨137018643466818261149623613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91345762311212174099749075 137018643466818261149623613)
      ·
        refine ⟨51381991300056847931108855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 137018643466818261149623613 51381991300056847931108855)
        ·
          refine ⟨77072986950085271896663283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51381991300056847931108855 77072986950085271896663283)
          ·
            refine ⟨115609480425127907844994925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77072986950085271896663283 115609480425127907844994925)
            ·
              refine ⟨43353555159422965441873097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 115609480425127907844994925 43353555159422965441873097)
              ·
                refine ⟨32515166369567224081404823, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43353555159422965441873097 32515166369567224081404823)
                ·
                  refine ⟨48772749554350836122107235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32515166369567224081404823 48772749554350836122107235)
                  ·
                    refine ⟨73159124331526254183160853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 48772749554350836122107235 73159124331526254183160853)
                    ·
                      refine ⟨3429333953040293164835665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 73159124331526254183160853 3429333953040293164835665)
                      ·
                        rfl

theorem cell23_6678604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 3, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 3, 2, 1, 1, 6].length) (baseStart_6678604 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6678604 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6678604 prefixEnd_6678604 := by exact prefixLift 6678604
  have htrace : WordTrace (prefixWord ++ tailWord_6678604) baseStart_6678604 baseEnd_6678604 := by
    simpa [prefixWord, tailWord_6678604, baseEnd_6678604] using wordTrace_append hprefix tailTrace_6678604
  have hstable : (prefixWord ++ tailWord_6678604).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6678604).length < 2 ^ (prefixWord ++ tailWord_6678604).sum := by decide
  have hdescent : baseEnd_6678604 < baseStart_6678604 := by decide
  rcases family_descends (prefixWord ++ tailWord_6678604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6678628 : List Nat := [2, 3, 1, 1, 2, 1, 5, 2, 1, 2, 3]
def baseStart_6678628 : Nat := 118140960795 + 6678628 * 2 ^ 59
def prefixEnd_6678628 : Nat := 4983230072969 + 3 ^ 40 * 6678628 * 2
def baseEnd_6678628 : Nat := 3429346276576001070935555

theorem tailTrace_6678628 : CollatzResearch.WordTrace tailWord_6678628 prefixEnd_6678628 3429346276576001070935555 := by
  unfold tailWord_6678628
  simp only [CollatzResearch.WordTrace]
  refine ⟨121794787424239424849102269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 162393049898985899798803025 121794787424239424849102269)
  ·
    refine ⟨45673045284089784318413351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 121794787424239424849102269 45673045284089784318413351)
    ·
      refine ⟨68509567926134676477620027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45673045284089784318413351 68509567926134676477620027)
      ·
        refine ⟨102764351889202014716430041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68509567926134676477620027 102764351889202014716430041)
        ·
          refine ⟨77073263916901511037322531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 102764351889202014716430041 77073263916901511037322531)
          ·
            refine ⟨115609895875352266555983797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77073263916901511037322531 115609895875352266555983797)
            ·
              refine ⟨10838427738314274989623481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 115609895875352266555983797 10838427738314274989623481)
              ·
                refine ⟨8128820803735706242217611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10838427738314274989623481 8128820803735706242217611)
                ·
                  refine ⟨12193231205603559363326417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8128820803735706242217611 12193231205603559363326417)
                  ·
                    refine ⟨9144923404202669522494813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12193231205603559363326417 9144923404202669522494813)
                    ·
                      refine ⟨3429346276576001070935555, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9144923404202669522494813 3429346276576001070935555)
                      ·
                        rfl

theorem cell23_6678628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 5, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 5, 2, 1, 2, 3].length) (baseStart_6678628 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6678628 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6678628 prefixEnd_6678628 := by exact prefixLift 6678628
  have htrace : WordTrace (prefixWord ++ tailWord_6678628) baseStart_6678628 baseEnd_6678628 := by
    simpa [prefixWord, tailWord_6678628, baseEnd_6678628] using wordTrace_append hprefix tailTrace_6678628
  have hstable : (prefixWord ++ tailWord_6678628).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6678628).length < 2 ^ (prefixWord ++ tailWord_6678628).sum := by decide
  have hdescent : baseEnd_6678628 < baseStart_6678628 := by decide
  rcases family_descends (prefixWord ++ tailWord_6678628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6678641 : List Nat := [1, 2, 2, 2, 1, 1, 5, 2, 1, 3, 3]
def baseStart_6678641 : Nat := 118140960795 + 6678641 * 2 ^ 59
def prefixEnd_6678641 : Nat := 4983230072969 + 3 ^ 40 * 6678641 * 2
def baseEnd_6678641 : Nat := 3429352951824509520072995

theorem tailTrace_6678641 : CollatzResearch.WordTrace tailWord_6678641 prefixEnd_6678641 3429352951824509520072995 := by
  unfold tailWord_6678641
  simp only [CollatzResearch.WordTrace]
  refine ⟨243590048997431752918427777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162393365998287835278951851 243590048997431752918427777)
  ·
    refine ⟨182692536748073814688820833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 243590048997431752918427777 182692536748073814688820833)
    ·
      refine ⟨137019402561055361016615625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 182692536748073814688820833 137019402561055361016615625)
      ·
        refine ⟨102764551920791520762461719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 137019402561055361016615625 102764551920791520762461719)
        ·
          refine ⟨154146827881187281143692579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 102764551920791520762461719 154146827881187281143692579)
          ·
            refine ⟨231220241821780921715538869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 154146827881187281143692579 231220241821780921715538869)
            ·
              refine ⟨21676897670791961410831769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 231220241821780921715538869 21676897670791961410831769)
              ·
                refine ⟨16257673253093971058123827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21676897670791961410831769 16257673253093971058123827)
                ·
                  refine ⟨24386509879640956587185741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16257673253093971058123827 24386509879640956587185741)
                  ·
                    refine ⟨9144941204865358720194653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24386509879640956587185741 9144941204865358720194653)
                    ·
                      refine ⟨3429352951824509520072995, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9144941204865358720194653 3429352951824509520072995)
                      ·
                        rfl

theorem cell23_6678641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 5, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 5, 2, 1, 3, 3].length) (baseStart_6678641 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6678641 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6678641 prefixEnd_6678641 := by exact prefixLift 6678641
  have htrace : WordTrace (prefixWord ++ tailWord_6678641) baseStart_6678641 baseEnd_6678641 := by
    simpa [prefixWord, tailWord_6678641, baseEnd_6678641] using wordTrace_append hprefix tailTrace_6678641
  have hstable : (prefixWord ++ tailWord_6678641).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6678641).length < 2 ^ (prefixWord ++ tailWord_6678641).sum := by decide
  have hdescent : baseEnd_6678641 < baseStart_6678641 := by decide
  rcases family_descends (prefixWord ++ tailWord_6678641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6678659 : List Nat := [1, 1, 1, 3, 3, 5, 2, 2, 1, 2, 2]
def baseStart_6678659 : Nat := 118140960795 + 6678659 * 2 ^ 59
def prefixEnd_6678659 : Nat := 4983230072969 + 3 ^ 40 * 6678659 * 2
def baseEnd_6678659 : Nat := 3429362194476290449647913

theorem tailTrace_6678659 : CollatzResearch.WordTrace tailWord_6678659 prefixEnd_6678659 3429362194476290449647913 := by
  unfold tailWord_6678659
  simp only [CollatzResearch.WordTrace]
  refine ⟨243590705511366541992583031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162393803674244361328388687 243590705511366541992583031)
  ·
    refine ⟨365386058267049812988874547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 243590705511366541992583031 365386058267049812988874547)
    ·
      refine ⟨548079087400574719483311821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 365386058267049812988874547 548079087400574719483311821)
      ·
        refine ⟨205529657775215519806241933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 548079087400574719483311821 205529657775215519806241933)
        ·
          refine ⟨77073621665705819927340725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 205529657775215519806241933 77073621665705819927340725)
          ·
            refine ⟨7225652031159920618188193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 77073621665705819927340725 7225652031159920618188193)
            ·
              refine ⟨5419239023369940463641145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7225652031159920618188193 5419239023369940463641145)
              ·
                refine ⟨4064429267527455347730859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5419239023369940463641145 4064429267527455347730859)
                ·
                  refine ⟨6096643901291183021596289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4064429267527455347730859 6096643901291183021596289)
                  ·
                    refine ⟨4572482925968387266197217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6096643901291183021596289 4572482925968387266197217)
                    ·
                      refine ⟨3429362194476290449647913, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4572482925968387266197217 3429362194476290449647913)
                      ·
                        rfl

theorem cell23_6678659_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 5, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 5, 2, 2, 1, 2, 2].length) (baseStart_6678659 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6678659 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6678659 prefixEnd_6678659 := by exact prefixLift 6678659
  have htrace : WordTrace (prefixWord ++ tailWord_6678659) baseStart_6678659 baseEnd_6678659 := by
    simpa [prefixWord, tailWord_6678659, baseEnd_6678659] using wordTrace_append hprefix tailTrace_6678659
  have hstable : (prefixWord ++ tailWord_6678659).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6678659).length < 2 ^ (prefixWord ++ tailWord_6678659).sum := by decide
  have hdescent : baseEnd_6678659 < baseStart_6678659 := by decide
  rcases family_descends (prefixWord ++ tailWord_6678659) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6678709 : List Nat := [1, 3, 3, 4, 1, 2, 1, 2, 2, 1, 3]
def baseStart_6678709 : Nat := 118140960795 + 6678709 * 2 ^ 59
def prefixEnd_6678709 : Nat := 4983230072969 + 3 ^ 40 * 6678709 * 2
def baseEnd_6678709 : Nat := 3429387868509015254022683

theorem tailTrace_6678709 : CollatzResearch.WordTrace tailWord_6678709 prefixEnd_6678709 3429387868509015254022683 := by
  unfold tailWord_6678709
  simp only [CollatzResearch.WordTrace]
  refine ⟨243592529161185400531903181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162395019440790267021268787 243592529161185400531903181)
  ·
    refine ⟨91347198435444525199463693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 243592529161185400531903181 91347198435444525199463693)
    ·
      refine ⟨34255199413291696949798885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 91347198435444525199463693 34255199413291696949798885)
      ·
        refine ⟨6422849889992193178087291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 34255199413291696949798885 6422849889992193178087291)
        ·
          refine ⟨9634274834988289767130937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6422849889992193178087291 9634274834988289767130937)
          ·
            refine ⟨7225706126241217325348203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9634274834988289767130937 7225706126241217325348203)
            ·
              refine ⟨10838559189361825988022305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7225706126241217325348203 10838559189361825988022305)
              ·
                refine ⟨8128919392021369491016729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10838559189361825988022305 8128919392021369491016729)
                ·
                  refine ⟨6096689544016027118262547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8128919392021369491016729 6096689544016027118262547)
                  ·
                    refine ⟨9145034316024040677393821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6096689544016027118262547 9145034316024040677393821)
                    ·
                      refine ⟨3429387868509015254022683, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9145034316024040677393821 3429387868509015254022683)
                      ·
                        rfl

theorem cell23_6678709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 1, 2, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 1, 2, 1, 2, 2, 1, 3].length) (baseStart_6678709 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6678709 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6678709 prefixEnd_6678709 := by exact prefixLift 6678709
  have htrace : WordTrace (prefixWord ++ tailWord_6678709) baseStart_6678709 baseEnd_6678709 := by
    simpa [prefixWord, tailWord_6678709, baseEnd_6678709] using wordTrace_append hprefix tailTrace_6678709
  have hstable : (prefixWord ++ tailWord_6678709).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6678709).length < 2 ^ (prefixWord ++ tailWord_6678709).sum := by decide
  have hdescent : baseEnd_6678709 < baseStart_6678709 := by decide
  rcases family_descends (prefixWord ++ tailWord_6678709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6678711 : List Nat := [1, 1, 3, 1, 4, 2, 1, 2, 2, 2, 4]
def baseStart_6678711 : Nat := 118140960795 + 6678711 * 2 ^ 59
def prefixEnd_6678711 : Nat := 4983230072969 + 3 ^ 40 * 6678711 * 2
def baseEnd_6678711 : Nat := 3429388895470324246197673

theorem tailTrace_6678711 : CollatzResearch.WordTrace tailWord_6678711 prefixEnd_6678711 3429388895470324246197673 := by
  unfold tailWord_6678711
  simp only [CollatzResearch.WordTrace]
  refine ⟨243592602107178154873475987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162395068071452103248983991 243592602107178154873475987)
  ·
    refine ⟨365388903160767232310213981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 243592602107178154873475987 365388903160767232310213981)
    ·
      refine ⟨137020838685287712116330243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 365388903160767232310213981 137020838685287712116330243)
      ·
        refine ⟨205531258027931568174495365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 137020838685287712116330243 205531258027931568174495365)
        ·
          refine ⟨38537110880237169032717881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 205531258027931568174495365 38537110880237169032717881)
          ·
            refine ⟨28902833160177876774538411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38537110880237169032717881 28902833160177876774538411)
            ·
              refine ⟨43354249740266815161807617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28902833160177876774538411 43354249740266815161807617)
              ·
                refine ⟨32515687305200111371355713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43354249740266815161807617 32515687305200111371355713)
                ·
                  refine ⟨24386765478900083528516785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32515687305200111371355713 24386765478900083528516785)
                  ·
                    refine ⟨18290074109175062646387589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24386765478900083528516785 18290074109175062646387589)
                    ·
                      refine ⟨3429388895470324246197673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18290074109175062646387589 3429388895470324246197673)
                      ·
                        rfl

theorem cell23_6678711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 1, 2, 2, 2, 4].length) (baseStart_6678711 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6678711 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6678711 prefixEnd_6678711 := by exact prefixLift 6678711
  have htrace : WordTrace (prefixWord ++ tailWord_6678711) baseStart_6678711 baseEnd_6678711 := by
    simpa [prefixWord, tailWord_6678711, baseEnd_6678711] using wordTrace_append hprefix tailTrace_6678711
  have hstable : (prefixWord ++ tailWord_6678711).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6678711).length < 2 ^ (prefixWord ++ tailWord_6678711).sum := by decide
  have hdescent : baseEnd_6678711 < baseStart_6678711 := by decide
  rcases family_descends (prefixWord ++ tailWord_6678711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6678731 : List Nat := [1, 1, 1, 1, 3, 2, 3, 3, 2, 3, 3]
def baseStart_6678731 : Nat := 118140960795 + 6678731 * 2 ^ 59
def prefixEnd_6678731 : Nat := 4983230072969 + 3 ^ 40 * 6678731 * 2
def baseEnd_6678731 : Nat := 3429399165083414167947581

theorem tailTrace_6678731 : CollatzResearch.WordTrace tailWord_6678731 prefixEnd_6678731 3429399165083414167947581 := by
  unfold tailWord_6678731
  simp only [CollatzResearch.WordTrace]
  refine ⟨243593331567105698289204047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162395554378070465526136031 243593331567105698289204047)
  ·
    refine ⟨365389997350658547433806071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 243593331567105698289204047 365389997350658547433806071)
    ·
      refine ⟨548084996025987821150709107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 365389997350658547433806071 548084996025987821150709107)
      ·
        refine ⟨822127494038981731726063661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 548084996025987821150709107 822127494038981731726063661)
        ·
          refine ⟨308297810264618149397273873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 822127494038981731726063661 308297810264618149397273873)
          ·
            refine ⟨231223357698463612047955405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 308297810264618149397273873 231223357698463612047955405)
            ·
              refine ⟨86708759136923854517983277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 231223357698463612047955405 86708759136923854517983277)
              ·
                refine ⟨32515784676346445444243729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 86708759136923854517983277 32515784676346445444243729)
                ·
                  refine ⟨24386838507259834083182797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32515784676346445444243729 24386838507259834083182797)
                  ·
                    refine ⟨9145064440222437781193549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24386838507259834083182797 9145064440222437781193549)
                    ·
                      refine ⟨3429399165083414167947581, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9145064440222437781193549 3429399165083414167947581)
                      ·
                        rfl

theorem cell23_6678731_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 3, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 3, 3, 2, 3, 3].length) (baseStart_6678731 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6678731 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6678731 prefixEnd_6678731 := by exact prefixLift 6678731
  have htrace : WordTrace (prefixWord ++ tailWord_6678731) baseStart_6678731 baseEnd_6678731 := by
    simpa [prefixWord, tailWord_6678731, baseEnd_6678731] using wordTrace_append hprefix tailTrace_6678731
  have hstable : (prefixWord ++ tailWord_6678731).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6678731).length < 2 ^ (prefixWord ++ tailWord_6678731).sum := by decide
  have hdescent : baseEnd_6678731 < baseStart_6678731 := by decide
  rcases family_descends (prefixWord ++ tailWord_6678731) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6678751 : List Nat := [1, 1, 2, 3, 2, 1, 1, 5, 2, 5]
def baseStart_6678751 : Nat := 118140960795 + 6678751 * 2 ^ 59
def prefixEnd_6678751 : Nat := 4983230072969 + 3 ^ 40 * 6678751 * 2
def baseEnd_6678751 : Nat := 1143136478232168029899163

theorem tailTrace_6678751 : CollatzResearch.WordTrace tailWord_6678751 prefixEnd_6678751 1143136478232168029899163 := by
  unfold tailWord_6678751
  simp only [CollatzResearch.WordTrace]
  refine ⟨243594061027033241704932107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162396040684688827803288071 243594061027033241704932107)
  ·
    refine ⟨365391091540549862557398161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 243594061027033241704932107 365391091540549862557398161)
    ·
      refine ⟨274043318655412396918048621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 365391091540549862557398161 274043318655412396918048621)
      ·
        refine ⟨102766244495779648844268233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 274043318655412396918048621 102766244495779648844268233)
        ·
          refine ⟨77074683371834736633201175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 102766244495779648844268233 77074683371834736633201175)
          ·
            refine ⟨115612025057752104949801763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77074683371834736633201175 115612025057752104949801763)
            ·
              refine ⟨173418037586628157424702645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 115612025057752104949801763 173418037586628157424702645)
              ·
                refine ⟨16257941023746389758565873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 173418037586628157424702645 16257941023746389758565873)
                ·
                  refine ⟨12193455767809792318924405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16257941023746389758565873 12193455767809792318924405)
                  ·
                    refine ⟨1143136478232168029899163, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12193455767809792318924405 1143136478232168029899163)
                    ·
                      rfl

theorem cell23_6678751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 1, 5, 2, 5].length) (baseStart_6678751 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6678751 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6678751 prefixEnd_6678751 := by exact prefixLift 6678751
  have htrace : WordTrace (prefixWord ++ tailWord_6678751) baseStart_6678751 baseEnd_6678751 := by
    simpa [prefixWord, tailWord_6678751, baseEnd_6678751] using wordTrace_append hprefix tailTrace_6678751
  have hstable : (prefixWord ++ tailWord_6678751).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6678751).length < 2 ^ (prefixWord ++ tailWord_6678751).sum := by decide
  have hdescent : baseEnd_6678751 < baseStart_6678751 := by decide
  rcases family_descends (prefixWord ++ tailWord_6678751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6678798 : List Nat := [4, 1, 1, 2, 1, 2, 2, 1, 5, 4]
def baseStart_6678798 : Nat := 118140960795 + 6678798 * 2 ^ 59
def prefixEnd_6678798 : Nat := 4983230072969 + 3 ^ 40 * 6678798 * 2
def baseEnd_6678798 : Nat := 1143144522762421801936591

theorem tailTrace_6678798 : CollatzResearch.WordTrace tailWord_6678798 prefixEnd_6678798 1143144522762421801936591 := by
  unfold tailWord_6678798
  simp only [CollatzResearch.WordTrace]
  refine ⟨30449471907232871091486631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 162397183505241979154595365 30449471907232871091486631)
  ·
    refine ⟨45674207860849306637229947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30449471907232871091486631 45674207860849306637229947)
    ·
      refine ⟨68511311791273959955844921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45674207860849306637229947 68511311791273959955844921)
      ·
        refine ⟨51383483843455469966883691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68511311791273959955844921 51383483843455469966883691)
        ·
          refine ⟨77075225765183204950325537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51383483843455469966883691 77075225765183204950325537)
          ·
            refine ⟨57806419323887403712744153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 77075225765183204950325537 57806419323887403712744153)
            ·
              refine ⟨43354814492915552784558115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 57806419323887403712744153 43354814492915552784558115)
              ·
                refine ⟨65032221739373329176837173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43354814492915552784558115 65032221739373329176837173)
                ·
                  refine ⟨6096770788066249610328485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 65032221739373329176837173 6096770788066249610328485)
                  ·
                    refine ⟨1143144522762421801936591, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6096770788066249610328485 1143144522762421801936591)
                    ·
                      rfl

theorem cell23_6678798_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 2, 1, 5, 4].length) (baseStart_6678798 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6678798 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6678798 prefixEnd_6678798 := by exact prefixLift 6678798
  have htrace : WordTrace (prefixWord ++ tailWord_6678798) baseStart_6678798 baseEnd_6678798 := by
    simpa [prefixWord, tailWord_6678798, baseEnd_6678798] using wordTrace_append hprefix tailTrace_6678798
  have hstable : (prefixWord ++ tailWord_6678798).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6678798).length < 2 ^ (prefixWord ++ tailWord_6678798).sum := by decide
  have hdescent : baseEnd_6678798 < baseStart_6678798 := by decide
  rcases family_descends (prefixWord ++ tailWord_6678798) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6678823 : List Nat := [1, 1, 8, 1, 2, 1, 2, 2, 5]
def baseStart_6678823 : Nat := 118140960795 + 6678823 * 2 ^ 59
def prefixEnd_6678823 : Nat := 4983230072969 + 3 ^ 40 * 6678823 * 2
def baseEnd_6678823 : Nat := 381049600589291978666351

theorem tailTrace_6678823 : CollatzResearch.WordTrace tailWord_6678823 prefixEnd_6678823 381049600589291978666351 := by
  unfold tailWord_6678823
  simp only [CollatzResearch.WordTrace]
  refine ⟨243596687082772398001553123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162397791388514932001035415 243596687082772398001553123)
  ·
    refine ⟨365395030624158597002329685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 243596687082772398001553123 365395030624158597002329685)
    ·
      refine ⟨4281973015126858558621051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 8 365395030624158597002329685 4281973015126858558621051)
      ·
        refine ⟨6422959522690287837931577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4281973015126858558621051 6422959522690287837931577)
        ·
          refine ⟨4817219642017715878448683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6422959522690287837931577 4817219642017715878448683)
          ·
            refine ⟨7225829463026573817673025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4817219642017715878448683 7225829463026573817673025)
            ·
              refine ⟨5419372097269930363254769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7225829463026573817673025 5419372097269930363254769)
              ·
                refine ⟨4064529072952447772441077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5419372097269930363254769 4064529072952447772441077)
                ·
                  refine ⟨381049600589291978666351, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4064529072952447772441077 381049600589291978666351)
                  ·
                    rfl

theorem cell23_6678823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 2, 1, 2, 2, 5].length) (baseStart_6678823 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6678823 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6678823 prefixEnd_6678823 := by exact prefixLift 6678823
  have htrace : WordTrace (prefixWord ++ tailWord_6678823) baseStart_6678823 baseEnd_6678823 := by
    simpa [prefixWord, tailWord_6678823, baseEnd_6678823] using wordTrace_append hprefix tailTrace_6678823
  have hstable : (prefixWord ++ tailWord_6678823).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6678823).length < 2 ^ (prefixWord ++ tailWord_6678823).sum := by decide
  have hdescent : baseEnd_6678823 < baseStart_6678823 := by decide
  rcases family_descends (prefixWord ++ tailWord_6678823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6678855 : List Nat := [1, 1, 4, 1, 2, 2, 3, 2, 3, 1, 3]
def baseStart_6678855 : Nat := 118140960795 + 6678855 * 2 ^ 59
def prefixEnd_6678855 : Nat := 4983230072969 + 3 ^ 40 * 6678855 * 2
def baseEnd_6678855 : Nat := 3429462836684571682797011

theorem tailTrace_6678855 : CollatzResearch.WordTrace tailWord_6678855 prefixEnd_6678855 3429462836684571682797011 := by
  unfold tailWord_6678855
  simp only [CollatzResearch.WordTrace]
  refine ⟨243597854218656467466718019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162398569479104311644478679 243597854218656467466718019)
  ·
    refine ⟨365396781327984701200077029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 243597854218656467466718019 365396781327984701200077029)
    ·
      refine ⟨68511896498997131475014443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 365396781327984701200077029 68511896498997131475014443)
      ·
        refine ⟨102767844748495697212521665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68511896498997131475014443 102767844748495697212521665)
        ·
          refine ⟨77075883561371772909391249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 102767844748495697212521665 77075883561371772909391249)
          ·
            refine ⟨57806912671028829682043437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 77075883561371772909391249 57806912671028829682043437)
            ·
              refine ⟨21677592251635811130766289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 57806912671028829682043437 21677592251635811130766289)
              ·
                refine ⟨16258194188726858348074717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21677592251635811130766289 16258194188726858348074717)
                ·
                  refine ⟨6096822820772571880528019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16258194188726858348074717 6096822820772571880528019)
                  ·
                    refine ⟨9145234231158857820792029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6096822820772571880528019 9145234231158857820792029)
                    ·
                      refine ⟨3429462836684571682797011, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9145234231158857820792029 3429462836684571682797011)
                      ·
                        rfl

theorem cell23_6678855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 3, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 3, 2, 3, 1, 3].length) (baseStart_6678855 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6678855 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6678855 prefixEnd_6678855 := by exact prefixLift 6678855
  have htrace : WordTrace (prefixWord ++ tailWord_6678855) baseStart_6678855 baseEnd_6678855 := by
    simpa [prefixWord, tailWord_6678855, baseEnd_6678855] using wordTrace_append hprefix tailTrace_6678855
  have hstable : (prefixWord ++ tailWord_6678855).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6678855).length < 2 ^ (prefixWord ++ tailWord_6678855).sum := by decide
  have hdescent : baseEnd_6678855 < baseStart_6678855 := by decide
  rcases family_descends (prefixWord ++ tailWord_6678855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6678865 : List Nat := [1, 2, 2, 1, 4, 3, 1, 1, 1, 5, 2]
def baseStart_6678865 : Nat := 118140960795 + 6678865 * 2 ^ 59
def prefixEnd_6678865 : Nat := 4983230072969 + 3 ^ 40 * 6678865 * 2
def baseEnd_6678865 : Nat := 3429467971491116643671965

theorem tailTrace_6678865 : CollatzResearch.WordTrace tailWord_6678865 prefixEnd_6678865 3429467971491116643671965 := by
  unfold tailWord_6678865
  simp only [CollatzResearch.WordTrace]
  refine ⟨243598218948620239174582049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162398812632413492783054699 243598218948620239174582049)
  ·
    refine ⟨182698664211465179380936537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 243598218948620239174582049 182698664211465179380936537)
    ·
      refine ⟨137023998158598884535702403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 182698664211465179380936537 137023998158598884535702403)
      ·
        refine ⟨205535997237898326803553605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 137023998158598884535702403 205535997237898326803553605)
        ·
          refine ⟨38537999482105936275666301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 205535997237898326803553605 38537999482105936275666301)
          ·
            refine ⟨14451749805789726103374863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38537999482105936275666301 14451749805789726103374863)
            ·
              refine ⟨21677624708684589155062295, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14451749805789726103374863 21677624708684589155062295)
              ·
                refine ⟨32516437063026883732593443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21677624708684589155062295 32516437063026883732593443)
                ·
                  refine ⟨48774655594540325598890165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32516437063026883732593443 48774655594540325598890165)
                  ·
                    refine ⟨4572623961988155524895953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 48774655594540325598890165 4572623961988155524895953)
                    ·
                      refine ⟨3429467971491116643671965, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4572623961988155524895953 3429467971491116643671965)
                      ·
                        rfl

theorem cell23_6678865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 3, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 3, 1, 1, 1, 5, 2].length) (baseStart_6678865 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6678865 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6678865 prefixEnd_6678865 := by exact prefixLift 6678865
  have htrace : WordTrace (prefixWord ++ tailWord_6678865) baseStart_6678865 baseEnd_6678865 := by
    simpa [prefixWord, tailWord_6678865, baseEnd_6678865] using wordTrace_append hprefix tailTrace_6678865
  have hstable : (prefixWord ++ tailWord_6678865).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6678865).length < 2 ^ (prefixWord ++ tailWord_6678865).sum := by decide
  have hdescent : baseEnd_6678865 < baseStart_6678865 := by decide
  rcases family_descends (prefixWord ++ tailWord_6678865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6678891 : List Nat := [1, 1, 1, 1, 2, 2, 2, 3, 3, 1, 6]
def baseStart_6678891 : Nat := 118140960795 + 6678891 * 2 ^ 59
def prefixEnd_6678891 : Nat := 4983230072969 + 3 ^ 40 * 6678891 * 2
def baseEnd_6678891 : Nat := 3429481321988133541946845

theorem tailTrace_6678891 : CollatzResearch.WordTrace tailWord_6678891 prefixEnd_6678891 3429481321988133541946845 := by
  unfold tailWord_6678891
  simp only [CollatzResearch.WordTrace]
  refine ⟨243599167246526045615028527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162399444831017363743352351 243599167246526045615028527)
  ·
    refine ⟨365398750869789068422542791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 243599167246526045615028527 365398750869789068422542791)
    ·
      refine ⟨548098126304683602633814187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 365398750869789068422542791 548098126304683602633814187)
      ·
        refine ⟨822147189457025403950721281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 548098126304683602633814187 822147189457025403950721281)
        ·
          refine ⟨616610392092769052963040961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 822147189457025403950721281 616610392092769052963040961)
          ·
            refine ⟨462457794069576789722280721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 616610392092769052963040961 462457794069576789722280721)
            ·
              refine ⟨346843345552182592291710541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 462457794069576789722280721 346843345552182592291710541)
              ·
                refine ⟨130066254582068472109391453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 346843345552182592291710541 130066254582068472109391453)
                ·
                  refine ⟨48774845468275677041021795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 130066254582068472109391453 48774845468275677041021795)
                  ·
                    refine ⟨73162268202413515561532693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 48774845468275677041021795 73162268202413515561532693)
                    ·
                      refine ⟨3429481321988133541946845, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 73162268202413515561532693 3429481321988133541946845)
                      ·
                        rfl

theorem cell23_6678891_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 3, 3, 1, 6].length) (baseStart_6678891 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6678891 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6678891 prefixEnd_6678891 := by exact prefixLift 6678891
  have htrace : WordTrace (prefixWord ++ tailWord_6678891) baseStart_6678891 baseEnd_6678891 := by
    simpa [prefixWord, tailWord_6678891, baseEnd_6678891] using wordTrace_append hprefix tailTrace_6678891
  have hstable : (prefixWord ++ tailWord_6678891).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6678891).length < 2 ^ (prefixWord ++ tailWord_6678891).sum := by decide
  have hdescent : baseEnd_6678891 < baseStart_6678891 := by decide
  rcases family_descends (prefixWord ++ tailWord_6678891) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6678898 : List Nat := [3, 2, 1, 2, 1, 3, 1, 1, 3, 1, 5]
def baseStart_6678898 : Nat := 118140960795 + 6678898 * 2 ^ 59
def prefixEnd_6678898 : Nat := 4983230072969 + 3 ^ 40 * 6678898 * 2
def baseEnd_6678898 : Nat := 3429484916352715014559313

theorem tailTrace_6678898 : CollatzResearch.WordTrace tailWord_6678898 prefixEnd_6678898 3429484916352715014559313 := by
  unfold tailWord_6678898
  simp only [CollatzResearch.WordTrace]
  refine ⟨60899855639375171452633337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 162399615038333790540355565 60899855639375171452633337)
  ·
    refine ⟨45674891729531378589475003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60899855639375171452633337 45674891729531378589475003)
    ·
      refine ⟨68512337594297067884212505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45674891729531378589475003 68512337594297067884212505)
      ·
        refine ⟨51384253195722800913159379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68512337594297067884212505 51384253195722800913159379)
        ·
          refine ⟨77076379793584201369739069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51384253195722800913159379 77076379793584201369739069)
          ·
            refine ⟨28903642422594075513652151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 77076379793584201369739069 28903642422594075513652151)
            ·
              refine ⟨43355463633891113270478227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28903642422594075513652151 43355463633891113270478227)
              ·
                refine ⟨65033195450836669905717341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43355463633891113270478227 65033195450836669905717341)
                ·
                  refine ⟨24387448294063751214644003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 65033195450836669905717341 24387448294063751214644003)
                  ·
                    refine ⟨36581172441095626821966005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24387448294063751214644003 36581172441095626821966005)
                    ·
                      refine ⟨3429484916352715014559313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36581172441095626821966005 3429484916352715014559313)
                      ·
                        rfl

theorem cell23_6678898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 1, 1, 3, 1, 5].length) (baseStart_6678898 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6678898 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6678898 prefixEnd_6678898 := by exact prefixLift 6678898
  have htrace : WordTrace (prefixWord ++ tailWord_6678898) baseStart_6678898 baseEnd_6678898 := by
    simpa [prefixWord, tailWord_6678898, baseEnd_6678898] using wordTrace_append hprefix tailTrace_6678898
  have hstable : (prefixWord ++ tailWord_6678898).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6678898).length < 2 ^ (prefixWord ++ tailWord_6678898).sum := by decide
  have hdescent : baseEnd_6678898 < baseStart_6678898 := by decide
  rcases family_descends (prefixWord ++ tailWord_6678898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6678908 : List Nat := [2, 2, 2, 1, 1, 1, 2, 5, 1, 2, 4]
def baseStart_6678908 : Nat := 118140960795 + 6678908 * 2 ^ 59
def prefixEnd_6678908 : Nat := 4983230072969 + 3 ^ 40 * 6678908 * 2
def baseEnd_6678908 : Nat := 3429490051159259975434267

theorem tailTrace_6678908 : CollatzResearch.WordTrace tailWord_6678908 prefixEnd_6678908 3429490051159259975434267 := by
  unfold tailWord_6678908
  simp only [CollatzResearch.WordTrace]
  refine ⟨121799893643732228759198689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 162399858191642971678931585 121799893643732228759198689)
  ·
    refine ⟨91349920232799171569399017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 121799893643732228759198689 91349920232799171569399017)
    ·
      refine ⟨68512440174599378677049263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 91349920232799171569399017 68512440174599378677049263)
      ·
        refine ⟨102768660261899068015573895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68512440174599378677049263 102768660261899068015573895)
        ·
          refine ⟨154152990392848602023360843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 102768660261899068015573895 154152990392848602023360843)
          ·
            refine ⟨231229485589272903035041265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 154152990392848602023360843 231229485589272903035041265)
            ·
              refine ⟨173422114191954677276280949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 231229485589272903035041265 173422114191954677276280949)
              ·
                refine ⟨16258323205495750994651339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 173422114191954677276280949 16258323205495750994651339)
                ·
                  refine ⟨24387484808243626491977009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16258323205495750994651339 24387484808243626491977009)
                  ·
                    refine ⟨18290613606182719868982757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24387484808243626491977009 18290613606182719868982757)
                    ·
                      refine ⟨3429490051159259975434267, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18290613606182719868982757 3429490051159259975434267)
                      ·
                        rfl

theorem cell23_6678908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 2, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 2, 5, 1, 2, 4].length) (baseStart_6678908 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6678908 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6678908 prefixEnd_6678908 := by exact prefixLift 6678908
  have htrace : WordTrace (prefixWord ++ tailWord_6678908) baseStart_6678908 baseEnd_6678908 := by
    simpa [prefixWord, tailWord_6678908, baseEnd_6678908] using wordTrace_append hprefix tailTrace_6678908
  have hstable : (prefixWord ++ tailWord_6678908).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6678908).length < 2 ^ (prefixWord ++ tailWord_6678908).sum := by decide
  have hdescent : baseEnd_6678908 < baseStart_6678908 := by decide
  rcases family_descends (prefixWord ++ tailWord_6678908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6678911 : List Nat := [1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 7]
def baseStart_6678911 : Nat := 118140960795 + 6678911 * 2 ^ 59
def prefixEnd_6678911 : Nat := 4983230072969 + 3 ^ 40 * 6678911 * 2
def baseEnd_6678911 : Nat := 3429491591601223463696753

theorem tailTrace_6678911 : CollatzResearch.WordTrace tailWord_6678911 prefixEnd_6678911 3429491591601223463696753 := by
  unfold tailWord_6678911
  simp only [CollatzResearch.WordTrace]
  refine ⟨243599896706453589030756587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162399931137635726020504391 243599896706453589030756587)
  ·
    refine ⟨365399845059680383546134881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 243599896706453589030756587 365399845059680383546134881)
    ·
      refine ⟨274049883794760287659601161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 365399845059680383546134881 274049883794760287659601161)
      ·
        refine ⟨205537412846070215744700871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 274049883794760287659601161 205537412846070215744700871)
        ·
          refine ⟨308306119269105323617051307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 205537412846070215744700871 308306119269105323617051307)
          ·
            refine ⟨462459178903657985425576961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 308306119269105323617051307 462459178903657985425576961)
            ·
              refine ⟨346844384177743489069182721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 462459178903657985425576961 346844384177743489069182721)
              ·
                refine ⟨260133288133307616801887041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 346844384177743489069182721 260133288133307616801887041)
                ·
                  refine ⟨195099966099980712601415281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 260133288133307616801887041 195099966099980712601415281)
                  ·
                    refine ⟨146324974574985534451061461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 195099966099980712601415281 146324974574985534451061461)
                    ·
                      refine ⟨3429491591601223463696753, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 146324974574985534451061461 3429491591601223463696753)
                      ·
                        rfl

theorem cell23_6678911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 7].length) (baseStart_6678911 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6678911 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6678911 prefixEnd_6678911 := by exact prefixLift 6678911
  have htrace : WordTrace (prefixWord ++ tailWord_6678911) baseStart_6678911 baseEnd_6678911 := by
    simpa [prefixWord, tailWord_6678911, baseEnd_6678911] using wordTrace_append hprefix tailTrace_6678911
  have hstable : (prefixWord ++ tailWord_6678911).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6678911).length < 2 ^ (prefixWord ++ tailWord_6678911).sum := by decide
  have hdescent : baseEnd_6678911 < baseStart_6678911 := by decide
  rcases family_descends (prefixWord ++ tailWord_6678911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6678932 : List Nat := [2, 4, 2, 1, 3, 1, 2, 1, 1, 1, 5]
def baseStart_6678932 : Nat := 118140960795 + 6678932 * 2 ^ 59
def prefixEnd_6678932 : Nat := 4983230072969 + 3 ^ 40 * 6678932 * 2
def baseEnd_6678932 : Nat := 3429502374694967881534157

theorem tailTrace_6678932 : CollatzResearch.WordTrace tailWord_6678932 prefixEnd_6678932 3429502374694967881534157 := by
  unfold tailWord_6678932
  simp only [CollatzResearch.WordTrace]
  refine ⟨121800331319688754808635525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 162400441759585006411514033 121800331319688754808635525)
  ·
    refine ⟨22837562122441641526619161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 121800331319688754808635525 22837562122441641526619161)
    ·
      refine ⟨17128171591831231144964371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22837562122441641526619161 17128171591831231144964371)
      ·
        refine ⟨25692257387746846717446557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17128171591831231144964371 25692257387746846717446557)
        ·
          refine ⟨9634596520405067519042459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25692257387746846717446557 9634596520405067519042459)
          ·
            refine ⟨14451894780607601278563689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9634596520405067519042459 14451894780607601278563689)
            ·
              refine ⟨10838921085455700958922767, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14451894780607601278563689 10838921085455700958922767)
              ·
                refine ⟨16258381628183551438384151, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10838921085455700958922767 16258381628183551438384151)
                ·
                  refine ⟨24387572442275327157576227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16258381628183551438384151 24387572442275327157576227)
                  ·
                    refine ⟨36581358663412990736364341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24387572442275327157576227 36581358663412990736364341)
                    ·
                      refine ⟨3429502374694967881534157, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36581358663412990736364341 3429502374694967881534157)
                      ·
                        rfl

theorem cell23_6678932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 3, 1, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 3, 1, 2, 1, 1, 1, 5].length) (baseStart_6678932 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6678932 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6678932 prefixEnd_6678932 := by exact prefixLift 6678932
  have htrace : WordTrace (prefixWord ++ tailWord_6678932) baseStart_6678932 baseEnd_6678932 := by
    simpa [prefixWord, tailWord_6678932, baseEnd_6678932] using wordTrace_append hprefix tailTrace_6678932
  have hstable : (prefixWord ++ tailWord_6678932).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6678932).length < 2 ^ (prefixWord ++ tailWord_6678932).sum := by decide
  have hdescent : baseEnd_6678932 < baseStart_6678932 := by decide
  rcases family_descends (prefixWord ++ tailWord_6678932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6678962 : List Nat := [3, 2, 1, 1, 1, 1, 5, 3, 2, 1, 3]
def baseStart_6678962 : Nat := 118140960795 + 6678962 * 2 ^ 59
def prefixEnd_6678962 : Nat := 4983230072969 + 3 ^ 40 * 6678962 * 2
def baseEnd_6678962 : Nat := 3429517779114602764159019

theorem tailTrace_6678962 : CollatzResearch.WordTrace tailWord_6678962 prefixEnd_6678962 3429517779114602764159019 := by
  unfold tailWord_6678962
  simp only [CollatzResearch.WordTrace]
  refine ⟨60900439207317206185215785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 162401171219512549827242093 60900439207317206185215785)
  ·
    refine ⟨45675329405487904638911839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60900439207317206185215785 45675329405487904638911839)
    ·
      refine ⟨68512994108231856958367759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45675329405487904638911839 68512994108231856958367759)
      ·
        refine ⟨102769491162347785437551639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68512994108231856958367759 102769491162347785437551639)
        ·
          refine ⟨154154236743521678156327459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 102769491162347785437551639 154154236743521678156327459)
          ·
            refine ⟨231231355115282517234491189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 154154236743521678156327459 231231355115282517234491189)
            ·
              refine ⟨21677939542057735990733549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 231231355115282517234491189 21677939542057735990733549)
              ·
                refine ⟨8129227328271650996525081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21677939542057735990733549 8129227328271650996525081)
                ·
                  refine ⟨6096920496203738247393811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8129227328271650996525081 6096920496203738247393811)
                  ·
                    refine ⟨9145380744305607371090717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6096920496203738247393811 9145380744305607371090717)
                    ·
                      refine ⟨3429517779114602764159019, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9145380744305607371090717 3429517779114602764159019)
                      ·
                        rfl

theorem cell23_6678962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 5, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 5, 3, 2, 1, 3].length) (baseStart_6678962 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6678962 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6678962 prefixEnd_6678962 := by exact prefixLift 6678962
  have htrace : WordTrace (prefixWord ++ tailWord_6678962) baseStart_6678962 baseEnd_6678962 := by
    simpa [prefixWord, tailWord_6678962, baseEnd_6678962] using wordTrace_append hprefix tailTrace_6678962
  have hstable : (prefixWord ++ tailWord_6678962).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6678962).length < 2 ^ (prefixWord ++ tailWord_6678962).sum := by decide
  have hdescent : baseEnd_6678962 < baseStart_6678962 := by decide
  rcases family_descends (prefixWord ++ tailWord_6678962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6678985 : List Nat := [1, 2, 1, 1, 2, 1, 5, 1, 3, 4, 2]
def baseStart_6678985 : Nat := 118140960795 + 6678985 * 2 ^ 59
def prefixEnd_6678985 : Nat := 4983230072969 + 3 ^ 40 * 6678985 * 2
def baseEnd_6678985 : Nat := 3429529589169656174171413

theorem tailTrace_6678985 : CollatzResearch.WordTrace tailWord_6678985 prefixEnd_6678985 3429529589169656174171413 := by
  unfold tailWord_6678985
  simp only [CollatzResearch.WordTrace]
  refine ⟨243602595708185499668950409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162401730472123666445966939 243602595708185499668950409)
  ·
    refine ⟨182701946781139124751712807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 243602595708185499668950409 182701946781139124751712807)
    ·
      refine ⟨274052920171708687127569211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 182701946781139124751712807 274052920171708687127569211)
      ·
        refine ⟨411079380257563030691353817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 274052920171708687127569211 411079380257563030691353817)
        ·
          refine ⟨308309535193172273018515363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 411079380257563030691353817 308309535193172273018515363)
          ·
            refine ⟨462464302789758409527773045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 308309535193172273018515363 462464302789758409527773045)
            ·
              refine ⟨43356028386539850893228723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 462464302789758409527773045 43356028386539850893228723)
              ·
                refine ⟨65034042579809776339843085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43356028386539850893228723 65034042579809776339843085)
                ·
                  refine ⟨24387765967428666127441157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 65034042579809776339843085 24387765967428666127441157)
                  ·
                    refine ⟨4572706118892874898895217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24387765967428666127441157 4572706118892874898895217)
                    ·
                      refine ⟨3429529589169656174171413, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4572706118892874898895217 3429529589169656174171413)
                      ·
                        rfl

theorem cell23_6678985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 5, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 5, 1, 3, 4, 2].length) (baseStart_6678985 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6678985 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6678985 prefixEnd_6678985 := by exact prefixLift 6678985
  have htrace : WordTrace (prefixWord ++ tailWord_6678985) baseStart_6678985 baseEnd_6678985 := by
    simpa [prefixWord, tailWord_6678985, baseEnd_6678985] using wordTrace_append hprefix tailTrace_6678985
  have hstable : (prefixWord ++ tailWord_6678985).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6678985).length < 2 ^ (prefixWord ++ tailWord_6678985).sum := by decide
  have hdescent : baseEnd_6678985 < baseStart_6678985 := by decide
  rcases family_descends (prefixWord ++ tailWord_6678985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6679005 : List Nat := [1, 4, 3, 1, 1, 1, 1, 1, 1, 6, 3]
def baseStart_6679005 : Nat := 118140960795 + 6679005 * 2 ^ 59
def prefixEnd_6679005 : Nat := 4983230072969 + 3 ^ 40 * 6679005 * 2
def baseEnd_6679005 : Nat := 3429539858782746095921321

theorem tailTrace_6679005 : CollatzResearch.WordTrace tailWord_6679005 prefixEnd_6679005 3429539858782746095921321 := by
  unfold tailWord_6679005
  simp only [CollatzResearch.WordTrace]
  refine ⟨243603325168113043084678469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162402216778742028723118979 243603325168113043084678469)
  ·
    refine ⟨45675623469021195578377213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 243603325168113043084678469 45675623469021195578377213)
    ·
      refine ⟨17128358800882948341891455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 45675623469021195578377213 17128358800882948341891455)
      ·
        refine ⟨25692538201324422512837183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17128358800882948341891455 25692538201324422512837183)
        ·
          refine ⟨38538807301986633769255775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25692538201324422512837183 38538807301986633769255775)
          ·
            refine ⟨57808210952979950653883663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38538807301986633769255775 57808210952979950653883663)
            ·
              refine ⟨86712316429469925980825495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57808210952979950653883663 86712316429469925980825495)
              ·
                refine ⟨130068474644204888971238243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 86712316429469925980825495 130068474644204888971238243)
                ·
                  refine ⟨195102711966307333456857365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 130068474644204888971238243 195102711966307333456857365)
                  ·
                    refine ⟨9145439623420656255790189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 195102711966307333456857365 9145439623420656255790189)
                    ·
                      refine ⟨3429539858782746095921321, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9145439623420656255790189 3429539858782746095921321)
                      ·
                        rfl

theorem cell23_6679005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 1, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 1, 1, 1, 6, 3].length) (baseStart_6679005 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6679005 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6679005 prefixEnd_6679005 := by exact prefixLift 6679005
  have htrace : WordTrace (prefixWord ++ tailWord_6679005) baseStart_6679005 baseEnd_6679005 := by
    simpa [prefixWord, tailWord_6679005, baseEnd_6679005] using wordTrace_append hprefix tailTrace_6679005
  have hstable : (prefixWord ++ tailWord_6679005).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6679005).length < 2 ^ (prefixWord ++ tailWord_6679005).sum := by decide
  have hdescent : baseEnd_6679005 < baseStart_6679005 := by decide
  rcases family_descends (prefixWord ++ tailWord_6679005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6679008 : List Nat := [2, 1, 1, 3, 1, 1, 4, 3, 7]
def baseStart_6679008 : Nat := 118140960795 + 6679008 * 2 ^ 59
def prefixEnd_6679008 : Nat := 4983230072969 + 3 ^ 40 * 6679008 * 2
def baseEnd_6679008 : Nat := 381060155469412176020423

theorem tailTrace_6679008 : CollatzResearch.WordTrace tailWord_6679008 prefixEnd_6679008 381060155469412176020423 := by
  unfold tailWord_6679008
  simp only [CollatzResearch.WordTrace]
  refine ⟨121801717293551087298518839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 162402289724734783064691785 121801717293551087298518839)
  ·
    refine ⟨182702575940326630947778259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121801717293551087298518839 182702575940326630947778259)
    ·
      refine ⟨274053863910489946421667389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 182702575940326630947778259 274053863910489946421667389)
      ·
        refine ⟨102770198966433729908125271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 274053863910489946421667389 102770198966433729908125271)
        ·
          refine ⟨154155298449650594862187907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 102770198966433729908125271 154155298449650594862187907)
          ·
            refine ⟨231232947674475892293281861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 154155298449650594862187907 231232947674475892293281861)
            ·
              refine ⟨43356177688964229804990349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 231232947674475892293281861 43356177688964229804990349)
              ·
                refine ⟨16258566633361586176871381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 43356177688964229804990349 16258566633361586176871381)
                ·
                  refine ⟨381060155469412176020423, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16258566633361586176871381 381060155469412176020423)
                  ·
                    rfl

theorem cell23_6679008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 4, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 4, 3, 7].length) (baseStart_6679008 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6679008 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6679008 prefixEnd_6679008 := by exact prefixLift 6679008
  have htrace : WordTrace (prefixWord ++ tailWord_6679008) baseStart_6679008 baseEnd_6679008 := by
    simpa [prefixWord, tailWord_6679008, baseEnd_6679008] using wordTrace_append hprefix tailTrace_6679008
  have hstable : (prefixWord ++ tailWord_6679008).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6679008).length < 2 ^ (prefixWord ++ tailWord_6679008).sum := by decide
  have hdescent : baseEnd_6679008 < baseStart_6679008 := by decide
  rcases family_descends (prefixWord ++ tailWord_6679008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6679015 : List Nat := [1, 1, 5, 2, 1, 1, 3, 1, 2, 2, 4]
def baseStart_6679015 : Nat := 118140960795 + 6679015 * 2 ^ 59
def prefixEnd_6679015 : Nat := 4983230072969 + 3 ^ 40 * 6679015 * 2
def baseEnd_6679015 : Nat := 3429544993589291056796275

theorem tailTrace_6679015 : CollatzResearch.WordTrace tailWord_6679015 prefixEnd_6679015 3429544993589291056796275 := by
  unfold tailWord_6679015
  simp only [CollatzResearch.WordTrace]
  refine ⟨243603689898076814792542499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162402459932051209861694999 243603689898076814792542499)
  ·
    refine ⟨365405534847115222188813749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 243603689898076814792542499 365405534847115222188813749)
    ·
      refine ⟨34256768891917052080201289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 365405534847115222188813749 34256768891917052080201289)
      ·
        refine ⟨25692576668937789060150967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34256768891917052080201289 25692576668937789060150967)
        ·
          refine ⟨38538865003406683590226451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25692576668937789060150967 38538865003406683590226451)
          ·
            refine ⟨57808297505110025385339677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38538865003406683590226451 57808297505110025385339677)
            ·
              refine ⟨21678111564416259519502379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 57808297505110025385339677 21678111564416259519502379)
              ·
                refine ⟨32517167346624389279253569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21678111564416259519502379 32517167346624389279253569)
                ·
                  refine ⟨24387875509968291959440177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32517167346624389279253569 24387875509968291959440177)
                  ·
                    refine ⟨18290906632476218969580133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24387875509968291959440177 18290906632476218969580133)
                    ·
                      refine ⟨3429544993589291056796275, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18290906632476218969580133 3429544993589291056796275)
                      ·
                        rfl

theorem cell23_6679015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 3, 1, 2, 2, 4].length) (baseStart_6679015 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6679015 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6679015 prefixEnd_6679015 := by exact prefixLift 6679015
  have htrace : WordTrace (prefixWord ++ tailWord_6679015) baseStart_6679015 baseEnd_6679015 := by
    simpa [prefixWord, tailWord_6679015, baseEnd_6679015] using wordTrace_append hprefix tailTrace_6679015
  have hstable : (prefixWord ++ tailWord_6679015).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6679015).length < 2 ^ (prefixWord ++ tailWord_6679015).sum := by decide
  have hdescent : baseEnd_6679015 < baseStart_6679015 := by decide
  rcases family_descends (prefixWord ++ tailWord_6679015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6679053 : List Nat := [1, 7, 1, 1, 1, 2, 1, 1, 4, 2, 2]
def baseStart_6679053 : Nat := 118140960795 + 6679053 * 2 ^ 59
def prefixEnd_6679053 : Nat := 4983230072969 + 3 ^ 40 * 6679053 * 2
def baseEnd_6679053 : Nat := 3429564505854161908121101

theorem tailTrace_6679053 : CollatzResearch.WordTrace tailWord_6679053 prefixEnd_6679053 3429564505854161908121101 := by
  unfold tailWord_6679053
  simp only [CollatzResearch.WordTrace]
  refine ⟨243605075871939147282425813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162403383914626098188283875 243605075871939147282425813)
  ·
    refine ⟨5709493965748573764431855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 243605075871939147282425813 5709493965748573764431855)
    ·
      refine ⟨8564240948622860646647783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5709493965748573764431855 8564240948622860646647783)
      ·
        refine ⟨12846361422934290969971675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8564240948622860646647783 12846361422934290969971675)
        ·
          refine ⟨19269542134401436454957513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12846361422934290969971675 19269542134401436454957513)
          ·
            refine ⟨14452156600801077341218135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19269542134401436454957513 14452156600801077341218135)
            ·
              refine ⟨21678234901201616011827203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14452156600801077341218135 21678234901201616011827203)
              ·
                refine ⟨32517352351802424017740805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21678234901201616011827203 32517352351802424017740805)
                ·
                  refine ⟨6097003565962954503326401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 32517352351802424017740805 6097003565962954503326401)
                  ·
                    refine ⟨4572752674472215877494801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6097003565962954503326401 4572752674472215877494801)
                    ·
                      refine ⟨3429564505854161908121101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4572752674472215877494801 3429564505854161908121101)
                      ·
                        rfl

theorem cell23_6679053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 2, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 2, 1, 1, 4, 2, 2].length) (baseStart_6679053 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6679053 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6679053 prefixEnd_6679053 := by exact prefixLift 6679053
  have htrace : WordTrace (prefixWord ++ tailWord_6679053) baseStart_6679053 baseEnd_6679053 := by
    simpa [prefixWord, tailWord_6679053, baseEnd_6679053] using wordTrace_append hprefix tailTrace_6679053
  have hstable : (prefixWord ++ tailWord_6679053).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6679053).length < 2 ^ (prefixWord ++ tailWord_6679053).sum := by decide
  have hdescent : baseEnd_6679053 < baseStart_6679053 := by decide
  rcases family_descends (prefixWord ++ tailWord_6679053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6679075 : List Nat := [1, 1, 1, 4, 4, 1, 1, 2, 1, 3, 4]
def baseStart_6679075 : Nat := 118140960795 + 6679075 * 2 ^ 59
def prefixEnd_6679075 : Nat := 4983230072969 + 3 ^ 40 * 6679075 * 2
def baseEnd_6679075 : Nat := 3429575802428560822045999

theorem tailTrace_6679075 : CollatzResearch.WordTrace tailWord_6679075 prefixEnd_6679075 3429575802428560822045999 := by
  unfold tailWord_6679075
  simp only [CollatzResearch.WordTrace]
  refine ⟨243605878277859445039726679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162403918851906296693151119 243605878277859445039726679)
  ·
    refine ⟨365408817416789167559590019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 243605878277859445039726679 365408817416789167559590019)
    ·
      refine ⟨548113226125183751339385029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 365408817416789167559590019 548113226125183751339385029)
      ·
        refine ⟨102771229898471953376134693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 548113226125183751339385029 102771229898471953376134693)
        ·
          refine ⟨19269605605963491258025255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 102771229898471953376134693 19269605605963491258025255)
          ·
            refine ⟨28904408408945236887037883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19269605605963491258025255 28904408408945236887037883)
            ·
              refine ⟨43356612613417855330556825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28904408408945236887037883 43356612613417855330556825)
              ·
                refine ⟨32517459460063391497917619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43356612613417855330556825 32517459460063391497917619)
                ·
                  refine ⟨48776189190095087246876429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32517459460063391497917619 48776189190095087246876429)
                  ·
                    refine ⟨18291070946285657717578661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 48776189190095087246876429 18291070946285657717578661)
                    ·
                      refine ⟨3429575802428560822045999, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18291070946285657717578661 3429575802428560822045999)
                      ·
                        rfl

theorem cell23_6679075_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 1, 2, 1, 3, 4].length) (baseStart_6679075 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6679075 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6679075 prefixEnd_6679075 := by exact prefixLift 6679075
  have htrace : WordTrace (prefixWord ++ tailWord_6679075) baseStart_6679075 baseEnd_6679075 := by
    simpa [prefixWord, tailWord_6679075, baseEnd_6679075] using wordTrace_append hprefix tailTrace_6679075
  have hstable : (prefixWord ++ tailWord_6679075).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6679075).length < 2 ^ (prefixWord ++ tailWord_6679075).sum := by decide
  have hdescent : baseEnd_6679075 < baseStart_6679075 := by decide
  rcases family_descends (prefixWord ++ tailWord_6679075) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6679095 : List Nat := [1, 1, 3, 1, 2, 3, 1, 3, 1, 4, 3]
def baseStart_6679095 : Nat := 118140960795 + 6679095 * 2 ^ 59
def prefixEnd_6679095 : Nat := 4983230072969 + 3 ^ 40 * 6679095 * 2
def baseEnd_6679095 : Nat := 3429586072041650743795907

theorem tailTrace_6679095 : CollatzResearch.WordTrace tailWord_6679095 prefixEnd_6679095 3429586072041650743795907 := by
  unfold tailWord_6679095
  simp only [CollatzResearch.WordTrace]
  refine ⟨243606607737786988455454739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162404405158524658970303159 243606607737786988455454739)
  ·
    refine ⟨365409911606680482683182109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 243606607737786988455454739 365409911606680482683182109)
    ·
      refine ⟨137028716852505181006193291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 365409911606680482683182109 137028716852505181006193291)
      ·
        refine ⟨205543075278757771509289937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 137028716852505181006193291 205543075278757771509289937)
        ·
          refine ⟨154157306459068328631967453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 205543075278757771509289937 154157306459068328631967453)
          ·
            refine ⟨57808989922150623236987795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 154157306459068328631967453 57808989922150623236987795)
            ·
              refine ⟨86713484883225934855481693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57808989922150623236987795 86713484883225934855481693)
              ·
                refine ⟨32517556831209725570805635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 86713484883225934855481693 32517556831209725570805635)
                ·
                  refine ⟨48776335246814588356208453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32517556831209725570805635 48776335246814588356208453)
                  ·
                    refine ⟨9145562858777735316789085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 48776335246814588356208453 9145562858777735316789085)
                    ·
                      refine ⟨3429586072041650743795907, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9145562858777735316789085 3429586072041650743795907)
                      ·
                        rfl

theorem cell23_6679095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 1, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 1, 3, 1, 4, 3].length) (baseStart_6679095 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6679095 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6679095 prefixEnd_6679095 := by exact prefixLift 6679095
  have htrace : WordTrace (prefixWord ++ tailWord_6679095) baseStart_6679095 baseEnd_6679095 := by
    simpa [prefixWord, tailWord_6679095, baseEnd_6679095] using wordTrace_append hprefix tailTrace_6679095
  have hstable : (prefixWord ++ tailWord_6679095).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6679095).length < 2 ^ (prefixWord ++ tailWord_6679095).sum := by decide
  have hdescent : baseEnd_6679095 < baseStart_6679095 := by decide
  rcases family_descends (prefixWord ++ tailWord_6679095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6679169 : List Nat := [1, 2, 4, 2, 1, 1, 1, 4, 2, 3, 2]
def baseStart_6679169 : Nat := 118140960795 + 6679169 * 2 ^ 59
def prefixEnd_6679169 : Nat := 4983230072969 + 3 ^ 40 * 6679169 * 2
def baseEnd_6679169 : Nat := 3429624069610083454270567

theorem tailTrace_6679169 : CollatzResearch.WordTrace tailWord_6679169 prefixEnd_6679169 3429624069610083454270567 := by
  unfold tailWord_6679169
  simp only [CollatzResearch.WordTrace]
  refine ⟨243609306739518899093648561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162406204493012599395765707 243609306739518899093648561)
  ·
    refine ⟨182706980054639174320236421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 243609306739518899093648561 182706980054639174320236421)
    ·
      refine ⟨34257558760244845185044329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 182706980054639174320236421 34257558760244845185044329)
      ·
        refine ⟨25693169070183633888783247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34257558760244845185044329 25693169070183633888783247)
        ·
          refine ⟨38539753605275450833174871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25693169070183633888783247 38539753605275450833174871)
          ·
            refine ⟨57809630407913176249762307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38539753605275450833174871 57809630407913176249762307)
            ·
              refine ⟨86714445611869764374643461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57809630407913176249762307 86714445611869764374643461)
              ·
                refine ⟨16258958552225580820245649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 86714445611869764374643461 16258958552225580820245649)
                ·
                  refine ⟨12194218914169185615184237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16258958552225580820245649 12194218914169185615184237)
                  ·
                    refine ⟨4572832092813444605694089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12194218914169185615184237 4572832092813444605694089)
                    ·
                      refine ⟨3429624069610083454270567, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4572832092813444605694089 3429624069610083454270567)
                      ·
                        rfl

theorem cell23_6679169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 1, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 1, 4, 2, 3, 2].length) (baseStart_6679169 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6679169 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6679169 prefixEnd_6679169 := by exact prefixLift 6679169
  have htrace : WordTrace (prefixWord ++ tailWord_6679169) baseStart_6679169 baseEnd_6679169 := by
    simpa [prefixWord, tailWord_6679169, baseEnd_6679169] using wordTrace_append hprefix tailTrace_6679169
  have hstable : (prefixWord ++ tailWord_6679169).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6679169).length < 2 ^ (prefixWord ++ tailWord_6679169).sum := by decide
  have hdescent : baseEnd_6679169 < baseStart_6679169 := by decide
  rcases family_descends (prefixWord ++ tailWord_6679169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6679175 : List Nat := [1, 1, 4, 2, 1, 2, 1, 2, 3, 6]
def baseStart_6679175 : Nat := 118140960795 + 6679175 * 2 ^ 59
def prefixEnd_6679175 : Nat := 4983230072969 + 3 ^ 40 * 6679175 * 2
def baseEnd_6679175 : Nat := 1143209050164670143598513

theorem tailTrace_6679175 : CollatzResearch.WordTrace tailWord_6679175 prefixEnd_6679175 1143209050164670143598513 := by
  unfold tailWord_6679175
  simp only [CollatzResearch.WordTrace]
  refine ⟨243609525577497162118366979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162406350384998108078911319 243609525577497162118366979)
  ·
    refine ⟨365414288366245743177550469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 243609525577497162118366979 365414288366245743177550469)
    ·
      refine ⟨68515179068671076845790713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 365414288366245743177550469 68515179068671076845790713)
      ·
        refine ⟨51386384301503307634343035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68515179068671076845790713 51386384301503307634343035)
        ·
          refine ⟨77079576452254961451514553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51386384301503307634343035 77079576452254961451514553)
          ·
            refine ⟨57809682339191221088635915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 77079576452254961451514553 57809682339191221088635915)
            ·
              refine ⟨86714523508786831632953873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57809682339191221088635915 86714523508786831632953873)
              ·
                refine ⟨65035892631590123724715405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 86714523508786831632953873 65035892631590123724715405)
                ·
                  refine ⟨24388459736846296396768277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 65035892631590123724715405 24388459736846296396768277)
                  ·
                    refine ⟨1143209050164670143598513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24388459736846296396768277 1143209050164670143598513)
                    ·
                      rfl

theorem cell23_6679175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 1, 2, 3, 6].length) (baseStart_6679175 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6679175 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6679175 prefixEnd_6679175 := by exact prefixLift 6679175
  have htrace : WordTrace (prefixWord ++ tailWord_6679175) baseStart_6679175 baseEnd_6679175 := by
    simpa [prefixWord, tailWord_6679175, baseEnd_6679175] using wordTrace_append hprefix tailTrace_6679175
  have hstable : (prefixWord ++ tailWord_6679175).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6679175).length < 2 ^ (prefixWord ++ tailWord_6679175).sum := by decide
  have hdescent : baseEnd_6679175 < baseStart_6679175 := by decide
  rcases family_descends (prefixWord ++ tailWord_6679175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6679182 : List Nat := [4, 1, 1, 3, 1, 1, 1, 1, 5, 1, 4]
def baseStart_6679182 : Nat := 118140960795 + 6679182 * 2 ^ 59
def prefixEnd_6679182 : Nat := 4983230072969 + 3 ^ 40 * 6679182 * 2
def baseEnd_6679182 : Nat := 3429630744858591903408007

theorem tailTrace_6679182 : CollatzResearch.WordTrace tailWord_6679182 prefixEnd_6679182 3429630744858591903408007 := by
  unfold tailWord_6679182
  simp only [CollatzResearch.WordTrace]
  refine ⟨30451222611058975289233975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 162406520592314534875914533 30451222611058975289233975)
  ·
    refine ⟨45676833916588462933850963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30451222611058975289233975 45676833916588462933850963)
    ·
      refine ⟨68515250874882694400776445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45676833916588462933850963 68515250874882694400776445)
      ·
        refine ⟨25693219078081010400291167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 68515250874882694400776445 25693219078081010400291167)
        ·
          refine ⟨38539828617121515600436751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25693219078081010400291167 38539828617121515600436751)
          ·
            refine ⟨57809742925682273400655127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38539828617121515600436751 57809742925682273400655127)
            ·
              refine ⟨86714614388523410100982691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57809742925682273400655127 86714614388523410100982691)
              ·
                refine ⟨130071921582785115151474037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 86714614388523410100982691 130071921582785115151474037)
                ·
                  refine ⟨12194242648386104545450691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 130071921582785115151474037 12194242648386104545450691)
                  ·
                    refine ⟨18291363972579156818176037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12194242648386104545450691 18291363972579156818176037)
                    ·
                      refine ⟨3429630744858591903408007, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18291363972579156818176037 3429630744858591903408007)
                      ·
                        rfl

theorem cell23_6679182_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 1, 1, 5, 1, 4].length) (baseStart_6679182 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6679182 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6679182 prefixEnd_6679182 := by exact prefixLift 6679182
  have htrace : WordTrace (prefixWord ++ tailWord_6679182) baseStart_6679182 baseEnd_6679182 := by
    simpa [prefixWord, tailWord_6679182, baseEnd_6679182] using wordTrace_append hprefix tailTrace_6679182
  have hstable : (prefixWord ++ tailWord_6679182).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6679182).length < 2 ^ (prefixWord ++ tailWord_6679182).sum := by decide
  have hdescent : baseEnd_6679182 < baseStart_6679182 := by decide
  rcases family_descends (prefixWord ++ tailWord_6679182) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6679192 : List Nat := [2, 1, 2, 4, 1, 1, 4, 1, 1, 6]
def baseStart_6679192 : Nat := 118140960795 + 6679192 * 2 ^ 59
def prefixEnd_6679192 : Nat := 4983230072969 + 3 ^ 40 * 6679192 * 2
def baseEnd_6679192 : Nat := 1143211959888378954760987

theorem tailTrace_6679192 : CollatzResearch.WordTrace tailWord_6679192 prefixEnd_6679192 1143211959888378954760987 := by
  unfold tailWord_6679192
  simp only [CollatzResearch.WordTrace]
  refine ⟨121805072809217787010867915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 162406763745623716014490553 121805072809217787010867915)
  ·
    refine ⟨182707609213826680516301873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121805072809217787010867915 182707609213826680516301873)
    ·
      refine ⟨137030706910370010387226405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 182707609213826680516301873 137030706910370010387226405)
      ·
        refine ⟨25693257545694376947604951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 137030706910370010387226405 25693257545694376947604951)
        ·
          refine ⟨38539886318541565421407427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25693257545694376947604951 38539886318541565421407427)
          ·
            refine ⟨57809829477812348132111141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38539886318541565421407427 57809829477812348132111141)
            ·
              refine ⟨10839343027089815274770839, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 57809829477812348132111141 10839343027089815274770839)
              ·
                refine ⟨16259014540634722912156259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10839343027089815274770839 16259014540634722912156259)
                ·
                  refine ⟨24388521810952084368234389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16259014540634722912156259 24388521810952084368234389)
                  ·
                    refine ⟨1143211959888378954760987, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24388521810952084368234389 1143211959888378954760987)
                    ·
                      rfl

theorem cell23_6679192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 4, 1, 1, 6].length) (baseStart_6679192 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6679192 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6679192 prefixEnd_6679192 := by exact prefixLift 6679192
  have htrace : WordTrace (prefixWord ++ tailWord_6679192) baseStart_6679192 baseEnd_6679192 := by
    simpa [prefixWord, tailWord_6679192, baseEnd_6679192] using wordTrace_append hprefix tailTrace_6679192
  have hstable : (prefixWord ++ tailWord_6679192).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6679192).length < 2 ^ (prefixWord ++ tailWord_6679192).sum := by decide
  have hdescent : baseEnd_6679192 < baseStart_6679192 := by decide
  rcases family_descends (prefixWord ++ tailWord_6679192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6679219 : List Nat := [1, 1, 1, 2, 3, 5, 1, 3, 1, 2, 3]
def baseStart_6679219 : Nat := 118140960795 + 6679219 * 2 ^ 59
def prefixEnd_6679219 : Nat := 4983230072969 + 3 ^ 40 * 6679219 * 2
def baseEnd_6679219 : Nat := 3429649743642808258645337

theorem tailTrace_6679219 : CollatzResearch.WordTrace tailWord_6679219 prefixEnd_6679219 3429649743642808258645337 := by
  unfold tailWord_6679219
  simp only [CollatzResearch.WordTrace]
  refine ⟨243611130389337757632968711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162407420259558505088645807 243611130389337757632968711)
  ·
    refine ⟨365416695584006636449453067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 243611130389337757632968711 365416695584006636449453067)
    ·
      refine ⟨548125043376009954674179601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 365416695584006636449453067 548125043376009954674179601)
      ·
        refine ⟨411093782532007466005634701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 548125043376009954674179601 411093782532007466005634701)
        ·
          refine ⟨154160168449502799752113013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 411093782532007466005634701 154160168449502799752113013)
          ·
            refine ⟨14452515792140887476760595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 154160168449502799752113013 14452515792140887476760595)
            ·
              refine ⟨21678773688211331215140893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14452515792140887476760595 21678773688211331215140893)
              ·
                refine ⟨8129540133079249205677835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21678773688211331215140893 8129540133079249205677835)
                ·
                  refine ⟨12194310199618873808516753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8129540133079249205677835 12194310199618873808516753)
                  ·
                    refine ⟨9145732649714155356387565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12194310199618873808516753 9145732649714155356387565)
                    ·
                      refine ⟨3429649743642808258645337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9145732649714155356387565 3429649743642808258645337)
                      ·
                        rfl

theorem cell23_6679219_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 5, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 5, 1, 3, 1, 2, 3].length) (baseStart_6679219 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6679219 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6679219 prefixEnd_6679219 := by exact prefixLift 6679219
  have htrace : WordTrace (prefixWord ++ tailWord_6679219) baseStart_6679219 baseEnd_6679219 := by
    simpa [prefixWord, tailWord_6679219, baseEnd_6679219] using wordTrace_append hprefix tailTrace_6679219
  have hstable : (prefixWord ++ tailWord_6679219).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6679219).length < 2 ^ (prefixWord ++ tailWord_6679219).sum := by decide
  have hdescent : baseEnd_6679219 < baseStart_6679219 := by decide
  rcases family_descends (prefixWord ++ tailWord_6679219) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6679225 : List Nat := [1, 2, 1, 4, 1, 1, 1, 2, 2, 2, 6]
def baseStart_6679225 : Nat := 118140960795 + 6679225 * 2 ^ 59
def prefixEnd_6679225 : Nat := 4983230072969 + 3 ^ 40 * 6679225 * 2
def baseEnd_6679225 : Nat := 3429652824526735235170309

theorem tailTrace_6679225 : CollatzResearch.WordTrace tailWord_6679225 prefixEnd_6679225 3429652824526735235170309 := by
  unfold tailWord_6679225
  simp only [CollatzResearch.WordTrace]
  refine ⟨243611349227316020657687129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162407566151544013771791419 243611349227316020657687129)
  ·
    refine ⟨182708511920487015493265347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 243611349227316020657687129 182708511920487015493265347)
    ·
      refine ⟨274062767880730523239898021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 182708511920487015493265347 274062767880730523239898021)
      ·
        refine ⟨51386768977636973107480879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 274062767880730523239898021 51386768977636973107480879)
        ·
          refine ⟨77080153466455459661221319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51386768977636973107480879 77080153466455459661221319)
          ·
            refine ⟨115620230199683189491831979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77080153466455459661221319 115620230199683189491831979)
            ·
              refine ⟨173430345299524784237747969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 115620230199683189491831979 173430345299524784237747969)
              ·
                refine ⟨130072758974643588178310977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 173430345299524784237747969 130072758974643588178310977)
                ·
                  refine ⟨97554569230982691133733233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 130072758974643588178310977 97554569230982691133733233)
                  ·
                    refine ⟨73165926923237018350299925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 97554569230982691133733233 73165926923237018350299925)
                    ·
                      refine ⟨3429652824526735235170309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 73165926923237018350299925 3429652824526735235170309)
                      ·
                        rfl

theorem cell23_6679225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 1, 2, 2, 2, 6].length) (baseStart_6679225 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6679225 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6679225 prefixEnd_6679225 := by exact prefixLift 6679225
  have htrace : WordTrace (prefixWord ++ tailWord_6679225) baseStart_6679225 baseEnd_6679225 := by
    simpa [prefixWord, tailWord_6679225, baseEnd_6679225] using wordTrace_append hprefix tailTrace_6679225
  have hstable : (prefixWord ++ tailWord_6679225).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6679225).length < 2 ^ (prefixWord ++ tailWord_6679225).sum := by decide
  have hdescent : baseEnd_6679225 < baseStart_6679225 := by decide
  rcases family_descends (prefixWord ++ tailWord_6679225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6679253 : List Nat := [1, 3, 2, 5, 1, 1, 2, 2, 1, 2, 3]
def baseStart_6679253 : Nat := 118140960795 + 6679253 * 2 ^ 59
def prefixEnd_6679253 : Nat := 4983230072969 + 3 ^ 40 * 6679253 * 2
def baseEnd_6679253 : Nat := 3429667201985061125620181

theorem tailTrace_6679253 : CollatzResearch.WordTrace tailWord_6679253 prefixEnd_6679253 3429667201985061125620181 := by
  unfold tailWord_6679253
  simp only [CollatzResearch.WordTrace]
  refine ⟨243612370471214581439706413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162408246980809720959804275 243612370471214581439706413)
  ·
    refine ⟨91354638926705468039889905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 243612370471214581439706413 91354638926705468039889905)
    ·
      refine ⟨68515979195029101029917429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 91354638926705468039889905 68515979195029101029917429)
      ·
        refine ⟨6423373049533978221554759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 68515979195029101029917429 6423373049533978221554759)
        ·
          refine ⟨9635059574300967332332139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6423373049533978221554759 9635059574300967332332139)
          ·
            refine ⟨14452589361451450998498209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9635059574300967332332139 14452589361451450998498209)
            ·
              refine ⟨10839442021088588248873657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14452589361451450998498209 10839442021088588248873657)
              ·
                refine ⟨8129581515816441186655243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10839442021088588248873657 8129581515816441186655243)
                ·
                  refine ⟨12194372273724661779982865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8129581515816441186655243 12194372273724661779982865)
                  ·
                    refine ⟨9145779205293496334987149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12194372273724661779982865 9145779205293496334987149)
                    ·
                      refine ⟨3429667201985061125620181, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9145779205293496334987149 3429667201985061125620181)
                      ·
                        rfl

theorem cell23_6679253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 1, 1, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 1, 1, 2, 2, 1, 2, 3].length) (baseStart_6679253 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6679253 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6679253 prefixEnd_6679253 := by exact prefixLift 6679253
  have htrace : WordTrace (prefixWord ++ tailWord_6679253) baseStart_6679253 baseEnd_6679253 := by
    simpa [prefixWord, tailWord_6679253, baseEnd_6679253] using wordTrace_append hprefix tailTrace_6679253
  have hstable : (prefixWord ++ tailWord_6679253).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6679253).length < 2 ^ (prefixWord ++ tailWord_6679253).sum := by decide
  have hdescent : baseEnd_6679253 < baseStart_6679253 := by decide
  rcases family_descends (prefixWord ++ tailWord_6679253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6679284 : List Nat := [2, 6, 1, 1, 3, 1, 1, 1, 3, 2, 2]
def baseStart_6679284 : Nat := 118140960795 + 6679284 * 2 ^ 59
def prefixEnd_6679284 : Nat := 4983230072969 + 3 ^ 40 * 6679284 * 2
def baseEnd_6679284 : Nat := 3429683119885350504332539

theorem tailTrace_6679284 : CollatzResearch.WordTrace tailWord_6679284 prefixEnd_6679284 3429683119885350504332539 := by
  unfold tailWord_6679284
  simp only [CollatzResearch.WordTrace]
  refine ⟨121806750567051136867042453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 162409000756068182489389937 121806750567051136867042453)
  ·
    refine ⟨5709691432830522040642615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 121806750567051136867042453 5709691432830522040642615)
    ·
      refine ⟨8564537149245783060963923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5709691432830522040642615 8564537149245783060963923)
      ·
        refine ⟨12846805723868674591445885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8564537149245783060963923 12846805723868674591445885)
        ·
          refine ⟨4817552146450752971792207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12846805723868674591445885 4817552146450752971792207)
          ·
            refine ⟨7226328219676129457688311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4817552146450752971792207 7226328219676129457688311)
            ·
              refine ⟨10839492329514194186532467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7226328219676129457688311 10839492329514194186532467)
              ·
                refine ⟨16259238494271291279798701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10839492329514194186532467 16259238494271291279798701)
                ·
                  refine ⟨6097214435351734229924513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16259238494271291279798701 6097214435351734229924513)
                  ·
                    refine ⟨4572910826513800672443385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6097214435351734229924513 4572910826513800672443385)
                    ·
                      refine ⟨3429683119885350504332539, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4572910826513800672443385 3429683119885350504332539)
                      ·
                        rfl

theorem cell23_6679284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 3, 1, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 3, 1, 1, 1, 3, 2, 2].length) (baseStart_6679284 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6679284 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6679284 prefixEnd_6679284 := by exact prefixLift 6679284
  have htrace : WordTrace (prefixWord ++ tailWord_6679284) baseStart_6679284 baseEnd_6679284 := by
    simpa [prefixWord, tailWord_6679284, baseEnd_6679284] using wordTrace_append hprefix tailTrace_6679284
  have hstable : (prefixWord ++ tailWord_6679284).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6679284).length < 2 ^ (prefixWord ++ tailWord_6679284).sum := by decide
  have hdescent : baseEnd_6679284 < baseStart_6679284 := by decide
  rcases family_descends (prefixWord ++ tailWord_6679284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6679329 : List Nat := [1, 2, 3, 2, 1, 2, 2, 5, 5]
def baseStart_6679329 : Nat := 118140960795 + 6679329 * 2 ^ 59
def prefixEnd_6679329 : Nat := 4983230072969 + 3 ^ 40 * 6679329 * 2
def baseEnd_6679329 : Nat := 381078469612755869807759

theorem tailTrace_6679329 : CollatzResearch.WordTrace tailWord_6679329 prefixEnd_6679329 381078469612755869807759 := by
  unfold tailWord_6679329
  simp only [CollatzResearch.WordTrace]
  refine ⟨243615142418939246419473041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162410094945959497612982027 243615142418939246419473041)
  ·
    refine ⟨182711356814204434814604781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 243615142418939246419473041 182711356814204434814604781)
    ·
      refine ⟨68516758805326663055476793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 182711356814204434814604781 68516758805326663055476793)
      ·
        refine ⟨51387569103994997291607595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68516758805326663055476793 51387569103994997291607595)
        ·
          refine ⟨77081353655992495937411393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51387569103994997291607595 77081353655992495937411393)
          ·
            refine ⟨57811015241994371953058545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 77081353655992495937411393 57811015241994371953058545)
            ·
              refine ⟨43358261431495778964793909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 57811015241994371953058545 43358261431495778964793909)
              ·
                refine ⟨4064837009202729277949429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 43358261431495778964793909 4064837009202729277949429)
                ·
                  refine ⟨381078469612755869807759, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4064837009202729277949429 381078469612755869807759)
                  ·
                    rfl

theorem cell23_6679329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 2, 5, 5].length) (baseStart_6679329 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6679329 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6679329 prefixEnd_6679329 := by exact prefixLift 6679329
  have htrace : WordTrace (prefixWord ++ tailWord_6679329) baseStart_6679329 baseEnd_6679329 := by
    simpa [prefixWord, tailWord_6679329, baseEnd_6679329] using wordTrace_append hprefix tailTrace_6679329
  have hstable : (prefixWord ++ tailWord_6679329).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6679329).length < 2 ^ (prefixWord ++ tailWord_6679329).sum := by decide
  have hdescent : baseEnd_6679329 < baseStart_6679329 := by decide
  rcases family_descends (prefixWord ++ tailWord_6679329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6679352 : List Nat := [2, 1, 2, 1, 3, 2, 1, 3, 1, 2, 5]
def baseStart_6679352 : Nat := 118140960795 + 6679352 * 2 ^ 59
def prefixEnd_6679352 : Nat := 4983230072969 + 3 ^ 40 * 6679352 * 2
def baseEnd_6679352 : Nat := 3429718036569856238282225

theorem tailTrace_6679352 : CollatzResearch.WordTrace tailWord_6679352 prefixEnd_6679352 3429718036569856238282225 := by
  unfold tailWord_6679352
  simp only [CollatzResearch.WordTrace]
  refine ⟨121807990648927960673780155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 162410654198570614231706873 121807990648927960673780155)
  ·
    refine ⟨182711985973391941010670233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121807990648927960673780155 182711985973391941010670233)
    ·
      refine ⟨137033989480043955758002675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 182711985973391941010670233 137033989480043955758002675)
      ·
        refine ⟨205550984220065933637004013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 137033989480043955758002675 205550984220065933637004013)
        ·
          refine ⟨77081619082524725113876505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 205550984220065933637004013 77081619082524725113876505)
          ·
            refine ⟨57811214311893543835407379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 77081619082524725113876505 57811214311893543835407379)
            ·
              refine ⟨86716821467840315753111069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57811214311893543835407379 86716821467840315753111069)
              ·
                refine ⟨32518808050440118407416651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 86716821467840315753111069 32518808050440118407416651)
                ·
                  refine ⟨48778212075660177611124977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32518808050440118407416651 48778212075660177611124977)
                  ·
                    refine ⟨36583659056745133208343733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 48778212075660177611124977 36583659056745133208343733)
                    ·
                      refine ⟨3429718036569856238282225, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36583659056745133208343733 3429718036569856238282225)
                      ·
                        rfl

theorem cell23_6679352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 1, 3, 1, 2, 5].length) (baseStart_6679352 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6679352 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6679352 prefixEnd_6679352 := by exact prefixLift 6679352
  have htrace : WordTrace (prefixWord ++ tailWord_6679352) baseStart_6679352 baseEnd_6679352 := by
    simpa [prefixWord, tailWord_6679352, baseEnd_6679352] using wordTrace_append hprefix tailTrace_6679352
  have hstable : (prefixWord ++ tailWord_6679352).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6679352).length < 2 ^ (prefixWord ++ tailWord_6679352).sum := by decide
  have hdescent : baseEnd_6679352 < baseStart_6679352 := by decide
  rcases family_descends (prefixWord ++ tailWord_6679352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6679392 : List Nat := [2, 1, 1, 3, 3, 1, 1, 1, 1, 3, 6]
def baseStart_6679392 : Nat := 118140960795 + 6679392 * 2 ^ 59
def prefixEnd_6679392 : Nat := 4983230072969 + 3 ^ 40 * 6679392 * 2
def baseEnd_6679392 : Nat := 3429738575796036081782041

theorem tailTrace_6679392 : CollatzResearch.WordTrace tailWord_6679392 prefixEnd_6679392 3429738575796036081782041 := by
  unfold tailWord_6679392
  simp only [CollatzResearch.WordTrace]
  refine ⟨121808720108855504089508215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 162411626811807338786010953 121808720108855504089508215)
  ·
    refine ⟨182713080163283256134262323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121808720108855504089508215 182713080163283256134262323)
    ·
      refine ⟨274069620244924884201393485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 182713080163283256134262323 274069620244924884201393485)
      ·
        refine ⟨102776107591846831575522557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 274069620244924884201393485 102776107591846831575522557)
        ·
          refine ⟨38541040346942561840820959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 102776107591846831575522557 38541040346942561840820959)
          ·
            refine ⟨57811560520413842761231439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38541040346942561840820959 57811560520413842761231439)
            ·
              refine ⟨86717340780620764141847159, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57811560520413842761231439 86717340780620764141847159)
              ·
                refine ⟨130076011170931146212770739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 86717340780620764141847159 130076011170931146212770739)
                ·
                  refine ⟨195114016756396719319156109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 130076011170931146212770739 195114016756396719319156109)
                  ·
                    refine ⟨73167756283648769744683541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 195114016756396719319156109 73167756283648769744683541)
                    ·
                      refine ⟨3429738575796036081782041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 73167756283648769744683541 3429738575796036081782041)
                      ·
                        rfl

theorem cell23_6679392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 1, 1, 1, 3, 6].length) (baseStart_6679392 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6679392 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6679392 prefixEnd_6679392 := by exact prefixLift 6679392
  have htrace : WordTrace (prefixWord ++ tailWord_6679392) baseStart_6679392 baseEnd_6679392 := by
    simpa [prefixWord, tailWord_6679392, baseEnd_6679392] using wordTrace_append hprefix tailTrace_6679392
  have hstable : (prefixWord ++ tailWord_6679392).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6679392).length < 2 ^ (prefixWord ++ tailWord_6679392).sum := by decide
  have hdescent : baseEnd_6679392 < baseStart_6679392 := by decide
  rcases family_descends (prefixWord ++ tailWord_6679392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6679396 : List Nat := [2, 3, 1, 1, 4, 1, 1, 2, 2, 4, 2]
def baseStart_6679396 : Nat := 118140960795 + 6679396 * 2 ^ 59
def prefixEnd_6679396 : Nat := 4983230072969 + 3 ^ 40 * 6679396 * 2
def baseEnd_6679396 : Nat := 3429740629718654066132023

theorem tailTrace_6679396 : CollatzResearch.WordTrace tailWord_6679396 prefixEnd_6679396 3429740629718654066132023 := by
  unfold tailWord_6679396
  simp only [CollatzResearch.WordTrace]
  refine ⟨121808793054848258431081021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 162411724073131011241441361 121808793054848258431081021)
  ·
    refine ⟨45678297395568096911655383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 121808793054848258431081021 45678297395568096911655383)
    ·
      refine ⟨68517446093352145367483075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45678297395568096911655383 68517446093352145367483075)
      ·
        refine ⟨102776169140028218051224613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68517446093352145367483075 102776169140028218051224613)
        ·
          refine ⟨19270531713755290884604615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 102776169140028218051224613 19270531713755290884604615)
          ·
            refine ⟨28905797570632936326906923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19270531713755290884604615 28905797570632936326906923)
            ·
              refine ⟨43358696355949404490360385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28905797570632936326906923 43358696355949404490360385)
              ·
                refine ⟨32519022266962053367770289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43358696355949404490360385 32519022266962053367770289)
                ·
                  refine ⟨24389266700221540025827717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32519022266962053367770289 24389266700221540025827717)
                  ·
                    refine ⟨4572987506291538754842697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24389266700221540025827717 4572987506291538754842697)
                    ·
                      refine ⟨3429740629718654066132023, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4572987506291538754842697 3429740629718654066132023)
                      ·
                        rfl

theorem cell23_6679396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 1, 2, 2, 4, 2].length) (baseStart_6679396 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6679396 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6679396 prefixEnd_6679396 := by exact prefixLift 6679396
  have htrace : WordTrace (prefixWord ++ tailWord_6679396) baseStart_6679396 baseEnd_6679396 := by
    simpa [prefixWord, tailWord_6679396, baseEnd_6679396] using wordTrace_append hprefix tailTrace_6679396
  have hstable : (prefixWord ++ tailWord_6679396).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6679396).length < 2 ^ (prefixWord ++ tailWord_6679396).sum := by decide
  have hdescent : baseEnd_6679396 < baseStart_6679396 := by decide
  rcases family_descends (prefixWord ++ tailWord_6679396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6679456 : List Nat := [2, 1, 1, 4, 1, 1, 3, 1, 4, 3, 2]
def baseStart_6679456 : Nat := 118140960795 + 6679456 * 2 ^ 59
def prefixEnd_6679456 : Nat := 4983230072969 + 3 ^ 40 * 6679456 * 2
def baseEnd_6679456 : Nat := 3429771438557923831381747

theorem tailTrace_6679456 : CollatzResearch.WordTrace tailWord_6679456 prefixEnd_6679456 3429771438557923831381747 := by
  unfold tailWord_6679456
  simp only [CollatzResearch.WordTrace]
  refine ⟨121809887244739573554673111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 162413182992986098072897481 121809887244739573554673111)
  ·
    refine ⟨182714830867109360332009667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121809887244739573554673111 182714830867109360332009667)
    ·
      refine ⟨274072246300664040498014501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 182714830867109360332009667 274072246300664040498014501)
      ·
        refine ⟨51388546181374507593377719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 274072246300664040498014501 51388546181374507593377719)
        ·
          refine ⟨77082819272061761390066579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51388546181374507593377719 77082819272061761390066579)
          ·
            refine ⟨115624228908092642085099869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77082819272061761390066579 115624228908092642085099869)
            ·
              refine ⟨43359085840534740781912451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 115624228908092642085099869 43359085840534740781912451)
              ·
                refine ⟨65038628760802111172868677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43359085840534740781912451 65038628760802111172868677)
                ·
                  refine ⟨12194742892650395844912877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 65038628760802111172868677 12194742892650395844912877)
                  ·
                    refine ⟨4573028584743898441842329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12194742892650395844912877 4573028584743898441842329)
                    ·
                      refine ⟨3429771438557923831381747, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4573028584743898441842329 3429771438557923831381747)
                      ·
                        rfl

theorem cell23_6679456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 3, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 3, 1, 4, 3, 2].length) (baseStart_6679456 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6679456 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6679456 prefixEnd_6679456 := by exact prefixLift 6679456
  have htrace : WordTrace (prefixWord ++ tailWord_6679456) baseStart_6679456 baseEnd_6679456 := by
    simpa [prefixWord, tailWord_6679456, baseEnd_6679456] using wordTrace_append hprefix tailTrace_6679456
  have hstable : (prefixWord ++ tailWord_6679456).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6679456).length < 2 ^ (prefixWord ++ tailWord_6679456).sum := by decide
  have hdescent : baseEnd_6679456 < baseStart_6679456 := by decide
  rcases family_descends (prefixWord ++ tailWord_6679456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6679486 : List Nat := [4, 2, 1, 1, 1, 2, 3, 1, 3, 1, 4]
def baseStart_6679486 : Nat := 118140960795 + 6679486 * 2 ^ 59
def prefixEnd_6679486 : Nat := 4983230072969 + 3 ^ 40 * 6679486 * 2
def baseEnd_6679486 : Nat := 3429786842977558714006609

theorem tailTrace_6679486 : CollatzResearch.WordTrace tailWord_6679486 prefixEnd_6679486 3429786842977558714006609 := by
  unfold tailWord_6679486
  simp only [CollatzResearch.WordTrace]
  refine ⟨30452608584921307779117289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 162413912452913641488625541 30452608584921307779117289)
  ·
    refine ⟨22839456438690980834337967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30452608584921307779117289 22839456438690980834337967)
    ·
      refine ⟨34259184658036471251506951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22839456438690980834337967 34259184658036471251506951)
      ·
        refine ⟨51388776987054706877260427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34259184658036471251506951 51388776987054706877260427)
        ·
          refine ⟨77083165480582060315890641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51388776987054706877260427 77083165480582060315890641)
          ·
            refine ⟨57812374110436545236917981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 77083165480582060315890641 57812374110436545236917981)
            ·
              refine ⟨21679640291413704463844243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 57812374110436545236917981 21679640291413704463844243)
              ·
                refine ⟨32519460437120556695766365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21679640291413704463844243 32519460437120556695766365)
                ·
                  refine ⟨12194797663920208760912387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32519460437120556695766365 12194797663920208760912387)
                  ·
                    refine ⟨18292196495880313141368581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12194797663920208760912387 18292196495880313141368581)
                    ·
                      refine ⟨3429786842977558714006609, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18292196495880313141368581 3429786842977558714006609)
                      ·
                        rfl

theorem cell23_6679486_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 3, 1, 3, 1, 4].length) (baseStart_6679486 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6679486 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6679486 prefixEnd_6679486 := by exact prefixLift 6679486
  have htrace : WordTrace (prefixWord ++ tailWord_6679486) baseStart_6679486 baseEnd_6679486 := by
    simpa [prefixWord, tailWord_6679486, baseEnd_6679486] using wordTrace_append hprefix tailTrace_6679486
  have hstable : (prefixWord ++ tailWord_6679486).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6679486).length < 2 ^ (prefixWord ++ tailWord_6679486).sum := by decide
  have hdescent : baseEnd_6679486 < baseStart_6679486 := by decide
  rcases family_descends (prefixWord ++ tailWord_6679486) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6679496 : List Nat := [2, 1, 3, 1, 5, 1, 1, 2, 1, 6]
def baseStart_6679496 : Nat := 118140960795 + 6679496 * 2 ^ 59
def prefixEnd_6679496 : Nat := 4983230072969 + 3 ^ 40 * 6679496 * 2
def baseEnd_6679496 : Nat := 1143263992594701224960521

theorem tailTrace_6679496 : CollatzResearch.WordTrace tailWord_6679496 prefixEnd_6679496 1143263992594701224960521 := by
  unfold tailWord_6679496
  simp only [CollatzResearch.WordTrace]
  refine ⟨121810616704667116970401171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 162414155606222822627201561 121810616704667116970401171)
  ·
    refine ⟨182715925057000675455601757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121810616704667116970401171 182715925057000675455601757)
    ·
      refine ⟨68518471896375253295850659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 182715925057000675455601757 68518471896375253295850659)
      ·
        refine ⟨102777707844562879943775989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68518471896375253295850659 102777707844562879943775989)
        ·
          refine ⟨9635410110427769994728999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 102777707844562879943775989 9635410110427769994728999)
          ·
            refine ⟨14453115165641654992093499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9635410110427769994728999 14453115165641654992093499)
            ·
              refine ⟨21679672748462482488140249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14453115165641654992093499 21679672748462482488140249)
              ·
                refine ⟨16259754561346861866105187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21679672748462482488140249 16259754561346861866105187)
                ·
                  refine ⟨24389631842020292799157781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16259754561346861866105187 24389631842020292799157781)
                  ·
                    refine ⟨1143263992594701224960521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24389631842020292799157781 1143263992594701224960521)
                    ·
                      rfl

theorem cell23_6679496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 5, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 5, 1, 1, 2, 1, 6].length) (baseStart_6679496 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6679496 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6679496 prefixEnd_6679496 := by exact prefixLift 6679496
  have htrace : WordTrace (prefixWord ++ tailWord_6679496) baseStart_6679496 baseEnd_6679496 := by
    simpa [prefixWord, tailWord_6679496, baseEnd_6679496] using wordTrace_append hprefix tailTrace_6679496
  have hstable : (prefixWord ++ tailWord_6679496).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6679496).length < 2 ^ (prefixWord ++ tailWord_6679496).sum := by decide
  have hdescent : baseEnd_6679496 < baseStart_6679496 := by decide
  rcases family_descends (prefixWord ++ tailWord_6679496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6679499 : List Nat := [1, 1, 1, 1, 3, 5, 1, 1, 3, 2, 4]
def baseStart_6679499 : Nat := 118140960795 + 6679499 * 2 ^ 59
def prefixEnd_6679499 : Nat := 4983230072969 + 3 ^ 40 * 6679499 * 2
def baseEnd_6679499 : Nat := 3429793518226067163144049

theorem tailTrace_6679499 : CollatzResearch.WordTrace tailWord_6679499 prefixEnd_6679499 3429793518226067163144049 := by
  unfold tailWord_6679499
  simp only [CollatzResearch.WordTrace]
  refine ⟨243621342828323365453161551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162414228552215576968774367 243621342828323365453161551)
  ·
    refine ⟨365432014242485048179742327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 243621342828323365453161551 365432014242485048179742327)
    ·
      refine ⟨548148021363727572269613491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 365432014242485048179742327 548148021363727572269613491)
      ·
        refine ⟨822222032045591358404420237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 548148021363727572269613491 822222032045591358404420237)
        ·
          refine ⟨308333262017096759401657589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 822222032045591358404420237 308333262017096759401657589)
          ·
            refine ⟨28906243314102821193905399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 308333262017096759401657589 28906243314102821193905399)
            ·
              refine ⟨43359364971154231790858099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28906243314102821193905399 43359364971154231790858099)
              ·
                refine ⟨65039047456731347686287149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43359364971154231790858099 65039047456731347686287149)
                ·
                  refine ⟨24389642796274255382357681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 65039047456731347686287149 24389642796274255382357681)
                  ·
                    refine ⟨18292232097205691536768261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24389642796274255382357681 18292232097205691536768261)
                    ·
                      refine ⟨3429793518226067163144049, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18292232097205691536768261 3429793518226067163144049)
                      ·
                        rfl

theorem cell23_6679499_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 1, 1, 3, 2, 4].length) (baseStart_6679499 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6679499 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6679499 prefixEnd_6679499 := by exact prefixLift 6679499
  have htrace : WordTrace (prefixWord ++ tailWord_6679499) baseStart_6679499 baseEnd_6679499 := by
    simpa [prefixWord, tailWord_6679499, baseEnd_6679499] using wordTrace_append hprefix tailTrace_6679499
  have hstable : (prefixWord ++ tailWord_6679499).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6679499).length < 2 ^ (prefixWord ++ tailWord_6679499).sum := by decide
  have hdescent : baseEnd_6679499 < baseStart_6679499 := by decide
  rcases family_descends (prefixWord ++ tailWord_6679499) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6679503 : List Nat := [1, 1, 2, 1, 1, 7, 3, 1, 1, 1, 4]
def baseStart_6679503 : Nat := 118140960795 + 6679503 * 2 ^ 59
def prefixEnd_6679503 : Nat := 4983230072969 + 3 ^ 40 * 6679503 * 2
def baseEnd_6679503 : Nat := 3429795572148685147494031

theorem tailTrace_6679503 : CollatzResearch.WordTrace tailWord_6679503 prefixEnd_6679503 3429795572148685147494031 := by
  unfold tailWord_6679503
  simp only [CollatzResearch.WordTrace]
  refine ⟨243621488720308874136307163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162414325813539249424204775 243621488720308874136307163)
  ·
    refine ⟨365432233080463311204460745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 243621488720308874136307163 365432233080463311204460745)
    ·
      refine ⟨274074174810347483403345559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 365432233080463311204460745 274074174810347483403345559)
      ·
        refine ⟨411111262215521225105018339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 274074174810347483403345559 411111262215521225105018339)
        ·
          refine ⟨616666893323281837657527509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 411111262215521225105018339 616666893323281837657527509)
          ·
            refine ⟨14453130312264418070098301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 616666893323281837657527509 14453130312264418070098301)
            ·
              refine ⟨5419923867099156776286863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14453130312264418070098301 5419923867099156776286863)
              ·
                refine ⟨8129885800648735164430295, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5419923867099156776286863 8129885800648735164430295)
                ·
                  refine ⟨12194828700973102746645443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8129885800648735164430295 12194828700973102746645443)
                  ·
                    refine ⟨18292243051459654119968165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12194828700973102746645443 18292243051459654119968165)
                    ·
                      refine ⟨3429795572148685147494031, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18292243051459654119968165 3429795572148685147494031)
                      ·
                        rfl

theorem cell23_6679503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 7, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 7, 3, 1, 1, 1, 4].length) (baseStart_6679503 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6679503 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6679503 prefixEnd_6679503 := by exact prefixLift 6679503
  have htrace : WordTrace (prefixWord ++ tailWord_6679503) baseStart_6679503 baseEnd_6679503 := by
    simpa [prefixWord, tailWord_6679503, baseEnd_6679503] using wordTrace_append hprefix tailTrace_6679503
  have hstable : (prefixWord ++ tailWord_6679503).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6679503).length < 2 ^ (prefixWord ++ tailWord_6679503).sum := by decide
  have hdescent : baseEnd_6679503 < baseStart_6679503 := by decide
  rcases family_descends (prefixWord ++ tailWord_6679503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6679509 : List Nat := [1, 3, 2, 3, 3, 11]
def baseStart_6679509 : Nat := 118140960795 + 6679509 * 2 ^ 59
def prefixEnd_6679509 : Nat := 4983230072969 + 3 ^ 40 * 6679509 * 2
def baseEnd_6679509 : Nat := 14114397749105399687321

theorem tailTrace_6679509 : CollatzResearch.WordTrace tailWord_6679509 prefixEnd_6679509 14114397749105399687321 := by
  unfold tailWord_6679509
  simp only [CollatzResearch.WordTrace]
  refine ⟨243621707558287137161025581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162414471705524758107350387 243621707558287137161025581)
  ·
    refine ⟨91358140334357676435384593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 243621707558287137161025581 91358140334357676435384593)
    ·
      refine ⟨68518605250768257326538445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 91358140334357676435384593 68518605250768257326538445)
      ·
        refine ⟨25694476969038096497451917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 68518605250768257326538445 25694476969038096497451917)
        ·
          refine ⟨9635428863389286186544469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25694476969038096497451917 9635428863389286186544469)
          ·
            refine ⟨14114397749105399687321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 9635428863389286186544469 14114397749105399687321)
            ·
              rfl

theorem cell23_6679509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 3, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 3, 11].length) (baseStart_6679509 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6679509 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6679509 prefixEnd_6679509 := by exact prefixLift 6679509
  have htrace : WordTrace (prefixWord ++ tailWord_6679509) baseStart_6679509 baseEnd_6679509 := by
    simpa [prefixWord, tailWord_6679509, baseEnd_6679509] using wordTrace_append hprefix tailTrace_6679509
  have hstable : (prefixWord ++ tailWord_6679509).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6679509).length < 2 ^ (prefixWord ++ tailWord_6679509).sum := by decide
  have hdescent : baseEnd_6679509 < baseStart_6679509 := by decide
  rcases family_descends (prefixWord ++ tailWord_6679509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6679513 : List Nat := [1, 2, 1, 2, 5, 2, 2, 2, 2, 4]
def baseStart_6679513 : Nat := 118140960795 + 6679513 * 2 ^ 59
def prefixEnd_6679513 : Nat := 4983230072969 + 3 ^ 40 * 6679513 * 2
def baseEnd_6679513 : Nat := 1143266902318410036122995

theorem tailTrace_6679513 : CollatzResearch.WordTrace tailWord_6679513 prefixEnd_6679513 1143266902318410036122995 := by
  unfold tailWord_6679513
  simp only [CollatzResearch.WordTrace]
  refine ⟨243621853450272645844171193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162414568966848430562780795 243621853450272645844171193)
  ·
    refine ⟨182716390087704484383128395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 243621853450272645844171193 182716390087704484383128395)
    ·
      refine ⟨274074585131556726574692593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 182716390087704484383128395 274074585131556726574692593)
      ·
        refine ⟨205555938848667544931019445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 274074585131556726574692593 205555938848667544931019445)
        ·
          refine ⟨19270869267062582337283073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 205555938848667544931019445 19270869267062582337283073)
          ·
            refine ⟨14453151950296936752962305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19270869267062582337283073 14453151950296936752962305)
            ·
              refine ⟨10839863962722702564721729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14453151950296936752962305 10839863962722702564721729)
              ·
                refine ⟨8129897972042026923541297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10839863962722702564721729 8129897972042026923541297)
                ·
                  refine ⟨6097423479031520192655973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8129897972042026923541297 6097423479031520192655973)
                  ·
                    refine ⟨1143266902318410036122995, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6097423479031520192655973 1143266902318410036122995)
                    ·
                      rfl

theorem cell23_6679513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 2, 2, 2, 2, 4].length) (baseStart_6679513 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6679513 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6679513 prefixEnd_6679513 := by exact prefixLift 6679513
  have htrace : WordTrace (prefixWord ++ tailWord_6679513) baseStart_6679513 baseEnd_6679513 := by
    simpa [prefixWord, tailWord_6679513, baseEnd_6679513] using wordTrace_append hprefix tailTrace_6679513
  have hstable : (prefixWord ++ tailWord_6679513).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6679513).length < 2 ^ (prefixWord ++ tailWord_6679513).sum := by decide
  have hdescent : baseEnd_6679513 < baseStart_6679513 := by decide
  rcases family_descends (prefixWord ++ tailWord_6679513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6679536 : List Nat := [2, 1, 1, 1, 3, 2, 1, 2, 6, 1, 3]
def baseStart_6679536 : Nat := 118140960795 + 6679536 * 2 ^ 59
def prefixEnd_6679536 : Nat := 4983230072969 + 3 ^ 40 * 6679536 * 2
def baseEnd_6679536 : Nat := 3429812517010283518381379

theorem tailTrace_6679536 : CollatzResearch.WordTrace tailWord_6679536 prefixEnd_6679536 3429812517010283518381379 := by
  unfold tailWord_6679536
  simp only [CollatzResearch.WordTrace]
  refine ⟨121811346164594660386129231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 162415128219459547181505641 121811346164594660386129231)
  ·
    refine ⟨182717019246891990579193847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121811346164594660386129231 182717019246891990579193847)
    ·
      refine ⟨274075528870337985868790771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 182717019246891990579193847 274075528870337985868790771)
      ·
        refine ⟨411113293305506978803186157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 274075528870337985868790771 411113293305506978803186157)
        ·
          refine ⟨154167484989565117051194809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 411113293305506978803186157 154167484989565117051194809)
          ·
            refine ⟨115625613742173837788396107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 154167484989565117051194809 115625613742173837788396107)
            ·
              refine ⟨173438420613260756682594161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 115625613742173837788396107 173438420613260756682594161)
              ·
                refine ⟨130078815459945567511945621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 173438420613260756682594161 130078815459945567511945621)
                ·
                  refine ⟨6097444474684948477122451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 130078815459945567511945621 6097444474684948477122451)
                  ·
                    refine ⟨9146166712027422715683677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6097444474684948477122451 9146166712027422715683677)
                    ·
                      refine ⟨3429812517010283518381379, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9146166712027422715683677 3429812517010283518381379)
                      ·
                        rfl

theorem cell23_6679536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 1, 2, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 1, 2, 6, 1, 3].length) (baseStart_6679536 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6679536 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6679536 prefixEnd_6679536 := by exact prefixLift 6679536
  have htrace : WordTrace (prefixWord ++ tailWord_6679536) baseStart_6679536 baseEnd_6679536 := by
    simpa [prefixWord, tailWord_6679536, baseEnd_6679536] using wordTrace_append hprefix tailTrace_6679536
  have hstable : (prefixWord ++ tailWord_6679536).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6679536).length < 2 ^ (prefixWord ++ tailWord_6679536).sum := by decide
  have hdescent : baseEnd_6679536 < baseStart_6679536 := by decide
  rcases family_descends (prefixWord ++ tailWord_6679536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6679549 : List Nat := [1, 4, 1, 1, 1, 2, 1, 3, 2, 2, 5]
def baseStart_6679549 : Nat := 118140960795 + 6679549 * 2 ^ 59
def prefixEnd_6679549 : Nat := 4983230072969 + 3 ^ 40 * 6679549 * 2
def baseEnd_6679549 : Nat := 3429819192258791967518819

theorem tailTrace_6679549 : CollatzResearch.WordTrace tailWord_6679549 prefixEnd_6679549 3429819192258791967518819 := by
  unfold tailWord_6679549
  simp only [CollatzResearch.WordTrace]
  refine ⟨243623166478142223992481701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162415444318761482661654467 243623166478142223992481701)
  ·
    refine ⟨45679343714651666998590319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 243623166478142223992481701 45679343714651666998590319)
    ·
      refine ⟨68519015571977500497885479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45679343714651666998590319 68519015571977500497885479)
      ·
        refine ⟨102778523357966250746828219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68519015571977500497885479 102778523357966250746828219)
        ·
          refine ⟨154167785036949376120242329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 102778523357966250746828219 154167785036949376120242329)
          ·
            refine ⟨115625838777712032090181747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 154167785036949376120242329 115625838777712032090181747)
            ·
              refine ⟨173438758166568048135272621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 115625838777712032090181747 173438758166568048135272621)
              ·
                refine ⟨65039534312463018050727233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 173438758166568048135272621 65039534312463018050727233)
                ·
                  refine ⟨48779650734347263538045425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 65039534312463018050727233 48779650734347263538045425)
                  ·
                    refine ⟨36584738050760447653534069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 48779650734347263538045425 36584738050760447653534069)
                    ·
                      refine ⟨3429819192258791967518819, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36584738050760447653534069 3429819192258791967518819)
                      ·
                        rfl

theorem cell23_6679549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 1, 3, 2, 2, 5].length) (baseStart_6679549 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6679549 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6679549 prefixEnd_6679549 := by exact prefixLift 6679549
  have htrace : WordTrace (prefixWord ++ tailWord_6679549) baseStart_6679549 baseEnd_6679549 := by
    simpa [prefixWord, tailWord_6679549, baseEnd_6679549] using wordTrace_append hprefix tailTrace_6679549
  have hstable : (prefixWord ++ tailWord_6679549).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6679549).length < 2 ^ (prefixWord ++ tailWord_6679549).sum := by decide
  have hdescent : baseEnd_6679549 < baseStart_6679549 := by decide
  rcases family_descends (prefixWord ++ tailWord_6679549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6679554 : List Nat := [3, 4, 1, 3, 1, 2, 2, 1, 1, 1, 4]
def baseStart_6679554 : Nat := 118140960795 + 6679554 * 2 ^ 59
def prefixEnd_6679554 : Nat := 4983230072969 + 3 ^ 40 * 6679554 * 2
def baseEnd_6679554 : Nat := 3429821759662064447956297

theorem tailTrace_6679554 : CollatzResearch.WordTrace tailWord_6679554 prefixEnd_6679554 3429821759662064447956297 := by
  unfold tailWord_6679554
  simp only [CollatzResearch.WordTrace]
  refine ⟨60905837210781027461603429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 162415565895416073230942477 60905837210781027461603429)
  ·
    refine ⟨11419844477021442649050643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 60905837210781027461603429 11419844477021442649050643)
    ·
      refine ⟨17129766715532163973575965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11419844477021442649050643 17129766715532163973575965)
      ·
        refine ⟨6423662518324561490090987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17129766715532163973575965 6423662518324561490090987)
        ·
          refine ⟨9635493777486842235136481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6423662518324561490090987 9635493777486842235136481)
          ·
            refine ⟨7226620333115131676352361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9635493777486842235136481 7226620333115131676352361)
            ·
              refine ⟨5419965249836348757264271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7226620333115131676352361 5419965249836348757264271)
              ·
                refine ⟨8129947874754523135896407, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5419965249836348757264271 8129947874754523135896407)
                ·
                  refine ⟨12194921812131784703844611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8129947874754523135896407 12194921812131784703844611)
                  ·
                    refine ⟨18292382718197677055766917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12194921812131784703844611 18292382718197677055766917)
                    ·
                      refine ⟨3429821759662064447956297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18292382718197677055766917 3429821759662064447956297)
                      ·
                        rfl

theorem cell23_6679554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 1, 2, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 1, 2, 2, 1, 1, 1, 4].length) (baseStart_6679554 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6679554 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6679554 prefixEnd_6679554 := by exact prefixLift 6679554
  have htrace : WordTrace (prefixWord ++ tailWord_6679554) baseStart_6679554 baseEnd_6679554 := by
    simpa [prefixWord, tailWord_6679554, baseEnd_6679554] using wordTrace_append hprefix tailTrace_6679554
  have hstable : (prefixWord ++ tailWord_6679554).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6679554).length < 2 ^ (prefixWord ++ tailWord_6679554).sum := by decide
  have hdescent : baseEnd_6679554 < baseStart_6679554 := by decide
  rcases family_descends (prefixWord ++ tailWord_6679554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6679586 : List Nat := [3, 3, 1, 1, 1, 3, 2, 1, 2, 6]
def baseStart_6679586 : Nat := 118140960795 + 6679586 * 2 ^ 59
def prefixEnd_6679586 : Nat := 4983230072969 + 3 ^ 40 * 6679586 * 2
def baseEnd_6679586 : Nat := 1143279397014336107585383

theorem tailTrace_6679586 : CollatzResearch.WordTrace tailWord_6679586 prefixEnd_6679586 1143279397014336107585383 := by
  unfold tailWord_6679586
  simp only [CollatzResearch.WordTrace]
  refine ⟨60906128994752044827894653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 162416343986005452874385741 60906128994752044827894653)
  ·
    refine ⟨22839798373032016810460495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 60906128994752044827894653 22839798373032016810460495)
    ·
      refine ⟨34259697559548025215690743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22839798373032016810460495 34259697559548025215690743)
      ·
        refine ⟨51389546339322037823536115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34259697559548025215690743 51389546339322037823536115)
        ·
          refine ⟨77084319508983056735304173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51389546339322037823536115 77084319508983056735304173)
          ·
            refine ⟨28906619815868646275739065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 77084319508983056735304173 28906619815868646275739065)
            ·
              refine ⟨21679964861901484706804299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28906619815868646275739065 21679964861901484706804299)
              ·
                refine ⟨32519947292852227060206449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21679964861901484706804299 32519947292852227060206449)
                ·
                  refine ⟨24389960469639170295154837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32519947292852227060206449 24389960469639170295154837)
                  ·
                    refine ⟨1143279397014336107585383, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24389960469639170295154837 1143279397014336107585383)
                    ·
                      rfl

theorem cell23_6679586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 2, 1, 2, 6].length) (baseStart_6679586 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6679586 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6679586 prefixEnd_6679586 := by exact prefixLift 6679586
  have htrace : WordTrace (prefixWord ++ tailWord_6679586) baseStart_6679586 baseEnd_6679586 := by
    simpa [prefixWord, tailWord_6679586, baseEnd_6679586] using wordTrace_append hprefix tailTrace_6679586
  have hstable : (prefixWord ++ tailWord_6679586).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6679586).length < 2 ^ (prefixWord ++ tailWord_6679586).sum := by decide
  have hdescent : baseEnd_6679586 < baseStart_6679586 := by decide
  rcases family_descends (prefixWord ++ tailWord_6679586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6679626 : List Nat := [3, 1, 2, 1, 1, 2, 2, 1, 4, 3, 3]
def baseStart_6679626 : Nat := 118140960795 + 6679626 * 2 ^ 59
def prefixEnd_6679626 : Nat := 4983230072969 + 3 ^ 40 * 6679626 * 2
def baseEnd_6679626 : Nat := 3429858730269188166255965

theorem tailTrace_6679626 : CollatzResearch.WordTrace tailWord_6679626 prefixEnd_6679626 3429858730269188166255965 := by
  unfold tailWord_6679626
  simp only [CollatzResearch.WordTrace]
  refine ⟨60906493724715816535758683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 162417316599242177428689821 60906493724715816535758683)
  ·
    refine ⟨91359740587073724803638025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60906493724715816535758683 91359740587073724803638025)
    ·
      refine ⟨68519805440305293602728519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 91359740587073724803638025 68519805440305293602728519)
      ·
        refine ⟨102779708160457940404092779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68519805440305293602728519 102779708160457940404092779)
        ·
          refine ⟨154169562240686910606139169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 102779708160457940404092779 154169562240686910606139169)
          ·
            refine ⟨115627171680515182954604377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 154169562240686910606139169 115627171680515182954604377)
            ·
              refine ⟨86720378760386387215953283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 115627171680515182954604377 86720378760386387215953283)
              ·
                refine ⟨130080568140579580823929925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 86720378760386387215953283 130080568140579580823929925)
                ·
                  refine ⟨24390106526358671404486861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 130080568140579580823929925 24390106526358671404486861)
                  ·
                    refine ⟨9146289947384501776682573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24390106526358671404486861 9146289947384501776682573)
                    ·
                      refine ⟨3429858730269188166255965, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9146289947384501776682573 3429858730269188166255965)
                      ·
                        rfl

theorem cell23_6679626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 2, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 2, 1, 4, 3, 3].length) (baseStart_6679626 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6679626 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6679626 prefixEnd_6679626 := by exact prefixLift 6679626
  have htrace : WordTrace (prefixWord ++ tailWord_6679626) baseStart_6679626 baseEnd_6679626 := by
    simpa [prefixWord, tailWord_6679626, baseEnd_6679626] using wordTrace_append hprefix tailTrace_6679626
  have hstable : (prefixWord ++ tailWord_6679626).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6679626).length < 2 ^ (prefixWord ++ tailWord_6679626).sum := by decide
  have hdescent : baseEnd_6679626 < baseStart_6679626 := by decide
  rcases family_descends (prefixWord ++ tailWord_6679626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6679638 : List Nat := [5, 2, 2, 1, 3, 1, 2, 1, 2, 1, 3]
def baseStart_6679638 : Nat := 118140960795 + 6679638 * 2 ^ 59
def prefixEnd_6679638 : Nat := 4983230072969 + 3 ^ 40 * 6679638 * 2
def baseEnd_6679638 : Nat := 3429864892037042119305911

theorem tailTrace_6679638 : CollatzResearch.WordTrace tailWord_6679638 prefixEnd_6679638 3429864892037042119305911 := by
  unfold tailWord_6679638
  simp only [CollatzResearch.WordTrace]
  refine ⟨15226650785926237012029473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 162417608383213194794981045 15226650785926237012029473)
  ·
    refine ⟨11419988089444677759022105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15226650785926237012029473 11419988089444677759022105)
    ·
      refine ⟨8564991067083508319266579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11419988089444677759022105 8564991067083508319266579)
      ·
        refine ⟨12847486600625262478899869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8564991067083508319266579 12847486600625262478899869)
        ·
          refine ⟨4817807475234473429587451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12847486600625262478899869 4817807475234473429587451)
          ·
            refine ⟨7226711212851710144381177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4817807475234473429587451 7226711212851710144381177)
            ·
              refine ⟨5420033409638782608285883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7226711212851710144381177 5420033409638782608285883)
              ·
                refine ⟨8130050114458173912428825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5420033409638782608285883 8130050114458173912428825)
                ·
                  refine ⟨6097537585843630434321619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8130050114458173912428825 6097537585843630434321619)
                  ·
                    refine ⟨9146306378765445651482429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6097537585843630434321619 9146306378765445651482429)
                    ·
                      refine ⟨3429864892037042119305911, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9146306378765445651482429 3429864892037042119305911)
                      ·
                        rfl

theorem cell23_6679638_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 3, 1, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 3, 1, 2, 1, 2, 1, 3].length) (baseStart_6679638 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6679638 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6679638 prefixEnd_6679638 := by exact prefixLift 6679638
  have htrace : WordTrace (prefixWord ++ tailWord_6679638) baseStart_6679638 baseEnd_6679638 := by
    simpa [prefixWord, tailWord_6679638, baseEnd_6679638] using wordTrace_append hprefix tailTrace_6679638
  have hstable : (prefixWord ++ tailWord_6679638).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6679638).length < 2 ^ (prefixWord ++ tailWord_6679638).sum := by decide
  have hdescent : baseEnd_6679638 < baseStart_6679638 := by decide
  rcases family_descends (prefixWord ++ tailWord_6679638) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6679678 : List Nat := [4, 2, 4, 1, 1, 1, 2, 2, 2, 2, 2]
def baseStart_6679678 : Nat := 118140960795 + 6679678 * 2 ^ 59
def prefixEnd_6679678 : Nat := 4983230072969 + 3 ^ 40 * 6679678 * 2
def baseEnd_6679678 : Nat := 3429885431263221962805727

theorem tailTrace_6679678 : CollatzResearch.WordTrace tailWord_6679678 prefixEnd_6679678 3429885431263221962805727 := by
  unfold tailWord_6679678
  simp only [CollatzResearch.WordTrace]
  refine ⟨30453483936834359877990961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 162418580996449919349285125 30453483936834359877990961)
  ·
    refine ⟨22840112952625769908493221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30453483936834359877990961 22840112952625769908493221)
    ·
      refine ⟨4282521178617331857842479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 22840112952625769908493221 4282521178617331857842479)
      ·
        refine ⟨6423781767925997786763719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4282521178617331857842479 6423781767925997786763719)
        ·
          refine ⟨9635672651888996680145579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6423781767925997786763719 9635672651888996680145579)
          ·
            refine ⟨14453508977833495020218369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9635672651888996680145579 14453508977833495020218369)
            ·
              refine ⟨10840131733375121265163777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14453508977833495020218369 10840131733375121265163777)
              ·
                refine ⟨8130098800031340948872833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10840131733375121265163777 8130098800031340948872833)
                ·
                  refine ⟨6097574100023505711654625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8130098800031340948872833 6097574100023505711654625)
                  ·
                    refine ⟨4573180575017629283740969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6097574100023505711654625 4573180575017629283740969)
                    ·
                      refine ⟨3429885431263221962805727, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4573180575017629283740969 3429885431263221962805727)
                      ·
                        rfl

theorem cell23_6679678_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 1, 1, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 1, 1, 2, 2, 2, 2, 2].length) (baseStart_6679678 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6679678 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6679678 prefixEnd_6679678 := by exact prefixLift 6679678
  have htrace : WordTrace (prefixWord ++ tailWord_6679678) baseStart_6679678 baseEnd_6679678 := by
    simpa [prefixWord, tailWord_6679678, baseEnd_6679678] using wordTrace_append hprefix tailTrace_6679678
  have hstable : (prefixWord ++ tailWord_6679678).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6679678).length < 2 ^ (prefixWord ++ tailWord_6679678).sum := by decide
  have hdescent : baseEnd_6679678 < baseStart_6679678 := by decide
  rcases family_descends (prefixWord ++ tailWord_6679678) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6679683 : List Nat := [1, 1, 1, 3, 3, 2, 2, 2, 2, 4, 2]
def baseStart_6679683 : Nat := 118140960795 + 6679683 * 2 ^ 59
def prefixEnd_6679683 : Nat := 4983230072969 + 3 ^ 40 * 6679683 * 2
def baseEnd_6679683 : Nat := 3429887998666494443243203

theorem tailTrace_6679683 : CollatzResearch.WordTrace tailWord_6679683 prefixEnd_6679683 3429887998666494443243203 := by
  unfold tailWord_6679683
  simp only [CollatzResearch.WordTrace]
  refine ⟨243628053859656764877859703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162418702573104509918573135 243628053859656764877859703)
  ·
    refine ⟨365442080789485147316789555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 243628053859656764877859703 365442080789485147316789555)
    ·
      refine ⟨548163121184227720975184333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 365442080789485147316789555 548163121184227720975184333)
      ·
        refine ⟨205561170444085395365694125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 548163121184227720975184333 205561170444085395365694125)
        ·
          refine ⟨77085438916532023262135297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 205561170444085395365694125 77085438916532023262135297)
          ·
            refine ⟨57814079187399017446601473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 77085438916532023262135297 57814079187399017446601473)
            ·
              refine ⟨43360559390549263084951105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 57814079187399017446601473 43360559390549263084951105)
              ·
                refine ⟨32520419542911947313713329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43360559390549263084951105 32520419542911947313713329)
                ·
                  refine ⟨24390314657183960485284997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32520419542911947313713329 24390314657183960485284997)
                  ·
                    refine ⟨4573183998221992590990937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24390314657183960485284997 4573183998221992590990937)
                    ·
                      refine ⟨3429887998666494443243203, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4573183998221992590990937 3429887998666494443243203)
                      ·
                        rfl

theorem cell23_6679683_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 2, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 2, 2, 2, 4, 2].length) (baseStart_6679683 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6679683 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6679683 prefixEnd_6679683 := by exact prefixLift 6679683
  have htrace : WordTrace (prefixWord ++ tailWord_6679683) baseStart_6679683 baseEnd_6679683 := by
    simpa [prefixWord, tailWord_6679683, baseEnd_6679683] using wordTrace_append hprefix tailTrace_6679683
  have hstable : (prefixWord ++ tailWord_6679683).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6679683).length < 2 ^ (prefixWord ++ tailWord_6679683).sum := by decide
  have hdescent : baseEnd_6679683 < baseStart_6679683 := by decide
  rcases family_descends (prefixWord ++ tailWord_6679683) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6679710 : List Nat := [4, 3, 1, 1, 2, 1, 1, 1, 5, 4]
def baseStart_6679710 : Nat := 118140960795 + 6679710 * 2 ^ 59
def prefixEnd_6679710 : Nat := 4983230072969 + 3 ^ 40 * 6679710 * 2
def baseEnd_6679710 : Nat := 1143300620881388612535193

theorem tailTrace_6679710 : CollatzResearch.WordTrace tailWord_6679710 prefixEnd_6679710 1143300620881388612535193 := by
  unfold tailWord_6679710
  simp only [CollatzResearch.WordTrace]
  refine ⟨30453629828819868561136573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 162419359087039298992728389 30453629828819868561136573)
  ·
    refine ⟨11420111185807450710426215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30453629828819868561136573 11420111185807450710426215)
    ·
      refine ⟨17130166778711176065639323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11420111185807450710426215 17130166778711176065639323)
      ·
        refine ⟨25695250168066764098458985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17130166778711176065639323 25695250168066764098458985)
        ·
          refine ⟨19271437626050073073844239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25695250168066764098458985 19271437626050073073844239)
          ·
            refine ⟨28907156439075109610766359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19271437626050073073844239 28907156439075109610766359)
            ·
              refine ⟨43360734658612664416149539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28907156439075109610766359 43360734658612664416149539)
              ·
                refine ⟨65041101987918996624224309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43360734658612664416149539 65041101987918996624224309)
                ·
                  refine ⟨6097603311367405933521029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 65041101987918996624224309 6097603311367405933521029)
                  ·
                    refine ⟨1143300620881388612535193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6097603311367405933521029 1143300620881388612535193)
                    ·
                      rfl

theorem cell23_6679710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 1, 1, 5, 4].length) (baseStart_6679710 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6679710 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6679710 prefixEnd_6679710 := by exact prefixLift 6679710
  have htrace : WordTrace (prefixWord ++ tailWord_6679710) baseStart_6679710 baseEnd_6679710 := by
    simpa [prefixWord, tailWord_6679710, baseEnd_6679710] using wordTrace_append hprefix tailTrace_6679710
  have hstable : (prefixWord ++ tailWord_6679710).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6679710).length < 2 ^ (prefixWord ++ tailWord_6679710).sum := by decide
  have hdescent : baseEnd_6679710 < baseStart_6679710 := by decide
  rcases family_descends (prefixWord ++ tailWord_6679710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6679736 : List Nat := [2, 1, 2, 1, 2, 1, 2, 2, 5, 5]
def baseStart_6679736 : Nat := 118140960795 + 6679736 * 2 ^ 59
def prefixEnd_6679736 : Nat := 4983230072969 + 3 ^ 40 * 6679736 * 2
def baseEnd_6679736 : Nat := 1143305071047060911960153

theorem tailTrace_6679736 : CollatzResearch.WordTrace tailWord_6679736 prefixEnd_6679736 1143305071047060911960153 := by
  unfold tailWord_6679736
  simp only [CollatzResearch.WordTrace]
  refine ⟨121814993464232377464769531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 162419991285643169953026041 121814993464232377464769531)
  ·
    refine ⟨182722490196348566197154297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121814993464232377464769531 182722490196348566197154297)
    ·
      refine ⟨137041867647261424647865723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 182722490196348566197154297 137041867647261424647865723)
      ·
        refine ⟨205562801470892136971798585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 137041867647261424647865723 205562801470892136971798585)
        ·
          refine ⟨154172101103169102728848939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 205562801470892136971798585 154172101103169102728848939)
          ·
            refine ⟨231258151654753654093273409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 154172101103169102728848939 231258151654753654093273409)
            ·
              refine ⟨173443613741065240569955057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 231258151654753654093273409 173443613741065240569955057)
              ·
                refine ⟨130082710305798930427466293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 173443613741065240569955057 130082710305798930427466293)
                ·
                  refine ⟨12195254091168649727574965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 130082710305798930427466293 12195254091168649727574965)
                  ·
                    refine ⟨1143305071047060911960153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12195254091168649727574965 1143305071047060911960153)
                    ·
                      rfl

theorem cell23_6679736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 2, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 2, 2, 5, 5].length) (baseStart_6679736 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6679736 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6679736 prefixEnd_6679736 := by exact prefixLift 6679736
  have htrace : WordTrace (prefixWord ++ tailWord_6679736) baseStart_6679736 baseEnd_6679736 := by
    simpa [prefixWord, tailWord_6679736, baseEnd_6679736] using wordTrace_append hprefix tailTrace_6679736
  have hstable : (prefixWord ++ tailWord_6679736).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6679736).length < 2 ^ (prefixWord ++ tailWord_6679736).sum := by decide
  have hdescent : baseEnd_6679736 < baseStart_6679736 := by decide
  rcases family_descends (prefixWord ++ tailWord_6679736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6679740 : List Nat := [2, 2, 2, 3, 2, 3, 1, 2, 6]
def baseStart_6679740 : Nat := 118140960795 + 6679740 * 2 ^ 59
def prefixEnd_6679740 : Nat := 4983230072969 + 3 ^ 40 * 6679740 * 2
def baseEnd_6679740 : Nat := 381101918562644524470049

theorem tailTrace_6679740 : CollatzResearch.WordTrace tailWord_6679740 prefixEnd_6679740 381101918562644524470049 := by
  unfold tailWord_6679740
  simp only [CollatzResearch.WordTrace]
  refine ⟨121815066410225131806342337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 162420088546966842408456449 121815066410225131806342337)
  ·
    refine ⟨91361299807668848854756753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 121815066410225131806342337 91361299807668848854756753)
    ·
      refine ⟨68520974855751636641067565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 91361299807668848854756753 68520974855751636641067565)
      ·
        refine ⟨25695365570906863740400337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 68520974855751636641067565 25695365570906863740400337)
        ·
          refine ⟨19271524178180147805300253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25695365570906863740400337 19271524178180147805300253)
          ·
            refine ⟨7226821566817555426987595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19271524178180147805300253 7226821566817555426987595)
            ·
              refine ⟨10840232350226333140481393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7226821566817555426987595 10840232350226333140481393)
              ·
                refine ⟨8130174262669749855361045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10840232350226333140481393 8130174262669749855361045)
                ·
                  refine ⟨381101918562644524470049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8130174262669749855361045 381101918562644524470049)
                  ·
                    rfl

theorem cell23_6679740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 3, 1, 2, 6].length) (baseStart_6679740 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6679740 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6679740 prefixEnd_6679740 := by exact prefixLift 6679740
  have htrace : WordTrace (prefixWord ++ tailWord_6679740) baseStart_6679740 baseEnd_6679740 := by
    simpa [prefixWord, tailWord_6679740, baseEnd_6679740] using wordTrace_append hprefix tailTrace_6679740
  have hstable : (prefixWord ++ tailWord_6679740).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6679740).length < 2 ^ (prefixWord ++ tailWord_6679740).sum := by decide
  have hdescent : baseEnd_6679740 < baseStart_6679740 := by decide
  rcases family_descends (prefixWord ++ tailWord_6679740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6679790 : List Nat := [4, 1, 2, 1, 1, 1, 4, 3, 1, 1, 4]
def baseStart_6679790 : Nat := 118140960795 + 6679790 * 2 ^ 59
def prefixEnd_6679790 : Nat := 4983230072969 + 3 ^ 40 * 6679790 * 2
def baseEnd_6679790 : Nat := 3429942941096525524605211

theorem tailTrace_6679790 : CollatzResearch.WordTrace tailWord_6679790 prefixEnd_6679790 3429942941096525524605211 := by
  unfold tailWord_6679790
  simp only [CollatzResearch.WordTrace]
  refine ⟨30453994558783640269000603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 162421304313512748101336549 30453994558783640269000603)
  ·
    refine ⟨45680991838175460403500905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30453994558783640269000603 45680991838175460403500905)
    ·
      refine ⟨34260743878631595302625679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45680991838175460403500905 34260743878631595302625679)
      ·
        refine ⟨51391115817947392953938519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34260743878631595302625679 51391115817947392953938519)
        ·
          refine ⟨77086673726921089430907779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51391115817947392953938519 77086673726921089430907779)
          ·
            refine ⟨115630010590381634146361669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77086673726921089430907779 115630010590381634146361669)
            ·
              refine ⟨21680626985696556402442813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 115630010590381634146361669 21680626985696556402442813)
              ·
                refine ⟨8130235119636208650916055, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21680626985696556402442813 8130235119636208650916055)
                ·
                  refine ⟨12195352679454312976374083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8130235119636208650916055 12195352679454312976374083)
                  ·
                    refine ⟨18293029019181469464561125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12195352679454312976374083 18293029019181469464561125)
                    ·
                      refine ⟨3429942941096525524605211, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18293029019181469464561125 3429942941096525524605211)
                      ·
                        rfl

theorem cell23_6679790_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 4, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 4, 3, 1, 1, 4].length) (baseStart_6679790 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6679790 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6679790 prefixEnd_6679790 := by exact prefixLift 6679790
  have htrace : WordTrace (prefixWord ++ tailWord_6679790) baseStart_6679790 baseEnd_6679790 := by
    simpa [prefixWord, tailWord_6679790, baseEnd_6679790] using wordTrace_append hprefix tailTrace_6679790
  have hstable : (prefixWord ++ tailWord_6679790).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6679790).length < 2 ^ (prefixWord ++ tailWord_6679790).sum := by decide
  have hdescent : baseEnd_6679790 < baseStart_6679790 := by decide
  rcases family_descends (prefixWord ++ tailWord_6679790) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6679793 : List Nat := [1, 2, 2, 2, 2, 1, 1, 2, 5, 2, 3]
def baseStart_6679793 : Nat := 118140960795 + 6679793 * 2 ^ 59
def prefixEnd_6679793 : Nat := 4983230072969 + 3 ^ 40 * 6679793 * 2
def baseEnd_6679793 : Nat := 3429944481538489012867697

theorem tailTrace_6679793 : CollatzResearch.WordTrace tailWord_6679793 prefixEnd_6679793 3429944481538489012867697 := by
  unfold tailWord_6679793
  simp only [CollatzResearch.WordTrace]
  refine ⟨243632065889258253664364033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162421377259505502442909355 243632065889258253664364033)
  ·
    refine ⟨182724049416943690248273025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 243632065889258253664364033 182724049416943690248273025)
    ·
      refine ⟨137043037062707767686204769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 182724049416943690248273025 137043037062707767686204769)
      ·
        refine ⟨102782277797030825764653577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 137043037062707767686204769 102782277797030825764653577)
        ·
          refine ⟨77086708347773119323490183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 102782277797030825764653577 77086708347773119323490183)
          ·
            refine ⟨115630062521659678985235275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77086708347773119323490183 115630062521659678985235275)
            ·
              refine ⟨173445093782489518477852913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 115630062521659678985235275 173445093782489518477852913)
              ·
                refine ⟨130083820336867138858389685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 173445093782489518477852913 130083820336867138858389685)
                ·
                  refine ⟨12195358156581294267974033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 130083820336867138858389685 12195358156581294267974033)
                  ·
                    refine ⟨9146518617435970700980525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12195358156581294267974033 9146518617435970700980525)
                    ·
                      refine ⟨3429944481538489012867697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9146518617435970700980525 3429944481538489012867697)
                      ·
                        rfl

theorem cell23_6679793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 1, 2, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 1, 2, 5, 2, 3].length) (baseStart_6679793 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6679793 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6679793 prefixEnd_6679793 := by exact prefixLift 6679793
  have htrace : WordTrace (prefixWord ++ tailWord_6679793) baseStart_6679793 baseEnd_6679793 := by
    simpa [prefixWord, tailWord_6679793, baseEnd_6679793] using wordTrace_append hprefix tailTrace_6679793
  have hstable : (prefixWord ++ tailWord_6679793).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6679793).length < 2 ^ (prefixWord ++ tailWord_6679793).sum := by decide
  have hdescent : baseEnd_6679793 < baseStart_6679793 := by decide
  rcases family_descends (prefixWord ++ tailWord_6679793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6679807 : List Nat := [1, 1, 2, 2, 1, 5, 3, 1, 3, 2, 2]
def baseStart_6679807 : Nat := 118140960795 + 6679807 * 2 ^ 59
def prefixEnd_6679807 : Nat := 4983230072969 + 3 ^ 40 * 6679807 * 2
def baseEnd_6679807 : Nat := 3429951670267651958092633

theorem tailTrace_6679807 : CollatzResearch.WordTrace tailWord_6679807 prefixEnd_6679807 3429951670267651958092633 := by
  unfold tailWord_6679807
  simp only [CollatzResearch.WordTrace]
  refine ⟨243632576511207534055373675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162421717674138356036915783 243632576511207534055373675)
  ·
    refine ⟨365448864766811301083060513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 243632576511207534055373675 365448864766811301083060513)
    ·
      refine ⟨274086648575108475812295385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 365448864766811301083060513 274086648575108475812295385)
      ·
        refine ⟨205564986431331356859221539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 274086648575108475812295385 205564986431331356859221539)
        ·
          refine ⟨308347479646997035288832309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 205564986431331356859221539 308347479646997035288832309)
          ·
            refine ⟨28907576216905972058328029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 308347479646997035288832309 28907576216905972058328029)
            ·
              refine ⟨10840341081339739521873011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28907576216905972058328029 10840341081339739521873011)
              ·
                refine ⟨16260511622009609282809517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10840341081339739521873011 16260511622009609282809517)
                ·
                  refine ⟨6097691858253603481053569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16260511622009609282809517 6097691858253603481053569)
                  ·
                    refine ⟨4573268893690202610790177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6097691858253603481053569 4573268893690202610790177)
                    ·
                      refine ⟨3429951670267651958092633, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4573268893690202610790177 3429951670267651958092633)
                      ·
                        rfl

theorem cell23_6679807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 3, 1, 3, 2, 2].length) (baseStart_6679807 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6679807 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6679807 prefixEnd_6679807 := by exact prefixLift 6679807
  have htrace : WordTrace (prefixWord ++ tailWord_6679807) baseStart_6679807 baseEnd_6679807 := by
    simpa [prefixWord, tailWord_6679807, baseEnd_6679807] using wordTrace_append hprefix tailTrace_6679807
  have hstable : (prefixWord ++ tailWord_6679807).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6679807).length < 2 ^ (prefixWord ++ tailWord_6679807).sum := by decide
  have hdescent : baseEnd_6679807 < baseStart_6679807 := by decide
  rcases family_descends (prefixWord ++ tailWord_6679807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6679857 : List Nat := [1, 2, 2, 3, 3, 1, 1, 4, 2, 1, 3]
def baseStart_6679857 : Nat := 118140960795 + 6679857 * 2 ^ 59
def prefixEnd_6679857 : Nat := 4983230072969 + 3 ^ 40 * 6679857 * 2
def baseEnd_6679857 : Nat := 3429977344300376762467403

theorem tailTrace_6679857 : CollatzResearch.WordTrace tailWord_6679857 prefixEnd_6679857 3429977344300376762467403 := by
  unfold tailWord_6679857
  simp only [CollatzResearch.WordTrace]
  refine ⟨243634400161026392594693825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162422933440684261729795883 243634400161026392594693825)
  ·
    refine ⟨182725800120769794446020369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 243634400161026392594693825 182725800120769794446020369)
    ·
      refine ⟨137044350090577345834515277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 182725800120769794446020369 137044350090577345834515277)
      ·
        refine ⟨51391631283966504687943229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 137044350090577345834515277 51391631283966504687943229)
        ·
          refine ⟨19271861731487439257978711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 51391631283966504687943229 19271861731487439257978711)
          ·
            refine ⟨28907792597231158886968067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19271861731487439257978711 28907792597231158886968067)
            ·
              refine ⟨43361688895846738330452101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28907792597231158886968067 43361688895846738330452101)
              ·
                refine ⟨8130316667971263436959769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 43361688895846738330452101 8130316667971263436959769)
                ·
                  refine ⟨6097737500978447577719827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8130316667971263436959769 6097737500978447577719827)
                  ·
                    refine ⟨9146606251467671366579741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6097737500978447577719827 9146606251467671366579741)
                    ·
                      refine ⟨3429977344300376762467403, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9146606251467671366579741 3429977344300376762467403)
                      ·
                        rfl

theorem cell23_6679857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 1, 4, 2, 1, 3].length) (baseStart_6679857 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6679857 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6679857 prefixEnd_6679857 := by exact prefixLift 6679857
  have htrace : WordTrace (prefixWord ++ tailWord_6679857) baseStart_6679857 baseEnd_6679857 := by
    simpa [prefixWord, tailWord_6679857, baseEnd_6679857] using wordTrace_append hprefix tailTrace_6679857
  have hstable : (prefixWord ++ tailWord_6679857).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6679857).length < 2 ^ (prefixWord ++ tailWord_6679857).sum := by decide
  have hdescent : baseEnd_6679857 < baseStart_6679857 := by decide
  rcases family_descends (prefixWord ++ tailWord_6679857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6679858 : List Nat := [3, 2, 1, 1, 4, 3, 2, 2, 1, 2, 2]
def baseStart_6679858 : Nat := 118140960795 + 6679858 * 2 ^ 59
def prefixEnd_6679858 : Nat := 4983230072969 + 3 ^ 40 * 6679858 * 2
def baseEnd_6679858 : Nat := 3429977857781031258554899

theorem tailTrace_6679858 : CollatzResearch.WordTrace tailWord_6679858 prefixEnd_6679858 3429977857781031258554899 := by
  unfold tailWord_6679858
  simp only [CollatzResearch.WordTrace]
  refine ⟨60908609158505692441370057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 162422957756015179843653485 60908609158505692441370057)
  ·
    refine ⟨45681456868879269331027543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60908609158505692441370057 45681456868879269331027543)
    ·
      refine ⟨68522185303318903996541315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45681456868879269331027543 68522185303318903996541315)
      ·
        refine ⟨102783277954978355994811973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68522185303318903996541315 102783277954978355994811973)
        ·
          refine ⟨19271864616558441749027245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 102783277954978355994811973 19271864616558441749027245)
          ·
            refine ⟨7226949231209415655885217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19271864616558441749027245 7226949231209415655885217)
            ·
              refine ⟨5420211923407061741913913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7226949231209415655885217 5420211923407061741913913)
              ·
                refine ⟨4065158942555296306435435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5420211923407061741913913 4065158942555296306435435)
                ·
                  refine ⟨6097738413832944459653153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4065158942555296306435435 6097738413832944459653153)
                  ·
                    refine ⟨4573303810374708344739865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6097738413832944459653153 4573303810374708344739865)
                    ·
                      refine ⟨3429977857781031258554899, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4573303810374708344739865 3429977857781031258554899)
                      ·
                        rfl

theorem cell23_6679858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 3, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 3, 2, 2, 1, 2, 2].length) (baseStart_6679858 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6679858 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6679858 prefixEnd_6679858 := by exact prefixLift 6679858
  have htrace : WordTrace (prefixWord ++ tailWord_6679858) baseStart_6679858 baseEnd_6679858 := by
    simpa [prefixWord, tailWord_6679858, baseEnd_6679858] using wordTrace_append hprefix tailTrace_6679858
  have hstable : (prefixWord ++ tailWord_6679858).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6679858).length < 2 ^ (prefixWord ++ tailWord_6679858).sum := by decide
  have hdescent : baseEnd_6679858 < baseStart_6679858 := by decide
  rcases family_descends (prefixWord ++ tailWord_6679858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6679920 : List Nat := [2, 1, 1, 1, 4, 2, 1, 6, 5]
def baseStart_6679920 : Nat := 118140960795 + 6679920 * 2 ^ 59
def prefixEnd_6679920 : Nat := 4983230072969 + 3 ^ 40 * 6679920 * 2
def baseEnd_6679920 : Nat := 381112188175734446219957

theorem tailTrace_6679920 : CollatzResearch.WordTrace tailWord_6679920 prefixEnd_6679920 381112188175734446219957 := by
  unfold tailWord_6679920
  simp only [CollatzResearch.WordTrace]
  refine ⟨121818348979899077177118607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 162424465306532102902824809 121818348979899077177118607)
  ·
    refine ⟨182727523469848615765677911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121818348979899077177118607 182727523469848615765677911)
    ·
      refine ⟨274091285204772923648516867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 182727523469848615765677911 274091285204772923648516867)
      ·
        refine ⟨411136927807159385472775301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 274091285204772923648516867 411136927807159385472775301)
        ·
          refine ⟨77088173963842384776145369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 411136927807159385472775301 77088173963842384776145369)
          ·
            refine ⟨57816130472881788582109027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 77088173963842384776145369 57816130472881788582109027)
            ·
              refine ⟨86724195709322682873163541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57816130472881788582109027 86724195709322682873163541)
              ·
                refine ⟨4065196673874500759679541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 86724195709322682873163541 4065196673874500759679541)
                ·
                  refine ⟨381112188175734446219957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4065196673874500759679541 381112188175734446219957)
                  ·
                    rfl

theorem cell23_6679920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 1, 6, 5].length) (baseStart_6679920 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6679920 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6679920 prefixEnd_6679920 := by exact prefixLift 6679920
  have htrace : WordTrace (prefixWord ++ tailWord_6679920) baseStart_6679920 baseEnd_6679920 := by
    simpa [prefixWord, tailWord_6679920, baseEnd_6679920] using wordTrace_append hprefix tailTrace_6679920
  have hstable : (prefixWord ++ tailWord_6679920).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6679920).length < 2 ^ (prefixWord ++ tailWord_6679920).sum := by decide
  have hdescent : baseEnd_6679920 < baseStart_6679920 := by decide
  rcases family_descends (prefixWord ++ tailWord_6679920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6679933 : List Nat := [1, 4, 1, 1, 2, 2, 1, 1, 3, 7]
def baseStart_6679933 : Nat := 118140960795 + 6679933 * 2 ^ 59
def prefixEnd_6679933 : Nat := 4983230072969 + 3 ^ 40 * 6679933 * 2
def baseEnd_6679933 : Nat := 1143338789610039488372351

theorem tailTrace_6679933 : CollatzResearch.WordTrace tailWord_6679933 prefixEnd_6679933 1143338789610039488372351 := by
  unfold tailWord_6679933
  simp only [CollatzResearch.WordTrace]
  refine ⟨243637172108751057574460453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162424781405834038382973635 243637172108751057574460453)
  ·
    refine ⟨45681969770390823295211335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 243637172108751057574460453 45681969770390823295211335)
    ·
      refine ⟨68522954655586234942817003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45681969770390823295211335 68522954655586234942817003)
      ·
        refine ⟨102784431983379352414225505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68522954655586234942817003 102784431983379352414225505)
        ·
          refine ⟨77088323987534514310669129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 102784431983379352414225505 77088323987534514310669129)
          ·
            refine ⟨57816242990650885733001847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 77088323987534514310669129 57816242990650885733001847)
            ·
              refine ⟨86724364485976328599502771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57816242990650885733001847 86724364485976328599502771)
              ·
                refine ⟨130086546728964492899254157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 86724364485976328599502771 130086546728964492899254157)
                ·
                  refine ⟨48782455023361684837220309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 130086546728964492899254157 48782455023361684837220309)
                  ·
                    refine ⟨1143338789610039488372351, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 48782455023361684837220309 1143338789610039488372351)
                    ·
                      rfl

theorem cell23_6679933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 1, 1, 3, 7].length) (baseStart_6679933 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6679933 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6679933 prefixEnd_6679933 := by exact prefixLift 6679933
  have htrace : WordTrace (prefixWord ++ tailWord_6679933) baseStart_6679933 baseEnd_6679933 := by
    simpa [prefixWord, tailWord_6679933, baseEnd_6679933] using wordTrace_append hprefix tailTrace_6679933
  have hstable : (prefixWord ++ tailWord_6679933).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6679933).length < 2 ^ (prefixWord ++ tailWord_6679933).sum := by decide
  have hdescent : baseEnd_6679933 < baseStart_6679933 := by decide
  rcases family_descends (prefixWord ++ tailWord_6679933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6679973 : List Nat := [1, 3, 1, 2, 1, 1, 2, 1, 1, 5, 5]
def baseStart_6679973 : Nat := 118140960795 + 6679973 * 2 ^ 59
def prefixEnd_6679973 : Nat := 4983230072969 + 3 ^ 40 * 6679973 * 2
def baseEnd_6679973 : Nat := 3430036908056298308616869

theorem tailTrace_6679973 : CollatzResearch.WordTrace tailWord_6679973 prefixEnd_6679973 3430036908056298308616869 := by
  unfold tailWord_6679973
  simp only [CollatzResearch.WordTrace]
  refine ⟨243638631028606144405916573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162425754019070762937277715 243638631028606144405916573)
  ·
    refine ⟨91364486635727304152218715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 243638631028606144405916573 91364486635727304152218715)
    ·
      refine ⟨137046729953590956228328073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91364486635727304152218715 137046729953590956228328073)
      ·
        refine ⟨102785047465193217171246055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 137046729953590956228328073 102785047465193217171246055)
        ·
          refine ⟨154177571197789825756869083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 102785047465193217171246055 154177571197789825756869083)
          ·
            refine ⟨231266356796684738635303625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 154177571197789825756869083 231266356796684738635303625)
            ·
              refine ⟨173449767597513553976477719, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 231266356796684738635303625 173449767597513553976477719)
              ·
                refine ⟨260174651396270330964716579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 173449767597513553976477719 260174651396270330964716579)
                ·
                  refine ⟨390261977094405496447074869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 260174651396270330964716579 390261977094405496447074869)
                  ·
                    refine ⟨36587060352600515291913269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 390261977094405496447074869 36587060352600515291913269)
                    ·
                      refine ⟨3430036908056298308616869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36587060352600515291913269 3430036908056298308616869)
                      ·
                        rfl

theorem cell23_6679973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 2, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 2, 1, 1, 5, 5].length) (baseStart_6679973 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6679973 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6679973 prefixEnd_6679973 := by exact prefixLift 6679973
  have htrace : WordTrace (prefixWord ++ tailWord_6679973) baseStart_6679973 baseEnd_6679973 := by
    simpa [prefixWord, tailWord_6679973, baseEnd_6679973] using wordTrace_append hprefix tailTrace_6679973
  have hstable : (prefixWord ++ tailWord_6679973).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6679973).length < 2 ^ (prefixWord ++ tailWord_6679973).sum := by decide
  have hdescent : baseEnd_6679973 < baseStart_6679973 := by decide
  rcases family_descends (prefixWord ++ tailWord_6679973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6679983 : List Nat := [1, 1, 2, 1, 2, 2, 1, 4, 2, 1, 6]
def baseStart_6679983 : Nat := 118140960795 + 6679983 * 2 ^ 59
def prefixEnd_6679983 : Nat := 4983230072969 + 3 ^ 40 * 6679983 * 2
def baseEnd_6679983 : Nat := 3430042042862843269491823

theorem tailTrace_6679983 : CollatzResearch.WordTrace tailWord_6679983 prefixEnd_6679983 3430042042862843269491823 := by
  unfold tailWord_6679983
  simp only [CollatzResearch.WordTrace]
  refine ⟨243638995758569916113780603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162425997172379944075853735 243638995758569916113780603)
  ·
    refine ⟨365458493637854874170670905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 243638995758569916113780603 365458493637854874170670905)
    ·
      refine ⟨274093870228391155628003179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 365458493637854874170670905 274093870228391155628003179)
      ·
        refine ⟨411140805342586733442004769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 274093870228391155628003179 411140805342586733442004769)
        ·
          refine ⟨308355604006940050081503577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 411140805342586733442004769 308355604006940050081503577)
          ·
            refine ⟨231266703005205037561127683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 308355604006940050081503577 231266703005205037561127683)
            ·
              refine ⟨346900054507807556341691525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 231266703005205037561127683 346900054507807556341691525)
              ·
                refine ⟨65043760220213916814067161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 346900054507807556341691525 65043760220213916814067161)
                ·
                  refine ⟨48782820165160437610550371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 65043760220213916814067161 48782820165160437610550371)
                  ·
                    refine ⟨73174230247740656415825557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 48782820165160437610550371 73174230247740656415825557)
                    ·
                      refine ⟨3430042042862843269491823, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 73174230247740656415825557 3430042042862843269491823)
                      ·
                        rfl

theorem cell23_6679983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 4, 2, 1, 6].length) (baseStart_6679983 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6679983 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6679983 prefixEnd_6679983 := by exact prefixLift 6679983
  have htrace : WordTrace (prefixWord ++ tailWord_6679983) baseStart_6679983 baseEnd_6679983 := by
    simpa [prefixWord, tailWord_6679983, baseEnd_6679983] using wordTrace_append hprefix tailTrace_6679983
  have hstable : (prefixWord ++ tailWord_6679983).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6679983).length < 2 ^ (prefixWord ++ tailWord_6679983).sum := by decide
  have hdescent : baseEnd_6679983 < baseStart_6679983 := by decide
  rcases family_descends (prefixWord ++ tailWord_6679983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6680004 : List Nat := [2, 3, 3, 2, 1, 2, 2, 1, 2, 1, 4]
def baseStart_6680004 : Nat := 118140960795 + 6680004 * 2 ^ 59
def prefixEnd_6680004 : Nat := 4983230072969 + 3 ^ 40 * 6680004 * 2
def baseEnd_6680004 : Nat := 3430052825956587687329227

theorem tailTrace_6680004 : CollatzResearch.WordTrace tailWord_6680004 prefixEnd_6680004 3430052825956587687329227 := by
  unfold tailWord_6680004
  simp only [CollatzResearch.WordTrace]
  refine ⟨121819880845746918350147533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 162426507794329224466863377 121819880845746918350147533)
  ·
    refine ⟨45682455317155094381305325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 121819880845746918350147533 45682455317155094381305325)
    ·
      refine ⟨17130920743933160392989497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 45682455317155094381305325 17130920743933160392989497)
      ·
        refine ⟨12848190557949870294742123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17130920743933160392989497 12848190557949870294742123)
        ·
          refine ⟨19272285836924805442113185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12848190557949870294742123 19272285836924805442113185)
          ·
            refine ⟨14454214377693604081584889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19272285836924805442113185 14454214377693604081584889)
            ·
              refine ⟨10840660783270203061188667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14454214377693604081584889 10840660783270203061188667)
              ·
                refine ⟨16260991174905304591783001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10840660783270203061188667 16260991174905304591783001)
                ·
                  refine ⟨12195743381178978443837251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16260991174905304591783001 12195743381178978443837251)
                  ·
                    refine ⟨18293615071768467665755877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12195743381178978443837251 18293615071768467665755877)
                    ·
                      refine ⟨3430052825956587687329227, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18293615071768467665755877 3430052825956587687329227)
                      ·
                        rfl

theorem cell23_6680004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 2, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 2, 2, 1, 2, 1, 4].length) (baseStart_6680004 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6680004 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6680004 prefixEnd_6680004 := by exact prefixLift 6680004
  have htrace : WordTrace (prefixWord ++ tailWord_6680004) baseStart_6680004 baseEnd_6680004 := by
    simpa [prefixWord, tailWord_6680004, baseEnd_6680004] using wordTrace_append hprefix tailTrace_6680004
  have hstable : (prefixWord ++ tailWord_6680004).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6680004).length < 2 ^ (prefixWord ++ tailWord_6680004).sum := by decide
  have hdescent : baseEnd_6680004 < baseStart_6680004 := by decide
  rcases family_descends (prefixWord ++ tailWord_6680004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6680007 : List Nat := [1, 1, 4, 1, 1, 3, 4, 1, 2, 2, 3]
def baseStart_6680007 : Nat := 118140960795 + 6680007 * 2 ^ 59
def prefixEnd_6680007 : Nat := 4983230072969 + 3 ^ 40 * 6680007 * 2
def baseEnd_6680007 : Nat := 3430054366398551175591713

theorem tailTrace_6680007 : CollatzResearch.WordTrace tailWord_6680007 prefixEnd_6680007 3430054366398551175591713 := by
  unfold tailWord_6680007
  simp only [CollatzResearch.WordTrace]
  refine ⟨243639871110482968212654275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162426580740321978808436183 243639871110482968212654275)
  ·
    refine ⟨365459806665724452318981413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 243639871110482968212654275 365459806665724452318981413)
    ·
      refine ⟨68523713749823334809809015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 365459806665724452318981413 68523713749823334809809015)
      ·
        refine ⟨102785570624735002214713523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68523713749823334809809015 102785570624735002214713523)
        ·
          refine ⟨154178355937102503322070285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 102785570624735002214713523 154178355937102503322070285)
          ·
            refine ⟨57816883476413438745776357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 154178355937102503322070285 57816883476413438745776357)
            ·
              refine ⟨10840665651827519764833067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 57816883476413438745776357 10840665651827519764833067)
              ·
                refine ⟨16260998477741279647249601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10840665651827519764833067 16260998477741279647249601)
                ·
                  refine ⟨12195748858305959735437201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16260998477741279647249601 12195748858305959735437201)
                  ·
                    refine ⟨9146811643729469801577901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12195748858305959735437201 9146811643729469801577901)
                    ·
                      refine ⟨3430054366398551175591713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9146811643729469801577901 3430054366398551175591713)
                      ·
                        rfl

theorem cell23_6680007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 4, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 4, 1, 2, 2, 3].length) (baseStart_6680007 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6680007 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6680007 prefixEnd_6680007 := by exact prefixLift 6680007
  have htrace : WordTrace (prefixWord ++ tailWord_6680007) baseStart_6680007 baseEnd_6680007 := by
    simpa [prefixWord, tailWord_6680007, baseEnd_6680007] using wordTrace_append hprefix tailTrace_6680007
  have hstable : (prefixWord ++ tailWord_6680007).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6680007).length < 2 ^ (prefixWord ++ tailWord_6680007).sum := by decide
  have hdescent : baseEnd_6680007 < baseStart_6680007 := by decide
  rcases family_descends (prefixWord ++ tailWord_6680007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6680040 : List Nat := [2, 1, 4, 1, 1, 2, 1, 1, 5, 5]
def baseStart_6680040 : Nat := 118140960795 + 6680040 * 2 ^ 59
def prefixEnd_6680040 : Nat := 4983230072969 + 3 ^ 40 * 6680040 * 2
def baseEnd_6680040 : Nat := 1143357103753383182159687

theorem tailTrace_6680040 : CollatzResearch.WordTrace tailWord_6680040 prefixEnd_6680040 1143357103753383182159687 := by
  unfold tailWord_6680040
  simp only [CollatzResearch.WordTrace]
  refine ⟨121820537359681707424302787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 162427383146242276565737049 121820537359681707424302787)
  ·
    refine ⟨182730806039522561136454181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121820537359681707424302787 182730806039522561136454181)
    ·
      refine ⟨34262026132410480213085159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 182730806039522561136454181 34262026132410480213085159)
      ·
        refine ⟨51393039198615720319627739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34262026132410480213085159 51393039198615720319627739)
        ·
          refine ⟨77089558797923580479441609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51393039198615720319627739 77089558797923580479441609)
          ·
            refine ⟨57817169098442685359581207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 77089558797923580479441609 57817169098442685359581207)
            ·
              refine ⟨86725753647664028039371811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57817169098442685359581207 86725753647664028039371811)
              ·
                refine ⟨130088630471496042059057717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 86725753647664028039371811 130088630471496042059057717)
                ·
                  refine ⟨12195809106702753943036661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 130088630471496042059057717 12195809106702753943036661)
                  ·
                    refine ⟨1143357103753383182159687, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12195809106702753943036661 1143357103753383182159687)
                    ·
                      rfl

theorem cell23_6680040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 1, 1, 5, 5].length) (baseStart_6680040 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6680040 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6680040 prefixEnd_6680040 := by exact prefixLift 6680040
  have htrace : WordTrace (prefixWord ++ tailWord_6680040) baseStart_6680040 baseEnd_6680040 := by
    simpa [prefixWord, tailWord_6680040, baseEnd_6680040] using wordTrace_append hprefix tailTrace_6680040
  have hstable : (prefixWord ++ tailWord_6680040).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6680040).length < 2 ^ (prefixWord ++ tailWord_6680040).sum := by decide
  have hdescent : baseEnd_6680040 < baseStart_6680040 := by decide
  rcases family_descends (prefixWord ++ tailWord_6680040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6680047 : List Nat := [1, 1, 2, 1, 4, 1, 2, 2, 4, 3, 2]
def baseStart_6680047 : Nat := 118140960795 + 6680047 * 2 ^ 59
def prefixEnd_6680047 : Nat := 4983230072969 + 3 ^ 40 * 6680047 * 2
def baseEnd_6680047 : Nat := 3430074905624731019091529

theorem tailTrace_6680047 : CollatzResearch.WordTrace tailWord_6680047 prefixEnd_6680047 3430074905624731019091529 := by
  unfold tailWord_6680047
  simp only [CollatzResearch.WordTrace]
  refine ⟨243641330030338055044110395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162427553353558703362740263 243641330030338055044110395)
  ·
    refine ⟨365461995045507082566165593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 243641330030338055044110395 365461995045507082566165593)
    ·
      refine ⟨274096496284130311924624195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 365461995045507082566165593 274096496284130311924624195)
      ·
        refine ⟨411144744426195467886936293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 274096496284130311924624195 411144744426195467886936293)
        ·
          refine ⟨77089639579911650228800555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 411144744426195467886936293 77089639579911650228800555)
          ·
            refine ⟨115634459369867475343200833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77089639579911650228800555 115634459369867475343200833)
            ·
              refine ⟨86725844527400606507400625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 115634459369867475343200833 86725844527400606507400625)
              ·
                refine ⟨65044383395550454880550469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 86725844527400606507400625 65044383395550454880550469)
                ·
                  refine ⟨12195821886665710290103213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 65044383395550454880550469 12195821886665710290103213)
                  ·
                    refine ⟨4573433207499641358788705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12195821886665710290103213 4573433207499641358788705)
                    ·
                      refine ⟨3430074905624731019091529, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4573433207499641358788705 3430074905624731019091529)
                      ·
                        rfl

theorem cell23_6680047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 2, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 2, 2, 4, 3, 2].length) (baseStart_6680047 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6680047 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6680047 prefixEnd_6680047 := by exact prefixLift 6680047
  have htrace : WordTrace (prefixWord ++ tailWord_6680047) baseStart_6680047 baseEnd_6680047 := by
    simpa [prefixWord, tailWord_6680047, baseEnd_6680047] using wordTrace_append hprefix tailTrace_6680047
  have hstable : (prefixWord ++ tailWord_6680047).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6680047).length < 2 ^ (prefixWord ++ tailWord_6680047).sum := by decide
  have hdescent : baseEnd_6680047 < baseStart_6680047 := by decide
  rcases family_descends (prefixWord ++ tailWord_6680047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6680054 : List Nat := [5, 1, 1, 1, 2, 2, 1, 1, 5, 1, 3]
def baseStart_6680054 : Nat := 118140960795 + 6680054 * 2 ^ 59
def prefixEnd_6680054 : Nat := 4983230072969 + 3 ^ 40 * 6680054 * 2
def baseEnd_6680054 : Nat := 3430078499989312491703997

theorem tailTrace_6680054 : CollatzResearch.WordTrace tailWord_6680054 prefixEnd_6680054 3430078499989312491703997 := by
  unfold tailWord_6680054
  simp only [CollatzResearch.WordTrace]
  refine ⟨15227599083832043452475951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 162427723560875130159743477 15227599083832043452475951)
  ·
    refine ⟨22841398625748065178713927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15227599083832043452475951 22841398625748065178713927)
    ·
      refine ⟨34262097938622097768070891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22841398625748065178713927 34262097938622097768070891)
      ·
        refine ⟨51393146907933146652106337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34262097938622097768070891 51393146907933146652106337)
        ·
          refine ⟨38544860180949859989079753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51393146907933146652106337 38544860180949859989079753)
          ·
            refine ⟨28908645135712394991809815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38544860180949859989079753 28908645135712394991809815)
            ·
              refine ⟨43362967703568592487714723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28908645135712394991809815 43362967703568592487714723)
              ·
                refine ⟨65044451555352888731572085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43362967703568592487714723 65044451555352888731572085)
                ·
                  refine ⟨6097917333314333318584883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 65044451555352888731572085 6097917333314333318584883)
                  ·
                    refine ⟨9146875999971499977877325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6097917333314333318584883 9146875999971499977877325)
                    ·
                      refine ⟨3430078499989312491703997, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9146875999971499977877325 3430078499989312491703997)
                      ·
                        rfl

theorem cell23_6680054_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 1, 1, 5, 1, 3].length) (baseStart_6680054 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6680054 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6680054 prefixEnd_6680054 := by exact prefixLift 6680054
  have htrace : WordTrace (prefixWord ++ tailWord_6680054) baseStart_6680054 baseEnd_6680054 := by
    simpa [prefixWord, tailWord_6680054, baseEnd_6680054] using wordTrace_append hprefix tailTrace_6680054
  have hstable : (prefixWord ++ tailWord_6680054).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6680054).length < 2 ^ (prefixWord ++ tailWord_6680054).sum := by decide
  have hdescent : baseEnd_6680054 < baseStart_6680054 := by decide
  rcases family_descends (prefixWord ++ tailWord_6680054) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6680071 : List Nat := [1, 1, 4, 3, 2, 1, 1, 5, 1, 1, 3]
def baseStart_6680071 : Nat := 118140960795 + 6680071 * 2 ^ 59
def prefixEnd_6680071 : Nat := 4983230072969 + 3 ^ 40 * 6680071 * 2
def baseEnd_6680071 : Nat := 3430087229160438925191419

theorem tailTrace_6680071 : CollatzResearch.WordTrace tailWord_6680071 prefixEnd_6680071 3430087229160438925191419 := by
  unfold tailWord_6680071
  simp only [CollatzResearch.WordTrace]
  refine ⟨243642205382251107142984067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162428136921500738095322711 243642205382251107142984067)
  ·
    refine ⟨365463308073376660714476101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 243642205382251107142984067 365463308073376660714476101)
    ·
      refine ⟨68524370263758123883964269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 365463308073376660714476101 68524370263758123883964269)
      ·
        refine ⟨25696638848909296456486601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 68524370263758123883964269 25696638848909296456486601)
        ·
          refine ⟨19272479136681972342364951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25696638848909296456486601 19272479136681972342364951)
          ·
            refine ⟨28908718705022958513547427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19272479136681972342364951 28908718705022958513547427)
            ·
              refine ⟨43363078057534437770321141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28908718705022958513547427 43363078057534437770321141)
              ·
                refine ⟨4065288567893853540967607, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 43363078057534437770321141 4065288567893853540967607)
                ·
                  refine ⟨6097932851840780311451411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4065288567893853540967607 6097932851840780311451411)
                  ·
                    refine ⟨9146899277761170467177117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6097932851840780311451411 9146899277761170467177117)
                    ·
                      refine ⟨3430087229160438925191419, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9146899277761170467177117 3430087229160438925191419)
                      ·
                        rfl

theorem cell23_6680071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 1, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 1, 5, 1, 1, 3].length) (baseStart_6680071 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6680071 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6680071 prefixEnd_6680071 := by exact prefixLift 6680071
  have htrace : WordTrace (prefixWord ++ tailWord_6680071) baseStart_6680071 baseEnd_6680071 := by
    simpa [prefixWord, tailWord_6680071, baseEnd_6680071] using wordTrace_append hprefix tailTrace_6680071
  have hstable : (prefixWord ++ tailWord_6680071).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6680071).length < 2 ^ (prefixWord ++ tailWord_6680071).sum := by decide
  have hdescent : baseEnd_6680071 < baseStart_6680071 := by decide
  rcases family_descends (prefixWord ++ tailWord_6680071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6680074 : List Nat := [3, 1, 2, 2, 2, 2, 4, 1, 1, 5]
def baseStart_6680074 : Nat := 118140960795 + 6680074 * 2 ^ 59
def prefixEnd_6680074 : Nat := 4983230072969 + 3 ^ 40 * 6680074 * 2
def baseEnd_6680074 : Nat := 1143362923200800804484635

theorem tailTrace_6680074 : CollatzResearch.WordTrace tailWord_6680074 prefixEnd_6680074 1143362923200800804484635 := by
  unfold tailWord_6680074
  simp only [CollatzResearch.WordTrace]
  refine ⟨60910578700310059663835819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 162428209867493492436895517 60910578700310059663835819)
  ·
    refine ⟨91365868050465089495753729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60910578700310059663835819 91365868050465089495753729)
    ·
      refine ⟨68524401037848817121815297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 91365868050465089495753729 68524401037848817121815297)
      ·
        refine ⟨51393300778386612841361473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68524401037848817121815297 51393300778386612841361473)
        ·
          refine ⟨38544975583789959631021105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51393300778386612841361473 38544975583789959631021105)
          ·
            refine ⟨28908731687842469723265829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38544975583789959631021105 28908731687842469723265829)
            ·
              refine ⟨5420387191470463073112343, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 28908731687842469723265829 5420387191470463073112343)
              ·
                refine ⟨8130580787205694609668515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5420387191470463073112343 8130580787205694609668515)
                ·
                  refine ⟨12195871180808541914502773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8130580787205694609668515 12195871180808541914502773)
                  ·
                    refine ⟨1143362923200800804484635, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12195871180808541914502773 1143362923200800804484635)
                    ·
                      rfl

theorem cell23_6680074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 4, 1, 1, 5].length) (baseStart_6680074 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6680074 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6680074 prefixEnd_6680074 := by exact prefixLift 6680074
  have htrace : WordTrace (prefixWord ++ tailWord_6680074) baseStart_6680074 baseEnd_6680074 := by
    simpa [prefixWord, tailWord_6680074, baseEnd_6680074] using wordTrace_append hprefix tailTrace_6680074
  have hstable : (prefixWord ++ tailWord_6680074).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6680074).length < 2 ^ (prefixWord ++ tailWord_6680074).sum := by decide
  have hdescent : baseEnd_6680074 < baseStart_6680074 := by decide
  rcases family_descends (prefixWord ++ tailWord_6680074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6680090 : List Nat := [3, 1, 1, 3, 1, 1, 1, 4, 1, 1, 6]
def baseStart_6680090 : Nat := 118140960795 + 6680090 * 2 ^ 59
def prefixEnd_6680090 : Nat := 4983230072969 + 3 ^ 40 * 6680090 * 2
def baseEnd_6680090 : Nat := 3430096985292874350853831

theorem tailTrace_6680090 : CollatzResearch.WordTrace tailWord_6680090 prefixEnd_6680090 3430096985292874350853831 := by
  unfold tailWord_6680090
  simp only [CollatzResearch.WordTrace]
  refine ⟨60910724592295568346981431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 162428598912788182258617149 60910724592295568346981431)
  ·
    refine ⟨91366086888443352520472147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60910724592295568346981431 91366086888443352520472147)
    ·
      refine ⟨137049130332665028780708221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91366086888443352520472147 137049130332665028780708221)
      ·
        refine ⟨51393423874749385792765583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 137049130332665028780708221 51393423874749385792765583)
        ·
          refine ⟨77090135812124078689148375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51393423874749385792765583 77090135812124078689148375)
          ·
            refine ⟨115635203718186118033722563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77090135812124078689148375 115635203718186118033722563)
            ·
              refine ⟨173452805577279177050583845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 115635203718186118033722563 173452805577279177050583845)
              ·
                refine ⟨32522401045739845696984471, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 173452805577279177050583845 32522401045739845696984471)
                ·
                  refine ⟨48783601568609768545476707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32522401045739845696984471 48783601568609768545476707)
                  ·
                    refine ⟨73175402352914652818215061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 48783601568609768545476707 73175402352914652818215061)
                    ·
                      refine ⟨3430096985292874350853831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 73175402352914652818215061 3430096985292874350853831)
                      ·
                        rfl

theorem cell23_6680090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 1, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 1, 4, 1, 1, 6].length) (baseStart_6680090 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6680090 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6680090 prefixEnd_6680090 := by exact prefixLift 6680090
  have htrace : WordTrace (prefixWord ++ tailWord_6680090) baseStart_6680090 baseEnd_6680090 := by
    simpa [prefixWord, tailWord_6680090, baseEnd_6680090] using wordTrace_append hprefix tailTrace_6680090
  have hstable : (prefixWord ++ tailWord_6680090).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6680090).length < 2 ^ (prefixWord ++ tailWord_6680090).sum := by decide
  have hdescent : baseEnd_6680090 < baseStart_6680090 := by decide
  rcases family_descends (prefixWord ++ tailWord_6680090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6680097 : List Nat := [1, 2, 3, 2, 2, 3, 1, 2, 1, 1, 5]
def baseStart_6680097 : Nat := 118140960795 + 6680097 * 2 ^ 59
def prefixEnd_6680097 : Nat := 4983230072969 + 3 ^ 40 * 6680097 * 2
def baseEnd_6680097 : Nat := 3430100579657455823466299

theorem tailTrace_6680097 : CollatzResearch.WordTrace tailWord_6680097 prefixEnd_6680097 3430100579657455823466299 := by
  unfold tailWord_6680097
  simp only [CollatzResearch.WordTrace]
  refine ⟨243643153680156913583430545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162428769120104609055620363 243643153680156913583430545)
  ·
    refine ⟨182732365260117685187572909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 243643153680156913583430545 182732365260117685187572909)
    ·
      refine ⟨68524636972544131945339841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 182732365260117685187572909 68524636972544131945339841)
      ·
        refine ⟨51393477729408098959004881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68524636972544131945339841 51393477729408098959004881)
        ·
          refine ⟨38545108297056074219253661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51393477729408098959004881 38545108297056074219253661)
          ·
            refine ⟨14454415611396027832220123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38545108297056074219253661 14454415611396027832220123)
            ·
              refine ⟨21681623417094041748330185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14454415611396027832220123 21681623417094041748330185)
              ·
                refine ⟨16261217562820531311247639, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21681623417094041748330185 16261217562820531311247639)
                ·
                  refine ⟨24391826344230796966871459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16261217562820531311247639 24391826344230796966871459)
                  ·
                    refine ⟨36587739516346195450307189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24391826344230796966871459 36587739516346195450307189)
                    ·
                      refine ⟨3430100579657455823466299, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36587739516346195450307189 3430100579657455823466299)
                      ·
                        rfl

theorem cell23_6680097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 3, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 3, 1, 2, 1, 1, 5].length) (baseStart_6680097 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6680097 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6680097 prefixEnd_6680097 := by exact prefixLift 6680097
  have htrace : WordTrace (prefixWord ++ tailWord_6680097) baseStart_6680097 baseEnd_6680097 := by
    simpa [prefixWord, tailWord_6680097, baseEnd_6680097] using wordTrace_append hprefix tailTrace_6680097
  have hstable : (prefixWord ++ tailWord_6680097).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6680097).length < 2 ^ (prefixWord ++ tailWord_6680097).sum := by decide
  have hdescent : baseEnd_6680097 < baseStart_6680097 := by decide
  rcases family_descends (prefixWord ++ tailWord_6680097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6680117 : List Nat := [1, 3, 3, 1, 1, 3, 4, 7]
def baseStart_6680117 : Nat := 118140960795 + 6680117 * 2 ^ 59
def prefixEnd_6680117 : Nat := 4983230072969 + 3 ^ 40 * 6680117 * 2
def baseEnd_6680117 : Nat := 127041142565575768341341

theorem tailTrace_6680117 : CollatzResearch.WordTrace tailWord_6680117 prefixEnd_6680117 127041142565575768341341 := by
  unfold tailWord_6680117
  simp only [CollatzResearch.WordTrace]
  refine ⟨243643883140084456999158605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162429255426722971332772403 243643883140084456999158605)
  ·
    refine ⟨91366456177531671374684477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 243643883140084456999158605 91366456177531671374684477)
    ·
      refine ⟨34262421066574376765506679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 91366456177531671374684477 34262421066574376765506679)
      ·
        refine ⟨51393631599861565148260019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34262421066574376765506679 51393631599861565148260019)
        ·
          refine ⟨77090447399792347722390029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51393631599861565148260019 77090447399792347722390029)
          ·
            refine ⟨28908917774922130395896261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 77090447399792347722390029 28908917774922130395896261)
            ·
              refine ⟨5420422082797899449230549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 28908917774922130395896261 5420422082797899449230549)
              ·
                refine ⟨127041142565575768341341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5420422082797899449230549 127041142565575768341341)
                ·
                  rfl

theorem cell23_6680117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 4, 7].length) (baseStart_6680117 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6680117 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6680117 prefixEnd_6680117 := by exact prefixLift 6680117
  have htrace : WordTrace (prefixWord ++ tailWord_6680117) baseStart_6680117 baseEnd_6680117 := by
    simpa [prefixWord, tailWord_6680117, baseEnd_6680117] using wordTrace_append hprefix tailTrace_6680117
  have hstable : (prefixWord ++ tailWord_6680117).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6680117).length < 2 ^ (prefixWord ++ tailWord_6680117).sum := by decide
  have hdescent : baseEnd_6680117 < baseStart_6680117 := by decide
  rcases family_descends (prefixWord ++ tailWord_6680117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6680144 : List Nat := [2, 1, 1, 1, 1, 3, 4, 4, 2, 1, 3]
def baseStart_6680144 : Nat := 118140960795 + 6680144 * 2 ^ 59
def prefixEnd_6680144 : Nat := 4983230072969 + 3 ^ 40 * 6680144 * 2
def baseEnd_6680144 : Nat := 3430124713248217139578583

theorem tailTrace_6680144 : CollatzResearch.WordTrace tailWord_6680144 prefixEnd_6680144 3430124713248217139578583 := by
  unfold tailWord_6680144
  simp only [CollatzResearch.WordTrace]
  refine ⟨121822433955493320305195743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 162429911940657760406927657 121822433955493320305195743)
  ·
    refine ⟨182733650933239980457793615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121822433955493320305195743 182733650933239980457793615)
    ·
      refine ⟨274100476399859970686690423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 182733650933239980457793615 274100476399859970686690423)
      ·
        refine ⟨411150714599789956030035635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 274100476399859970686690423 411150714599789956030035635)
        ·
          refine ⟨616726071899684934045053453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 411150714599789956030035635 616726071899684934045053453)
          ·
            refine ⟨231272276962381850266895045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 616726071899684934045053453 231272276962381850266895045)
            ·
              refine ⟨43363551930446596925042821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 231272276962381850266895045 43363551930446596925042821)
              ·
                refine ⟨8130665986958736923445529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 43363551930446596925042821 8130665986958736923445529)
                ·
                  refine ⟨6097999490219052692584147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8130665986958736923445529 6097999490219052692584147)
                  ·
                    refine ⟨9146999235328579038876221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6097999490219052692584147 9146999235328579038876221)
                    ·
                      refine ⟨3430124713248217139578583, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9146999235328579038876221 3430124713248217139578583)
                      ·
                        rfl

theorem cell23_6680144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 4, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 4, 4, 2, 1, 3].length) (baseStart_6680144 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6680144 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6680144 prefixEnd_6680144 := by exact prefixLift 6680144
  have htrace : WordTrace (prefixWord ++ tailWord_6680144) baseStart_6680144 baseEnd_6680144 := by
    simpa [prefixWord, tailWord_6680144, baseEnd_6680144] using wordTrace_append hprefix tailTrace_6680144
  have hstable : (prefixWord ++ tailWord_6680144).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6680144).length < 2 ^ (prefixWord ++ tailWord_6680144).sum := by decide
  have hdescent : baseEnd_6680144 < baseStart_6680144 := by decide
  rcases family_descends (prefixWord ++ tailWord_6680144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6680160 : List Nat := [2, 1, 1, 3, 2, 1, 1, 3, 1, 8]
def baseStart_6680160 : Nat := 118140960795 + 6680160 * 2 ^ 59
def prefixEnd_6680160 : Nat := 4983230072969 + 3 ^ 40 * 6680160 * 2
def baseEnd_6680160 : Nat := 1143377642979563025659503

theorem tailTrace_6680160 : CollatzResearch.WordTrace tailWord_6680160 prefixEnd_6680160 1143377642979563025659503 := by
  unfold tailWord_6680160
  simp only [CollatzResearch.WordTrace]
  refine ⟨121822725739464337671486967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 162430300985952450228649289 121822725739464337671486967)
  ·
    refine ⟨182734088609196506507230451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121822725739464337671486967 182734088609196506507230451)
    ·
      refine ⟨274101132913794759760845677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 182734088609196506507230451 274101132913794759760845677)
      ·
        refine ⟨102787924842673034910317129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 274101132913794759760845677 102787924842673034910317129)
        ·
          refine ⟨77090943632004776182737847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 102787924842673034910317129 77090943632004776182737847)
          ·
            refine ⟨115636415448007164274106771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77090943632004776182737847 115636415448007164274106771)
            ·
              refine ⟨173454623172010746411160157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 115636415448007164274106771 173454623172010746411160157)
              ·
                refine ⟨65045483689504029904185059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 173454623172010746411160157 65045483689504029904185059)
                ·
                  refine ⟨97568225534256044856277589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 65045483689504029904185059 97568225534256044856277589)
                  ·
                    refine ⟨1143377642979563025659503, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 97568225534256044856277589 1143377642979563025659503)
                    ·
                      rfl

theorem cell23_6680160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 1, 3, 1, 8].length) (baseStart_6680160 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6680160 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6680160 prefixEnd_6680160 := by exact prefixLift 6680160
  have htrace : WordTrace (prefixWord ++ tailWord_6680160) baseStart_6680160 baseEnd_6680160 := by
    simpa [prefixWord, tailWord_6680160, baseEnd_6680160] using wordTrace_append hprefix tailTrace_6680160
  have hstable : (prefixWord ++ tailWord_6680160).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6680160).length < 2 ^ (prefixWord ++ tailWord_6680160).sum := by decide
  have hdescent : baseEnd_6680160 < baseStart_6680160 := by decide
  rcases family_descends (prefixWord ++ tailWord_6680160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6680197 : List Nat := [1, 3, 1, 1, 4, 1, 2, 2, 2, 2, 4]
def baseStart_6680197 : Nat := 118140960795 + 6680197 * 2 ^ 59
def prefixEnd_6680197 : Nat := 4983230072969 + 3 ^ 40 * 6680197 * 2
def baseEnd_6680197 : Nat := 3430151927722905432215839

theorem tailTrace_6680197 : CollatzResearch.WordTrace tailWord_6680197 prefixEnd_6680197 3430151927722905432215839 := by
  unfold tailWord_6680197
  simp only [CollatzResearch.WordTrace]
  refine ⟨243646800979794630662070845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162431200653196420441380563 243646800979794630662070845)
  ·
    refine ⟨91367550367422986498276567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 243646800979794630662070845 91367550367422986498276567)
    ·
      refine ⟨137051325551134479747414851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91367550367422986498276567 137051325551134479747414851)
      ·
        refine ⟨205576988326701719621122277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 137051325551134479747414851 205576988326701719621122277)
        ·
          refine ⟨38545685311256572428960427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 205576988326701719621122277 38545685311256572428960427)
          ·
            refine ⟨57818527966884858643440641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38545685311256572428960427 57818527966884858643440641)
            ·
              refine ⟨43363895975163643982580481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 57818527966884858643440641 43363895975163643982580481)
              ·
                refine ⟨32522921981372732986935361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43363895975163643982580481 32522921981372732986935361)
                ·
                  refine ⟨24392191486029549740201521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32522921981372732986935361 24392191486029549740201521)
                  ·
                    refine ⟨18294143614522162305151141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24392191486029549740201521 18294143614522162305151141)
                    ·
                      refine ⟨3430151927722905432215839, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18294143614522162305151141 3430151927722905432215839)
                      ·
                        rfl

theorem cell23_6680197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 2, 2, 2, 2, 4].length) (baseStart_6680197 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6680197 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6680197 prefixEnd_6680197 := by exact prefixLift 6680197
  have htrace : WordTrace (prefixWord ++ tailWord_6680197) baseStart_6680197 baseEnd_6680197 := by
    simpa [prefixWord, tailWord_6680197, baseEnd_6680197] using wordTrace_append hprefix tailTrace_6680197
  have hstable : (prefixWord ++ tailWord_6680197).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6680197).length < 2 ^ (prefixWord ++ tailWord_6680197).sum := by decide
  have hdescent : baseEnd_6680197 < baseStart_6680197 := by decide
  rcases family_descends (prefixWord ++ tailWord_6680197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6680201 : List Nat := [1, 2, 1, 1, 4, 1, 3, 4, 2, 2, 2]
def baseStart_6680201 : Nat := 118140960795 + 6680201 * 2 ^ 59
def prefixEnd_6680201 : Nat := 4983230072969 + 3 ^ 40 * 6680201 * 2
def baseEnd_6680201 : Nat := 3430153981645523416565821

theorem tailTrace_6680201 : CollatzResearch.WordTrace tailWord_6680201 prefixEnd_6680201 3430153981645523416565821 := by
  unfold tailWord_6680201
  simp only [CollatzResearch.WordTrace]
  refine ⟨243646946871780139345216457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162431297914520092896810971 243646946871780139345216457)
  ·
    refine ⟨182735210153835104508912343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 243646946871780139345216457 182735210153835104508912343)
    ·
      refine ⟨274102815230752656763368515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 182735210153835104508912343 274102815230752656763368515)
      ·
        refine ⟨411154222846128985145052773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 274102815230752656763368515 411154222846128985145052773)
        ·
          refine ⟨77091416783649184714697395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 411154222846128985145052773 77091416783649184714697395)
          ·
            refine ⟨115637125175473777072046093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77091416783649184714697395 115637125175473777072046093)
            ·
              refine ⟨43363921940802666402017285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 115637125175473777072046093 43363921940802666402017285)
              ·
                refine ⟨8130735363900499950378241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 43363921940802666402017285 8130735363900499950378241)
                ·
                  refine ⟨6098051522925374962783681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8130735363900499950378241 6098051522925374962783681)
                  ·
                    refine ⟨4573538642194031222087761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6098051522925374962783681 4573538642194031222087761)
                    ·
                      refine ⟨3430153981645523416565821, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4573538642194031222087761 3430153981645523416565821)
                      ·
                        rfl

theorem cell23_6680201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 3, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 3, 4, 2, 2, 2].length) (baseStart_6680201 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6680201 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6680201 prefixEnd_6680201 := by exact prefixLift 6680201
  have htrace : WordTrace (prefixWord ++ tailWord_6680201) baseStart_6680201 baseEnd_6680201 := by
    simpa [prefixWord, tailWord_6680201, baseEnd_6680201] using wordTrace_append hprefix tailTrace_6680201
  have hstable : (prefixWord ++ tailWord_6680201).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6680201).length < 2 ^ (prefixWord ++ tailWord_6680201).sum := by decide
  have hdescent : baseEnd_6680201 < baseStart_6680201 := by decide
  rcases family_descends (prefixWord ++ tailWord_6680201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6680274 : List Nat := [3, 2, 2, 2, 2, 1, 1, 2, 1, 3, 4]
def baseStart_6680274 : Nat := 118140960795 + 6680274 * 2 ^ 59
def prefixEnd_6680274 : Nat := 4983230072969 + 3 ^ 40 * 6680274 * 2
def baseEnd_6680274 : Nat := 3430191465733301630952985

theorem tailTrace_6680274 : CollatzResearch.WordTrace tailWord_6680274 prefixEnd_6680274 3430191465733301630952985 := by
  unfold tailWord_6680274
  simp only [CollatzResearch.WordTrace]
  refine ⟨60912402350128918203155969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 162433072933677115208415917 60912402350128918203155969)
  ·
    refine ⟨45684301762596688652366977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60912402350128918203155969 45684301762596688652366977)
    ·
      refine ⟨34263226321947516489275233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45684301762596688652366977 34263226321947516489275233)
      ·
        refine ⟨25697419741460637366956425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34263226321947516489275233 25697419741460637366956425)
        ·
          refine ⟨19273064806095478025217319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25697419741460637366956425 19273064806095478025217319)
          ·
            refine ⟨28909597209143217037825979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19273064806095478025217319 28909597209143217037825979)
            ·
              refine ⟨43364395813714825556738969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28909597209143217037825979 43364395813714825556738969)
              ·
                refine ⟨32523296860286119167554227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43364395813714825556738969 32523296860286119167554227)
                ·
                  refine ⟨48784945290429178751331341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32523296860286119167554227 48784945290429178751331341)
                  ·
                    refine ⟨18294354483910942031749253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 48784945290429178751331341 18294354483910942031749253)
                    ·
                      refine ⟨3430191465733301630952985, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18294354483910942031749253 3430191465733301630952985)
                      ·
                        rfl

theorem cell23_6680274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 1, 2, 1, 3, 4].length) (baseStart_6680274 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6680274 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6680274 prefixEnd_6680274 := by exact prefixLift 6680274
  have htrace : WordTrace (prefixWord ++ tailWord_6680274) baseStart_6680274 baseEnd_6680274 := by
    simpa [prefixWord, tailWord_6680274, baseEnd_6680274] using wordTrace_append hprefix tailTrace_6680274
  have hstable : (prefixWord ++ tailWord_6680274).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6680274).length < 2 ^ (prefixWord ++ tailWord_6680274).sum := by decide
  have hdescent : baseEnd_6680274 < baseStart_6680274 := by decide
  rcases family_descends (prefixWord ++ tailWord_6680274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6680287 : List Nat := [1, 1, 2, 3, 2, 2, 1, 1, 2, 4, 4]
def baseStart_6680287 : Nat := 118140960795 + 6680287 * 2 ^ 59
def prefixEnd_6680287 : Nat := 4983230072969 + 3 ^ 40 * 6680287 * 2
def baseEnd_6680287 : Nat := 3430198140981810080090425

theorem tailTrace_6680287 : CollatzResearch.WordTrace tailWord_6680287 prefixEnd_6680287 3430198140981810080090425 := by
  unfold tailWord_6680287
  simp only [CollatzResearch.WordTrace]
  refine ⟨243650083549468576032847115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162433389032979050688564743 243650083549468576032847115)
  ·
    refine ⟨365475125324202864049270673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 243650083549468576032847115 365475125324202864049270673)
    ·
      refine ⟨274106343993152148036953005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 365475125324202864049270673 274106343993152148036953005)
      ·
        refine ⟨102789878997432055513857377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 274106343993152148036953005 102789878997432055513857377)
        ·
          refine ⟨77092409248074041635393033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 102789878997432055513857377 77092409248074041635393033)
          ·
            refine ⟨57819306936055531226544775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 77092409248074041635393033 57819306936055531226544775)
            ·
              refine ⟨86728960404083296839817163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57819306936055531226544775 86728960404083296839817163)
              ·
                refine ⟨130093440606124945259725745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 86728960404083296839817163 130093440606124945259725745)
                ·
                  refine ⟨97570080454593708944794309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 130093440606124945259725745 97570080454593708944794309)
                  ·
                    refine ⟨18294390085236320427148933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 97570080454593708944794309 18294390085236320427148933)
                    ·
                      refine ⟨3430198140981810080090425, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18294390085236320427148933 3430198140981810080090425)
                      ·
                        rfl

theorem cell23_6680287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 1, 1, 2, 4, 4].length) (baseStart_6680287 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6680287 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6680287 prefixEnd_6680287 := by exact prefixLift 6680287
  have htrace : WordTrace (prefixWord ++ tailWord_6680287) baseStart_6680287 baseEnd_6680287 := by
    simpa [prefixWord, tailWord_6680287, baseEnd_6680287] using wordTrace_append hprefix tailTrace_6680287
  have hstable : (prefixWord ++ tailWord_6680287).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6680287).length < 2 ^ (prefixWord ++ tailWord_6680287).sum := by decide
  have hdescent : baseEnd_6680287 < baseStart_6680287 := by decide
  rcases family_descends (prefixWord ++ tailWord_6680287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6680308 : List Nat := [2, 6, 1, 1, 1, 1, 1, 1, 4, 1, 4]
def baseStart_6680308 : Nat := 118140960795 + 6680308 * 2 ^ 59
def prefixEnd_6680308 : Nat := 4983230072969 + 3 ^ 40 * 6680308 * 2
def baseEnd_6680308 : Nat := 3430208924075554497927829

theorem tailTrace_6680308 : CollatzResearch.WordTrace tailWord_6680308 prefixEnd_6680308 3430208924075554497927829 := by
  unfold tailWord_6680308
  simp only [CollatzResearch.WordTrace]
  refine ⟨121825424741196248309680789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 162433899654928331079574385 121825424741196248309680789)
  ·
    refine ⟨5710566784743574139516287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 121825424741196248309680789 5710566784743574139516287)
    ·
      refine ⟨8565850177115361209274431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5710566784743574139516287 8565850177115361209274431)
      ·
        refine ⟨12848775265673041813911647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8565850177115361209274431 12848775265673041813911647)
        ·
          refine ⟨19273162898509562720867471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12848775265673041813911647 19273162898509562720867471)
          ·
            refine ⟨28909744347764344081301207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19273162898509562720867471 28909744347764344081301207)
            ·
              refine ⟨43364616521646516121951811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28909744347764344081301207 43364616521646516121951811)
              ·
                refine ⟨65046924782469774182927717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43364616521646516121951811 65046924782469774182927717)
                ·
                  refine ⟨12196298396713082659298947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 65046924782469774182927717 12196298396713082659298947)
                  ·
                    refine ⟨18294447595069623988948421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12196298396713082659298947 18294447595069623988948421)
                    ·
                      refine ⟨3430208924075554497927829, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18294447595069623988948421 3430208924075554497927829)
                      ·
                        rfl

theorem cell23_6680308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 1, 1, 4, 1, 4].length) (baseStart_6680308 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6680308 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6680308 prefixEnd_6680308 := by exact prefixLift 6680308
  have htrace : WordTrace (prefixWord ++ tailWord_6680308) baseStart_6680308 baseEnd_6680308 := by
    simpa [prefixWord, tailWord_6680308, baseEnd_6680308] using wordTrace_append hprefix tailTrace_6680308
  have hstable : (prefixWord ++ tailWord_6680308).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6680308).length < 2 ^ (prefixWord ++ tailWord_6680308).sum := by decide
  have hdescent : baseEnd_6680308 < baseStart_6680308 := by decide
  rcases family_descends (prefixWord ++ tailWord_6680308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6680317 : List Nat := [1, 4, 1, 1, 1, 1, 2, 3, 1, 2, 6]
def baseStart_6680317 : Nat := 118140960795 + 6680317 * 2 ^ 59
def prefixEnd_6680317 : Nat := 4983230072969 + 3 ^ 40 * 6680317 * 2
def baseEnd_6680317 : Nat := 3430213545401444962715287

theorem tailTrace_6680317 : CollatzResearch.WordTrace tailWord_6680317 prefixEnd_6680317 3430213545401444962715287 := by
  unfold tailWord_6680317
  simp only [CollatzResearch.WordTrace]
  refine ⟨243651177739359891156439205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162434118492906594104292803 243651177739359891156439205)
  ·
    refine ⟨45684595826129979591832351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 243651177739359891156439205 45684595826129979591832351)
    ·
      refine ⟨68526893739194969387748527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45684595826129979591832351 68526893739194969387748527)
      ·
        refine ⟨102790340608792454081622791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68526893739194969387748527 102790340608792454081622791)
        ·
          refine ⟨154185510913188681122434187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 102790340608792454081622791 154185510913188681122434187)
          ·
            refine ⟨231278266369783021683651281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 154185510913188681122434187 231278266369783021683651281)
            ·
              refine ⟨173458699777337266262738461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 231278266369783021683651281 173458699777337266262738461)
              ·
                refine ⟨65047012416501474848526923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 173458699777337266262738461 65047012416501474848526923)
                ·
                  refine ⟨97570518624752212272790385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 65047012416501474848526923 97570518624752212272790385)
                  ·
                    refine ⟨73177888968564159204592789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 97570518624752212272790385 73177888968564159204592789)
                    ·
                      refine ⟨3430213545401444962715287, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 73177888968564159204592789 3430213545401444962715287)
                      ·
                        rfl

theorem cell23_6680317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 2, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 2, 3, 1, 2, 6].length) (baseStart_6680317 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6680317 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6680317 prefixEnd_6680317 := by exact prefixLift 6680317
  have htrace : WordTrace (prefixWord ++ tailWord_6680317) baseStart_6680317 baseEnd_6680317 := by
    simpa [prefixWord, tailWord_6680317, baseEnd_6680317] using wordTrace_append hprefix tailTrace_6680317
  have hstable : (prefixWord ++ tailWord_6680317).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6680317).length < 2 ^ (prefixWord ++ tailWord_6680317).sum := by decide
  have hdescent : baseEnd_6680317 < baseStart_6680317 := by decide
  rcases family_descends (prefixWord ++ tailWord_6680317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6680347 : List Nat := [1, 1, 1, 1, 1, 1, 4, 2, 2, 5, 4]
def baseStart_6680347 : Nat := 118140960795 + 6680347 * 2 ^ 59
def prefixEnd_6680347 : Nat := 4983230072969 + 3 ^ 40 * 6680347 * 2
def baseEnd_6680347 : Nat := 3430228949821079845340149

theorem tailTrace_6680347 : CollatzResearch.WordTrace tailWord_6680347 prefixEnd_6680347 3430228949821079845340149 := by
  unfold tailWord_6680347
  simp only [CollatzResearch.WordTrace]
  refine ⟨243652271929251206280031295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162434847952834137520020863 243652271929251206280031295)
  ·
    refine ⟨365478407893876809420046943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 243652271929251206280031295 365478407893876809420046943)
    ·
      refine ⟨548217611840815214130070415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 365478407893876809420046943 548217611840815214130070415)
      ·
        refine ⟨822326417761222821195105623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 548217611840815214130070415 822326417761222821195105623)
        ·
          refine ⟨1233489626641834231792658435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 822326417761222821195105623 1233489626641834231792658435)
          ·
            refine ⟨1850234439962751347688987653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1233489626641834231792658435 1850234439962751347688987653)
            ·
              refine ⟨346918957493015877691685185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1850234439962751347688987653 346918957493015877691685185)
              ·
                refine ⟨260189218119761908268763889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 346918957493015877691685185 260189218119761908268763889)
                ·
                  refine ⟨195141913589821431201572917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 260189218119761908268763889 195141913589821431201572917)
                  ·
                    refine ⟨18294554399045759175147461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 195141913589821431201572917 18294554399045759175147461)
                    ·
                      refine ⟨3430228949821079845340149, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18294554399045759175147461 3430228949821079845340149)
                      ·
                        rfl

theorem cell23_6680347_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 2, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 2, 2, 5, 4].length) (baseStart_6680347 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6680347 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6680347 prefixEnd_6680347 := by exact prefixLift 6680347
  have htrace : WordTrace (prefixWord ++ tailWord_6680347) baseStart_6680347 baseEnd_6680347 := by
    simpa [prefixWord, tailWord_6680347, baseEnd_6680347] using wordTrace_append hprefix tailTrace_6680347
  have hstable : (prefixWord ++ tailWord_6680347).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6680347).length < 2 ^ (prefixWord ++ tailWord_6680347).sum := by decide
  have hdescent : baseEnd_6680347 < baseStart_6680347 := by decide
  rcases family_descends (prefixWord ++ tailWord_6680347) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6680381 : List Nat := [1, 4, 1, 4, 1, 1, 1, 2, 3, 1, 4]
def baseStart_6680381 : Nat := 118140960795 + 6680381 * 2 ^ 59
def prefixEnd_6680381 : Nat := 4983230072969 + 3 ^ 40 * 6680381 * 2
def baseEnd_6680381 : Nat := 3430246408163332712314993

theorem tailTrace_6680381 : CollatzResearch.WordTrace tailWord_6680381 prefixEnd_6680381 3430246408163332712314993 := by
  unfold tailWord_6680381
  simp only [CollatzResearch.WordTrace]
  refine ⟨243653512011128030086768997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162435674674085353391179331 243653512011128030086768997)
  ·
    refine ⟨45685033502086505641269187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 243653512011128030086768997 45685033502086505641269187)
    ·
      refine ⟨68527550253129758461903781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45685033502086505641269187 68527550253129758461903781)
      ·
        refine ⟨12848915672461829711606959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 68527550253129758461903781 12848915672461829711606959)
        ·
          refine ⟨19273373508692744567410439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12848915672461829711606959 19273373508692744567410439)
          ·
            refine ⟨28910060263039116851115659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19273373508692744567410439 28910060263039116851115659)
            ·
              refine ⟨43365090394558675276673489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28910060263039116851115659 43365090394558675276673489)
              ·
                refine ⟨32523817795919006457505117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43365090394558675276673489 32523817795919006457505117)
                ·
                  refine ⟨12196431673469627421564419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32523817795919006457505117 12196431673469627421564419)
                  ·
                    refine ⟨18294647510204441132346629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12196431673469627421564419 18294647510204441132346629)
                    ·
                      refine ⟨3430246408163332712314993, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18294647510204441132346629 3430246408163332712314993)
                      ·
                        rfl

theorem cell23_6680381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 1, 2, 3, 1, 4].length) (baseStart_6680381 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6680381 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6680381 prefixEnd_6680381 := by exact prefixLift 6680381
  have htrace : WordTrace (prefixWord ++ tailWord_6680381) baseStart_6680381 baseEnd_6680381 := by
    simpa [prefixWord, tailWord_6680381, baseEnd_6680381] using wordTrace_append hprefix tailTrace_6680381
  have hstable : (prefixWord ++ tailWord_6680381).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6680381).length < 2 ^ (prefixWord ++ tailWord_6680381).sum := by decide
  have hdescent : baseEnd_6680381 < baseStart_6680381 := by decide
  rcases family_descends (prefixWord ++ tailWord_6680381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6680391 : List Nat := [1, 1, 4, 1, 2, 1, 4, 3, 2, 4]
def baseStart_6680391 : Nat := 118140960795 + 6680391 * 2 ^ 59
def prefixEnd_6680391 : Nat := 4983230072969 + 3 ^ 40 * 6680391 * 2
def baseEnd_6680391 : Nat := 1143417180989959224396649

theorem tailTrace_6680391 : CollatzResearch.WordTrace tailWord_6680391 prefixEnd_6680391 1143417180989959224396649 := by
  unfold tailWord_6680391
  simp only [CollatzResearch.WordTrace]
  refine ⟨243653876741091801794633027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162435917827394534529755351 243653876741091801794633027)
  ·
    refine ⟨365480815111637702691949541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 243653876741091801794633027 365480815111637702691949541)
    ·
      refine ⟨68527652833432069254740539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 365480815111637702691949541 68527652833432069254740539)
      ·
        refine ⟨102791479250148103882110809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68527652833432069254740539 102791479250148103882110809)
        ·
          refine ⟨77093609437611077911583107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 102791479250148103882110809 77093609437611077911583107)
          ·
            refine ⟨115640414156416616867374661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77093609437611077911583107 115640414156416616867374661)
            ·
              refine ⟨21682577654328115662632749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 115640414156416616867374661 21682577654328115662632749)
              ·
                refine ⟨8130966620373043373487281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21682577654328115662632749 8130966620373043373487281)
                ·
                  refine ⟨6098224965279782530115461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8130966620373043373487281 6098224965279782530115461)
                  ·
                    refine ⟨1143417180989959224396649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6098224965279782530115461 1143417180989959224396649)
                    ·
                      rfl

theorem cell23_6680391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 4, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 4, 3, 2, 4].length) (baseStart_6680391 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6680391 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6680391 prefixEnd_6680391 := by exact prefixLift 6680391
  have htrace : WordTrace (prefixWord ++ tailWord_6680391) baseStart_6680391 baseEnd_6680391 := by
    simpa [prefixWord, tailWord_6680391, baseEnd_6680391] using wordTrace_append hprefix tailTrace_6680391
  have hstable : (prefixWord ++ tailWord_6680391).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6680391).length < 2 ^ (prefixWord ++ tailWord_6680391).sum := by decide
  have hdescent : baseEnd_6680391 < baseStart_6680391 := by decide
  rcases family_descends (prefixWord ++ tailWord_6680391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6680401 : List Nat := [1, 2, 2, 1, 5, 1, 2, 1, 3, 2, 3]
def baseStart_6680401 : Nat := 118140960795 + 6680401 * 2 ^ 59
def prefixEnd_6680401 : Nat := 4983230072969 + 3 ^ 40 * 6680401 * 2
def baseEnd_6680401 : Nat := 3430256677776422634064901

theorem tailTrace_6680401 : CollatzResearch.WordTrace tailWord_6680401 prefixEnd_6680401 3430256677776422634064901 := by
  unfold tailWord_6680401
  simp only [CollatzResearch.WordTrace]
  refine ⟨243654241471055573502497057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162436160980703715668331371 243654241471055573502497057)
  ·
    refine ⟨182740681103291680126872793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 243654241471055573502497057 182740681103291680126872793)
    ·
      refine ⟨137055510827468760095154595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 182740681103291680126872793 137055510827468760095154595)
      ·
        refine ⟨205583266241203140142731893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 137055510827468760095154595 205583266241203140142731893)
        ·
          refine ⟨19273431210112794388381115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 205583266241203140142731893 19273431210112794388381115)
          ·
            refine ⟨28910146815169191582571673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19273431210112794388381115 28910146815169191582571673)
            ·
              refine ⟨21682610111376893686928755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28910146815169191582571673 21682610111376893686928755)
              ·
                refine ⟨32523915167065340530393133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21682610111376893686928755 32523915167065340530393133)
                ·
                  refine ⟨12196468187649502698897425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32523915167065340530393133 12196468187649502698897425)
                  ·
                    refine ⟨9147351140737127024173069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12196468187649502698897425 9147351140737127024173069)
                    ·
                      refine ⟨3430256677776422634064901, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9147351140737127024173069 3430256677776422634064901)
                      ·
                        rfl

theorem cell23_6680401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 2, 1, 3, 2, 3].length) (baseStart_6680401 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6680401 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6680401 prefixEnd_6680401 := by exact prefixLift 6680401
  have htrace : WordTrace (prefixWord ++ tailWord_6680401) baseStart_6680401 baseEnd_6680401 := by
    simpa [prefixWord, tailWord_6680401, baseEnd_6680401] using wordTrace_append hprefix tailTrace_6680401
  have hstable : (prefixWord ++ tailWord_6680401).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6680401).length < 2 ^ (prefixWord ++ tailWord_6680401).sum := by decide
  have hdescent : baseEnd_6680401 < baseStart_6680401 := by decide
  rcases family_descends (prefixWord ++ tailWord_6680401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6680412 : List Nat := [2, 2, 4, 2, 3, 1, 2, 1, 1, 5]
def baseStart_6680412 : Nat := 118140960795 + 6680412 * 2 ^ 59
def prefixEnd_6680412 : Nat := 4983230072969 + 3 ^ 40 * 6680412 * 2
def baseEnd_6680412 : Nat := 1143420775354540697009117

theorem tailTrace_6680412 : CollatzResearch.WordTrace tailWord_6680412 prefixEnd_6680412 1143420775354540697009117 := by
  unfold tailWord_6680412
  simp only [CollatzResearch.WordTrace]
  refine ⟨121827321337007861190573745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 162436428449343814920764993 121827321337007861190573745)
  ·
    refine ⟨91370491002755895892930309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 121827321337007861190573745 91370491002755895892930309)
    ·
      refine ⟨17131967063016730479924433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 91370491002755895892930309 17131967063016730479924433)
      ·
        refine ⟨12848975297262547859943325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17131967063016730479924433 12848975297262547859943325)
        ·
          refine ⟨4818365736473455447478747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12848975297262547859943325 4818365736473455447478747)
          ·
            refine ⟨7227548604710183171218121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4818365736473455447478747 7227548604710183171218121)
            ·
              refine ⟨5420661453532637378413591, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7227548604710183171218121 5420661453532637378413591)
              ·
                refine ⟨8130992180298956067620387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5420661453532637378413591 8130992180298956067620387)
                ·
                  refine ⟨12196488270448434101430581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8130992180298956067620387 12196488270448434101430581)
                  ·
                    refine ⟨1143420775354540697009117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12196488270448434101430581 1143420775354540697009117)
                    ·
                      rfl

theorem cell23_6680412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 3, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 3, 1, 2, 1, 1, 5].length) (baseStart_6680412 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6680412 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6680412 prefixEnd_6680412 := by exact prefixLift 6680412
  have htrace : WordTrace (prefixWord ++ tailWord_6680412) baseStart_6680412 baseEnd_6680412 := by
    simpa [prefixWord, tailWord_6680412, baseEnd_6680412] using wordTrace_append hprefix tailTrace_6680412
  have hstable : (prefixWord ++ tailWord_6680412).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6680412).length < 2 ^ (prefixWord ++ tailWord_6680412).sum := by decide
  have hdescent : baseEnd_6680412 < baseStart_6680412 := by decide
  rcases family_descends (prefixWord ++ tailWord_6680412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6680415 : List Nat := [1, 1, 2, 3, 1, 4, 1, 5, 1, 2, 2]
def baseStart_6680415 : Nat := 118140960795 + 6680415 * 2 ^ 59
def prefixEnd_6680415 : Nat := 4983230072969 + 3 ^ 40 * 6680415 * 2
def baseEnd_6680415 : Nat := 3430263866505585579289837

theorem tailTrace_6680415 : CollatzResearch.WordTrace tailWord_6680415 prefixEnd_6680415 3430263866505585579289837 := by
  unfold tailWord_6680415
  simp only [CollatzResearch.WordTrace]
  refine ⟨243654752093004853893506699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162436501395336569262337799 243654752093004853893506699)
  ·
    refine ⟨365482128139507280840260049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 243654752093004853893506699 365482128139507280840260049)
    ·
      refine ⟨274111596104630460630195037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 365482128139507280840260049 274111596104630460630195037)
      ·
        refine ⟨102791848539236422736323139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 274111596104630460630195037 102791848539236422736323139)
        ·
          refine ⟨154187772808854634104484709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 102791848539236422736323139 154187772808854634104484709)
          ·
            refine ⟨28910207401660243894590883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 154187772808854634104484709 28910207401660243894590883)
            ·
              refine ⟨43365311102490365841886325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28910207401660243894590883 43365311102490365841886325)
              ·
                refine ⟨4065497915858471797676843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 43365311102490365841886325 4065497915858471797676843)
                ·
                  refine ⟨6098246873787707696515265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4065497915858471797676843 6098246873787707696515265)
                  ·
                    refine ⟨4573685155340780772386449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6098246873787707696515265 4573685155340780772386449)
                    ·
                      refine ⟨3430263866505585579289837, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4573685155340780772386449 3430263866505585579289837)
                      ·
                        rfl

theorem cell23_6680415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 1, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 1, 5, 1, 2, 2].length) (baseStart_6680415 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6680415 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6680415 prefixEnd_6680415 := by exact prefixLift 6680415
  have htrace : WordTrace (prefixWord ++ tailWord_6680415) baseStart_6680415 baseEnd_6680415 := by
    simpa [prefixWord, tailWord_6680415, baseEnd_6680415] using wordTrace_append hprefix tailTrace_6680415
  have hstable : (prefixWord ++ tailWord_6680415).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6680415).length < 2 ^ (prefixWord ++ tailWord_6680415).sum := by decide
  have hdescent : baseEnd_6680415 < baseStart_6680415 := by decide
  rcases family_descends (prefixWord ++ tailWord_6680415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6680505 : List Nat := [1, 2, 1, 4, 2, 1, 3, 3, 2, 2, 2]
def baseStart_6680505 : Nat := 118140960795 + 6680505 * 2 ^ 59
def prefixEnd_6680505 : Nat := 4983230072969 + 3 ^ 40 * 6680505 * 2
def baseEnd_6680505 : Nat := 3430310079764490227164423

theorem tailTrace_6680505 : CollatzResearch.WordTrace tailWord_6680505 prefixEnd_6680505 3430310079764490227164423 := by
  unfold tailWord_6680505
  simp only [CollatzResearch.WordTrace]
  refine ⟨243658034662678799264282969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162438689775119199509521979 243658034662678799264282969)
  ·
    refine ⟨182743525997009099448212227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 243658034662678799264282969 182743525997009099448212227)
    ·
      refine ⟨274115288995513649172318341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 182743525997009099448212227 274115288995513649172318341)
      ·
        refine ⟨51396616686658809219809689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 274115288995513649172318341 51396616686658809219809689)
        ·
          refine ⟨38547462514994106914857267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51396616686658809219809689 38547462514994106914857267)
          ·
            refine ⟨57821193772491160372285901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38547462514994106914857267 57821193772491160372285901)
            ·
              refine ⟨21682947664684185139607213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 57821193772491160372285901 21682947664684185139607213)
              ·
                refine ⟨8131105374256569427352705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21682947664684185139607213 8131105374256569427352705)
                ·
                  refine ⟨6098329030692427070514529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8131105374256569427352705 6098329030692427070514529)
                  ·
                    refine ⟨4573746773019320302885897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6098329030692427070514529 4573746773019320302885897)
                    ·
                      refine ⟨3430310079764490227164423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4573746773019320302885897 3430310079764490227164423)
                      ·
                        rfl

theorem cell23_6680505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 3, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 3, 3, 2, 2, 2].length) (baseStart_6680505 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6680505 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6680505 prefixEnd_6680505 := by exact prefixLift 6680505
  have htrace : WordTrace (prefixWord ++ tailWord_6680505) baseStart_6680505 baseEnd_6680505 := by
    simpa [prefixWord, tailWord_6680505, baseEnd_6680505] using wordTrace_append hprefix tailTrace_6680505
  have hstable : (prefixWord ++ tailWord_6680505).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6680505).length < 2 ^ (prefixWord ++ tailWord_6680505).sum := by decide
  have hdescent : baseEnd_6680505 < baseStart_6680505 := by decide
  rcases family_descends (prefixWord ++ tailWord_6680505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6680571 : List Nat := [1, 1, 1, 1, 1, 3, 5, 1, 5, 4]
def baseStart_6680571 : Nat := 118140960795 + 6680571 * 2 ^ 59
def prefixEnd_6680571 : Nat := 4983230072969 + 3 ^ 40 * 6680571 * 2
def baseEnd_6680571 : Nat := 1143447989829228989646373

theorem tailTrace_6680571 : CollatzResearch.WordTrace tailWord_6680571 prefixEnd_6680571 1143447989829228989646373 := by
  unfold tailWord_6680571
  simp only [CollatzResearch.WordTrace]
  refine ⟨243660441880439692536185567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162440294586959795024123711 243660441880439692536185567)
  ·
    refine ⟨365490662820659538804278351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 243660441880439692536185567 365490662820659538804278351)
    ·
      refine ⟨548235994230989308206417527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 365490662820659538804278351 548235994230989308206417527)
      ·
        refine ⟨822353991346483962309626291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 548235994230989308206417527 822353991346483962309626291)
        ·
          refine ⟨1233530987019725943464439437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 822353991346483962309626291 1233530987019725943464439437)
          ·
            refine ⟨462574120132397228799164789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1233530987019725943464439437 462574120132397228799164789)
            ·
              refine ⟨43366323762412240199921699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 462574120132397228799164789 43366323762412240199921699)
              ·
                refine ⟨65049485643618360299882549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43366323762412240199921699 65049485643618360299882549)
                ·
                  refine ⟨6098389279089221278113989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 65049485643618360299882549 6098389279089221278113989)
                  ·
                    refine ⟨1143447989829228989646373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6098389279089221278113989 1143447989829228989646373)
                    ·
                      rfl

theorem cell23_6680571_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 5, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 5, 1, 5, 4].length) (baseStart_6680571 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6680571 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6680571 prefixEnd_6680571 := by exact prefixLift 6680571
  have htrace : WordTrace (prefixWord ++ tailWord_6680571) baseStart_6680571 baseEnd_6680571 := by
    simpa [prefixWord, tailWord_6680571, baseEnd_6680571] using wordTrace_append hprefix tailTrace_6680571
  have hstable : (prefixWord ++ tailWord_6680571).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6680571).length < 2 ^ (prefixWord ++ tailWord_6680571).sum := by decide
  have hdescent : baseEnd_6680571 < baseStart_6680571 := by decide
  rcases family_descends (prefixWord ++ tailWord_6680571) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6680605 : List Nat := [1, 4, 2, 2, 2, 2, 2, 1, 3, 4]
def baseStart_6680605 : Nat := 118140960795 + 6680605 * 2 ^ 59
def prefixEnd_6680605 : Nat := 4983230072969 + 3 ^ 40 * 6680605 * 2
def baseEnd_6680605 : Nat := 1143453809276646611971321

theorem tailTrace_6680605 : CollatzResearch.WordTrace tailWord_6680605 prefixEnd_6680605 1143453809276646611971321 := by
  unfold tailWord_6680605
  simp only [CollatzResearch.WordTrace]
  refine ⟨243661681962316516342923269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162441121308211010895282179 243661681962316516342923269)
  ·
    refine ⟨45686565367934346814298113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 243661681962316516342923269 45686565367934346814298113)
    ·
      refine ⟨34264924025950760110723585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45686565367934346814298113 34264924025950760110723585)
      ·
        refine ⟨25698693019463070083042689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34264924025950760110723585 25698693019463070083042689)
        ·
          refine ⟨19274019764597302562282017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25698693019463070083042689 19274019764597302562282017)
          ·
            refine ⟨14455514823447976921711513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19274019764597302562282017 14455514823447976921711513)
            ·
              refine ⟨10841636117585982691283635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14455514823447976921711513 10841636117585982691283635)
              ·
                refine ⟨16262454176378974036925453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10841636117585982691283635 16262454176378974036925453)
                ·
                  refine ⟨6098420316142115263847045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16262454176378974036925453 6098420316142115263847045)
                  ·
                    refine ⟨1143453809276646611971321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6098420316142115263847045 1143453809276646611971321)
                    ·
                      rfl

theorem cell23_6680605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 2, 2, 1, 3, 4].length) (baseStart_6680605 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6680605 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6680605 prefixEnd_6680605 := by exact prefixLift 6680605
  have htrace : WordTrace (prefixWord ++ tailWord_6680605) baseStart_6680605 baseEnd_6680605 := by
    simpa [prefixWord, tailWord_6680605, baseEnd_6680605] using wordTrace_append hprefix tailTrace_6680605
  have hstable : (prefixWord ++ tailWord_6680605).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6680605).length < 2 ^ (prefixWord ++ tailWord_6680605).sum := by decide
  have hdescent : baseEnd_6680605 < baseStart_6680605 := by decide
  rcases family_descends (prefixWord ++ tailWord_6680605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6680631 : List Nat := [1, 1, 3, 1, 2, 2, 2, 3, 3, 5]
def baseStart_6680631 : Nat := 118140960795 + 6680631 * 2 ^ 59
def prefixEnd_6680631 : Nat := 4983230072969 + 3 ^ 40 * 6680631 * 2
def baseEnd_6680631 : Nat := 1143458259442318911396281

theorem tailTrace_6680631 : CollatzResearch.WordTrace tailWord_6680631 prefixEnd_6680631 1143458259442318911396281 := by
  unfold tailWord_6680631
  simp only [CollatzResearch.WordTrace]
  refine ⟨243662630260222322783369747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162441753506814881855579831 243662630260222322783369747)
  ·
    refine ⟨365493945390333484175054621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 243662630260222322783369747 365493945390333484175054621)
    ·
      refine ⟨137060229521375056565645483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 365493945390333484175054621 137060229521375056565645483)
      ·
        refine ⟨205590344282062584848468225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 137060229521375056565645483 205590344282062584848468225)
        ·
          refine ⟨154192758211546938636351169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 205590344282062584848468225 154192758211546938636351169)
          ·
            refine ⟨115644568658660203977263377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 154192758211546938636351169 115644568658660203977263377)
            ·
              refine ⟨86733426493995152982947533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 115644568658660203977263377 86733426493995152982947533)
              ·
                refine ⟨32525034935248182368605325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 86733426493995152982947533 32525034935248182368605325)
                ·
                  refine ⟨12196888100718068388226997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32525034935248182368605325 12196888100718068388226997)
                  ·
                    refine ⟨1143458259442318911396281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12196888100718068388226997 1143458259442318911396281)
                    ·
                      rfl

theorem cell23_6680631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 2, 3, 3, 5].length) (baseStart_6680631 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6680631 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6680631 prefixEnd_6680631 := by exact prefixLift 6680631
  have htrace : WordTrace (prefixWord ++ tailWord_6680631) baseStart_6680631 baseEnd_6680631 := by
    simpa [prefixWord, tailWord_6680631, baseEnd_6680631] using wordTrace_append hprefix tailTrace_6680631
  have hstable : (prefixWord ++ tailWord_6680631).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6680631).length < 2 ^ (prefixWord ++ tailWord_6680631).sum := by decide
  have hdescent : baseEnd_6680631 < baseStart_6680631 := by decide
  rcases family_descends (prefixWord ++ tailWord_6680631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6680671 : List Nat := [1, 1, 2, 3, 1, 1, 2, 3, 3, 1, 5]
def baseStart_6680671 : Nat := 118140960795 + 6680671 * 2 ^ 59
def prefixEnd_6680671 : Nat := 4983230072969 + 3 ^ 40 * 6680671 * 2
def baseEnd_6680671 : Nat := 3430395317553136577688659

theorem tailTrace_6680671 : CollatzResearch.WordTrace tailWord_6680671 prefixEnd_6680671 3430395317553136577688659 := by
  unfold tailWord_6680671
  simp only [CollatzResearch.WordTrace]
  refine ⟨243664089180077409614825867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162442726120051606409883911 243664089180077409614825867)
  ·
    refine ⟨365496133770116114422238801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 243664089180077409614825867 365496133770116114422238801)
    ·
      refine ⟨274122100327587085816679101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 365496133770116114422238801 274122100327587085816679101)
      ·
        refine ⟨102795787622845157181254663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 274122100327587085816679101 102795787622845157181254663)
        ·
          refine ⟨154193681434267735771881995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 102795787622845157181254663 154193681434267735771881995)
          ·
            refine ⟨231290522151401603657822993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 154193681434267735771881995 231290522151401603657822993)
            ·
              refine ⟨173467891613551202743367245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 231290522151401603657822993 173467891613551202743367245)
              ·
                refine ⟨65050459355081701028762717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 173467891613551202743367245 65050459355081701028762717)
                ·
                  refine ⟨24393922258155637885786019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 65050459355081701028762717 24393922258155637885786019)
                  ·
                    refine ⟨36590883387233456828679029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24393922258155637885786019 36590883387233456828679029)
                    ·
                      refine ⟨3430395317553136577688659, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36590883387233456828679029 3430395317553136577688659)
                      ·
                        rfl

theorem cell23_6680671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 2, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 2, 3, 3, 1, 5].length) (baseStart_6680671 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6680671 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6680671 prefixEnd_6680671 := by exact prefixLift 6680671
  have htrace : WordTrace (prefixWord ++ tailWord_6680671) baseStart_6680671 baseEnd_6680671 := by
    simpa [prefixWord, tailWord_6680671, baseEnd_6680671] using wordTrace_append hprefix tailTrace_6680671
  have hstable : (prefixWord ++ tailWord_6680671).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6680671).length < 2 ^ (prefixWord ++ tailWord_6680671).sum := by decide
  have hdescent : baseEnd_6680671 < baseStart_6680671 := by decide
  rcases family_descends (prefixWord ++ tailWord_6680671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6680681 : List Nat := [1, 2, 1, 1, 1, 5, 1, 3, 1, 1, 6]
def baseStart_6680681 : Nat := 118140960795 + 6680681 * 2 ^ 59
def prefixEnd_6680681 : Nat := 4983230072969 + 3 ^ 40 * 6680681 * 2
def baseEnd_6680681 : Nat := 3430400452359681538563613

theorem tailTrace_6680681 : CollatzResearch.WordTrace tailWord_6680681 prefixEnd_6680681 3430400452359681538563613 := by
  unfold tailWord_6680681
  simp only [CollatzResearch.WordTrace]
  refine ⟨243664453910041181322689897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162442969273360787548459931 243664453910041181322689897)
  ·
    refine ⟨182748340432530885992017423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 243664453910041181322689897 182748340432530885992017423)
    ·
      refine ⟨274122510648796328988026135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 182748340432530885992017423 274122510648796328988026135)
      ·
        refine ⟨411183765973194493482039203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 274122510648796328988026135 411183765973194493482039203)
        ·
          refine ⟨616775648959791740223058805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 411183765973194493482039203 616775648959791740223058805)
          ·
            refine ⟨57822717089980475645911763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 616775648959791740223058805 57822717089980475645911763)
            ·
              refine ⟨86734075634970713468867645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57822717089980475645911763 86734075634970713468867645)
              ·
                refine ⟨32525278363114017550825367, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 86734075634970713468867645 32525278363114017550825367)
                ·
                  refine ⟨48787917544671026326238051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32525278363114017550825367 48787917544671026326238051)
                  ·
                    refine ⟨73181876317006539489357077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 48787917544671026326238051 73181876317006539489357077)
                    ·
                      refine ⟨3430400452359681538563613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 73181876317006539489357077 3430400452359681538563613)
                      ·
                        rfl

theorem cell23_6680681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 1, 3, 1, 1, 6].length) (baseStart_6680681 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6680681 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6680681 prefixEnd_6680681 := by exact prefixLift 6680681
  have htrace : WordTrace (prefixWord ++ tailWord_6680681) baseStart_6680681 baseEnd_6680681 := by
    simpa [prefixWord, tailWord_6680681, baseEnd_6680681] using wordTrace_append hprefix tailTrace_6680681
  have hstable : (prefixWord ++ tailWord_6680681).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6680681).length < 2 ^ (prefixWord ++ tailWord_6680681).sum := by decide
  have hdescent : baseEnd_6680681 < baseStart_6680681 := by decide
  rcases family_descends (prefixWord ++ tailWord_6680681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6680682 : List Nat := [3, 1, 3, 2, 3, 2, 1, 2, 1, 5]
def baseStart_6680682 : Nat := 118140960795 + 6680682 * 2 ^ 59
def prefixEnd_6680682 : Nat := 4983230072969 + 3 ^ 40 * 6680682 * 2
def baseEnd_6680682 : Nat := 1143466988613445344883703

theorem tailTrace_6680682 : CollatzResearch.WordTrace tailWord_6680682 prefixEnd_6680682 1143466988613445344883703 := by
  unfold tailWord_6680682
  simp only [CollatzResearch.WordTrace]
  refine ⟨60916122595759389623369075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 162442993588691705662317533 60916122595759389623369075)
  ·
    refine ⟨91374183893639084435053613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60916122595759389623369075 91374183893639084435053613)
    ·
      refine ⟨34265318960114656663145105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 91374183893639084435053613 34265318960114656663145105)
      ·
        refine ⟨25698989220085992497358829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34265318960114656663145105 25698989220085992497358829)
        ·
          refine ⟨9637120957532247186509561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25698989220085992497358829 9637120957532247186509561)
          ·
            refine ⟨7227840718149185389882171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9637120957532247186509561 7227840718149185389882171)
            ·
              refine ⟨10841761077223778084823257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7227840718149185389882171 10841761077223778084823257)
              ·
                refine ⟨8131320807917833563617443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10841761077223778084823257 8131320807917833563617443)
                ·
                  refine ⟨12196981211876750345426165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8131320807917833563617443 12196981211876750345426165)
                  ·
                    refine ⟨1143466988613445344883703, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12196981211876750345426165 1143466988613445344883703)
                    ·
                      rfl

theorem cell23_6680682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 3, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 3, 2, 1, 2, 1, 5].length) (baseStart_6680682 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6680682 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6680682 prefixEnd_6680682 := by exact prefixLift 6680682
  have htrace : WordTrace (prefixWord ++ tailWord_6680682) baseStart_6680682 baseEnd_6680682 := by
    simpa [prefixWord, tailWord_6680682, baseEnd_6680682] using wordTrace_append hprefix tailTrace_6680682
  have hstable : (prefixWord ++ tailWord_6680682).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6680682).length < 2 ^ (prefixWord ++ tailWord_6680682).sum := by decide
  have hdescent : baseEnd_6680682 < baseStart_6680682 := by decide
  rcases family_descends (prefixWord ++ tailWord_6680682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6680712 : List Nat := [2, 1, 3, 4, 1, 2, 2, 2, 2, 4]
def baseStart_6680712 : Nat := 118140960795 + 6680712 * 2 ^ 59
def prefixEnd_6680712 : Nat := 4983230072969 + 3 ^ 40 * 6680712 * 2
def baseEnd_6680712 : Nat := 1143472123419990305758657

theorem tailTrace_6680712 : CollatzResearch.WordTrace tailWord_6680712 prefixEnd_6680712 1143472123419990305758657 := by
  unfold tailWord_6680712
  simp only [CollatzResearch.WordTrace]
  refine ⟨121832792286464436808534195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 162443723048619249078045593 121832792286464436808534195)
  ·
    refine ⟨182749188429696655212801293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121832792286464436808534195 182749188429696655212801293)
    ·
      refine ⟨68530945661136245704800485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 182749188429696655212801293 68530945661136245704800485)
      ·
        refine ⟨12849552311463046069650091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 68530945661136245704800485 12849552311463046069650091)
        ·
          refine ⟨19274328467194569104475137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12849552311463046069650091 19274328467194569104475137)
          ·
            refine ⟨14455746350395926828356353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19274328467194569104475137 14455746350395926828356353)
            ·
              refine ⟨10841809762796945121267265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14455746350395926828356353 10841809762796945121267265)
              ·
                refine ⟨8131357322097708840950449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10841809762796945121267265 8131357322097708840950449)
                ·
                  refine ⟨6098517991573281630712837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8131357322097708840950449 6098517991573281630712837)
                  ·
                    refine ⟨1143472123419990305758657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6098517991573281630712837 1143472123419990305758657)
                    ·
                      rfl

theorem cell23_6680712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 2, 2, 2, 2, 4].length) (baseStart_6680712 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6680712 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6680712 prefixEnd_6680712 := by exact prefixLift 6680712
  have htrace : WordTrace (prefixWord ++ tailWord_6680712) baseStart_6680712 baseEnd_6680712 := by
    simpa [prefixWord, tailWord_6680712, baseEnd_6680712] using wordTrace_append hprefix tailTrace_6680712
  have hstable : (prefixWord ++ tailWord_6680712).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6680712).length < 2 ^ (prefixWord ++ tailWord_6680712).sum := by decide
  have hdescent : baseEnd_6680712 < baseStart_6680712 := by decide
  rcases family_descends (prefixWord ++ tailWord_6680712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6680731 : List Nat := [1, 1, 1, 1, 1, 1, 2, 4, 4, 2, 5]
def baseStart_6680731 : Nat := 118140960795 + 6680731 * 2 ^ 59
def prefixEnd_6680731 : Nat := 4983230072969 + 3 ^ 40 * 6680731 * 2
def baseEnd_6680731 : Nat := 3430426126392406342938383

theorem tailTrace_6680731 : CollatzResearch.WordTrace tailWord_6680731 prefixEnd_6680731 3430426126392406342938383 := by
  unfold tailWord_6680731
  simp only [CollatzResearch.WordTrace]
  refine ⟨243666277559860039862010047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162444185039906693241340031 243666277559860039862010047)
  ·
    refine ⟨365499416339790059793015071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 243666277559860039862010047 365499416339790059793015071)
    ·
      refine ⟨548249124509685089689522607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 365499416339790059793015071 548249124509685089689522607)
      ·
        refine ⟨822373686764527634534283911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 548249124509685089689522607 822373686764527634534283911)
        ·
          refine ⟨1233560530146791451801425867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 822373686764527634534283911 1233560530146791451801425867)
          ·
            refine ⟨1850340795220187177702138801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1233560530146791451801425867 1850340795220187177702138801)
            ·
              refine ⟨1387755596415140383276604101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1850340795220187177702138801 1387755596415140383276604101)
              ·
                refine ⟨260204174327838821864363269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1387755596415140383276604101 260204174327838821864363269)
                ·
                  refine ⟨48788282686469779099568113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 260204174327838821864363269 48788282686469779099568113)
                  ·
                    refine ⟨36591212014852334324676085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 48788282686469779099568113 36591212014852334324676085)
                    ·
                      refine ⟨3430426126392406342938383, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36591212014852334324676085 3430426126392406342938383)
                      ·
                        rfl

theorem cell23_6680731_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 4, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 4, 4, 2, 5].length) (baseStart_6680731 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6680731 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6680731 prefixEnd_6680731 := by exact prefixLift 6680731
  have htrace : WordTrace (prefixWord ++ tailWord_6680731) baseStart_6680731 baseEnd_6680731 := by
    simpa [prefixWord, tailWord_6680731, baseEnd_6680731] using wordTrace_append hprefix tailTrace_6680731
  have hstable : (prefixWord ++ tailWord_6680731).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6680731).length < 2 ^ (prefixWord ++ tailWord_6680731).sum := by decide
  have hdescent : baseEnd_6680731 < baseStart_6680731 := by decide
  rcases family_descends (prefixWord ++ tailWord_6680731) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6680735 : List Nat := [1, 1, 2, 6, 1, 1, 1, 3, 1, 3, 3]
def baseStart_6680735 : Nat := 118140960795 + 6680735 * 2 ^ 59
def prefixEnd_6680735 : Nat := 4983230072969 + 3 ^ 40 * 6680735 * 2
def baseEnd_6680735 : Nat := 3430428180315024327288365

theorem tailTrace_6680735 : CollatzResearch.WordTrace tailWord_6680735 prefixEnd_6680735 3430428180315024327288365 := by
  unfold tailWord_6680735
  simp only [CollatzResearch.WordTrace]
  refine ⟨243666423451845548545155659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162444282301230365696770439 243666423451845548545155659)
  ·
    refine ⟨365499635177768322817733489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 243666423451845548545155659 365499635177768322817733489)
    ·
      refine ⟨274124726383326242113300117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 365499635177768322817733489 274124726383326242113300117)
      ·
        refine ⟨12849596549218417599060943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 274124726383326242113300117 12849596549218417599060943)
        ·
          refine ⟨19274394823827626398591415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12849596549218417599060943 19274394823827626398591415)
          ·
            refine ⟨28911592235741439597887123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19274394823827626398591415 28911592235741439597887123)
            ·
              refine ⟨43367388353612159396830685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28911592235741439597887123 43367388353612159396830685)
              ·
                refine ⟨16262770632604559773811507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 43367388353612159396830685 16262770632604559773811507)
                ·
                  refine ⟨24394155948906839660717261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16262770632604559773811507 24394155948906839660717261)
                  ·
                    refine ⟨9147808480840064872768973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24394155948906839660717261 9147808480840064872768973)
                    ·
                      refine ⟨3430428180315024327288365, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9147808480840064872768973 3430428180315024327288365)
                      ·
                        rfl

theorem cell23_6680735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 1, 3, 1, 3, 3].length) (baseStart_6680735 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6680735 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6680735 prefixEnd_6680735 := by exact prefixLift 6680735
  have htrace : WordTrace (prefixWord ++ tailWord_6680735) baseStart_6680735 baseEnd_6680735 := by
    simpa [prefixWord, tailWord_6680735, baseEnd_6680735] using wordTrace_append hprefix tailTrace_6680735
  have hstable : (prefixWord ++ tailWord_6680735).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6680735).length < 2 ^ (prefixWord ++ tailWord_6680735).sum := by decide
  have hdescent : baseEnd_6680735 < baseStart_6680735 := by decide
  rcases family_descends (prefixWord ++ tailWord_6680735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6680751 : List Nat := [1, 1, 2, 1, 2, 3, 1, 1, 3, 8]
def baseStart_6680751 : Nat := 118140960795 + 6680751 * 2 ^ 59
def prefixEnd_6680751 : Nat := 4983230072969 + 3 ^ 40 * 6680751 * 2
def baseEnd_6680751 : Nat := 1143478798668498754896097

theorem tailTrace_6680751 : CollatzResearch.WordTrace tailWord_6680751 prefixEnd_6680751 1143478798668498754896097 := by
  unfold tailWord_6680751
  simp only [CollatzResearch.WordTrace]
  refine ⟨243667007019787583277738107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162444671346525055518492071 243667007019787583277738107)
  ·
    refine ⟨365500510529681374916607161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 243667007019787583277738107 365500510529681374916607161)
    ·
      refine ⟨274125382897261031187455371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 365500510529681374916607161 274125382897261031187455371)
      ·
        refine ⟨411188074345891546781183057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 274125382897261031187455371 411188074345891546781183057)
        ·
          refine ⟨308391055759418660085887293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 411188074345891546781183057 308391055759418660085887293)
          ·
            refine ⟨115646645909781997532207735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 308391055759418660085887293 115646645909781997532207735)
            ·
              refine ⟨173469968864672996298311603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 115646645909781997532207735 173469968864672996298311603)
              ·
                refine ⟨260204953297009494447467405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 173469968864672996298311603 260204953297009494447467405)
                ·
                  refine ⟨97576857486378560417800277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 260204953297009494447467405 97576857486378560417800277)
                  ·
                    refine ⟨1143478798668498754896097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 97576857486378560417800277 1143478798668498754896097)
                    ·
                      rfl

theorem cell23_6680751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 1, 1, 3, 8].length) (baseStart_6680751 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6680751 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6680751 prefixEnd_6680751 := by exact prefixLift 6680751
  have htrace : WordTrace (prefixWord ++ tailWord_6680751) baseStart_6680751 baseEnd_6680751 := by
    simpa [prefixWord, tailWord_6680751, baseEnd_6680751] using wordTrace_append hprefix tailTrace_6680751
  have hstable : (prefixWord ++ tailWord_6680751).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6680751).length < 2 ^ (prefixWord ++ tailWord_6680751).sum := by decide
  have hdescent : baseEnd_6680751 < baseStart_6680751 := by decide
  rcases family_descends (prefixWord ++ tailWord_6680751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6680768 : List Nat := [2, 1, 1, 2, 5, 1, 1, 2, 2, 6]
def baseStart_6680768 : Nat := 118140960795 + 6680768 * 2 ^ 59
def prefixEnd_6680768 : Nat := 4983230072969 + 3 ^ 40 * 6680768 * 2
def baseEnd_6680768 : Nat := 1143481708392207566058571

theorem tailTrace_6680768 : CollatzResearch.WordTrace tailWord_6680768 prefixEnd_6680768 1143481708392207566058571 := by
  unfold tailWord_6680768
  simp only [CollatzResearch.WordTrace]
  refine ⟨121833813530362997590553479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 162445084707150663454071305 121833813530362997590553479)
  ·
    refine ⟨182750720295544496385830219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121833813530362997590553479 182750720295544496385830219)
    ·
      refine ⟨274126080443316744578745329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 182750720295544496385830219 274126080443316744578745329)
      ·
        refine ⟨205594560332487558434058997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 274126080443316744578745329 205594560332487558434058997)
        ·
          refine ⟨19274490031170708603193031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 205594560332487558434058997 19274490031170708603193031)
          ·
            refine ⟨28911735046756062904789547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19274490031170708603193031 28911735046756062904789547)
            ·
              refine ⟨43367602570134094357184321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28911735046756062904789547 43367602570134094357184321)
              ·
                refine ⟨32525701927600570767888241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43367602570134094357184321 32525701927600570767888241)
                ·
                  refine ⟨24394276445700428075916181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32525701927600570767888241 24394276445700428075916181)
                  ·
                    refine ⟨1143481708392207566058571, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24394276445700428075916181 1143481708392207566058571)
                    ·
                      rfl

theorem cell23_6680768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 1, 2, 2, 6].length) (baseStart_6680768 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6680768 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6680768 prefixEnd_6680768 := by exact prefixLift 6680768
  have htrace : WordTrace (prefixWord ++ tailWord_6680768) baseStart_6680768 baseEnd_6680768 := by
    simpa [prefixWord, tailWord_6680768, baseEnd_6680768] using wordTrace_append hprefix tailTrace_6680768
  have hstable : (prefixWord ++ tailWord_6680768).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6680768).length < 2 ^ (prefixWord ++ tailWord_6680768).sum := by decide
  have hdescent : baseEnd_6680768 < baseStart_6680768 := by decide
  rcases family_descends (prefixWord ++ tailWord_6680768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6680769 : List Nat := [1, 2, 6, 1, 2, 1, 1, 1, 4, 1, 3]
def baseStart_6680769 : Nat := 118140960795 + 6680769 * 2 ^ 59
def prefixEnd_6680769 : Nat := 4983230072969 + 3 ^ 40 * 6680769 * 2
def baseEnd_6680769 : Nat := 3430445638657277194263209

theorem tailTrace_6680769 : CollatzResearch.WordTrace tailWord_6680769 prefixEnd_6680769 3430445638657277194263209 := by
  unfold tailWord_6680769
  simp only [CollatzResearch.WordTrace]
  refine ⟨243667663533722372351893361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162445109022481581567928907 243667663533722372351893361)
  ·
    refine ⟨182750747650291779263920021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 243667663533722372351893361 182750747650291779263920021)
    ·
      refine ⟨8566441296107427152996251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 182750747650291779263920021 8566441296107427152996251)
      ·
        refine ⟨12849661944161140729494377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8566441296107427152996251 12849661944161140729494377)
        ·
          refine ⟨9637246458120855547120783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12849661944161140729494377 9637246458120855547120783)
          ·
            refine ⟨14455869687181283320681175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9637246458120855547120783 14455869687181283320681175)
            ·
              refine ⟨21683804530771924981021763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14455869687181283320681175 21683804530771924981021763)
              ·
                refine ⟨32525706796157887471532645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21683804530771924981021763 32525706796157887471532645)
                ·
                  refine ⟨6098570024279603900912371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 32525706796157887471532645 6098570024279603900912371)
                  ·
                    refine ⟨9147855036419405851368557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6098570024279603900912371 9147855036419405851368557)
                    ·
                      refine ⟨3430445638657277194263209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9147855036419405851368557 3430445638657277194263209)
                      ·
                        rfl

theorem cell23_6680769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 2, 1, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 2, 1, 1, 1, 4, 1, 3].length) (baseStart_6680769 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6680769 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6680769 prefixEnd_6680769 := by exact prefixLift 6680769
  have htrace : WordTrace (prefixWord ++ tailWord_6680769) baseStart_6680769 baseEnd_6680769 := by
    simpa [prefixWord, tailWord_6680769, baseEnd_6680769] using wordTrace_append hprefix tailTrace_6680769
  have hstable : (prefixWord ++ tailWord_6680769).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6680769).length < 2 ^ (prefixWord ++ tailWord_6680769).sum := by decide
  have hdescent : baseEnd_6680769 < baseStart_6680769 := by decide
  rcases family_descends (prefixWord ++ tailWord_6680769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6680792 : List Nat := [2, 1, 2, 2, 4, 1, 3, 1, 1, 4, 2]
def baseStart_6680792 : Nat := 118140960795 + 6680792 * 2 ^ 59
def prefixEnd_6680792 : Nat := 4983230072969 + 3 ^ 40 * 6680792 * 2
def baseEnd_6680792 : Nat := 3430457448712330604275603

theorem tailTrace_6680792 : CollatzResearch.WordTrace tailWord_6680792 prefixEnd_6680792 3430457448712330604275603 := by
  unfold tailWord_6680792
  simp only [CollatzResearch.WordTrace]
  refine ⟨121834251206319523639990315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 162445668275092698186653753 121834251206319523639990315)
  ·
    refine ⟨182751376809479285459985473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121834251206319523639990315 182751376809479285459985473)
    ·
      refine ⟨137063532607109464094989105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 182751376809479285459985473 137063532607109464094989105)
      ·
        refine ⟨102797649455332098071241829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 137063532607109464094989105 102797649455332098071241829)
        ·
          refine ⟨19274559272874768388357843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 102797649455332098071241829 19274559272874768388357843)
          ·
            refine ⟨28911838909312152582536765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19274559272874768388357843 28911838909312152582536765)
            ·
              refine ⟨10841939590992057218451287, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28911838909312152582536765 10841939590992057218451287)
              ·
                refine ⟨16262909386488085827676931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10841939590992057218451287 16262909386488085827676931)
                ·
                  refine ⟨24394364079732128741515397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16262909386488085827676931 24394364079732128741515397)
                  ·
                    refine ⟨4573943264949774139034137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24394364079732128741515397 4573943264949774139034137)
                    ·
                      refine ⟨3430457448712330604275603, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4573943264949774139034137 3430457448712330604275603)
                      ·
                        rfl

theorem cell23_6680792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 3, 1, 1, 4, 2].length) (baseStart_6680792 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6680792 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6680792 prefixEnd_6680792 := by exact prefixLift 6680792
  have htrace : WordTrace (prefixWord ++ tailWord_6680792) baseStart_6680792 baseEnd_6680792 := by
    simpa [prefixWord, tailWord_6680792, baseEnd_6680792] using wordTrace_append hprefix tailTrace_6680792
  have hstable : (prefixWord ++ tailWord_6680792).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6680792).length < 2 ^ (prefixWord ++ tailWord_6680792).sum := by decide
  have hdescent : baseEnd_6680792 < baseStart_6680792 := by decide
  rcases family_descends (prefixWord ++ tailWord_6680792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6680835 : List Nat := [1, 1, 1, 3, 2, 3, 2, 1, 2, 5, 2]
def baseStart_6680835 : Nat := 118140960795 + 6680835 * 2 ^ 59
def prefixEnd_6680835 : Nat := 4983230072969 + 3 ^ 40 * 6680835 * 2
def baseEnd_6680835 : Nat := 3430479528380473936037905

theorem tailTrace_6680835 : CollatzResearch.WordTrace tailWord_6680835 prefixEnd_6680835 3430479528380473936037905 := by
  unfold tailWord_6680835
  simp only [CollatzResearch.WordTrace]
  refine ⟨243670070751483265623795959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162446713834322177082530639 243670070751483265623795959)
  ·
    refine ⟨365505106127224898435693939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 243670070751483265623795959 365505106127224898435693939)
    ·
      refine ⟨548257659190837347653540909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 365505106127224898435693939 548257659190837347653540909)
      ·
        refine ⟨205596622196564005370077841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 548257659190837347653540909 205596622196564005370077841)
        ·
          refine ⟨154197466647423004027558381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 205596622196564005370077841 154197466647423004027558381)
          ·
            refine ⟨57824049992783626510334393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 154197466647423004027558381 57824049992783626510334393)
            ·
              refine ⟨43368037494587719882750795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 57824049992783626510334393 43368037494587719882750795)
              ·
                refine ⟨65052056241881579824126193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43368037494587719882750795 65052056241881579824126193)
                ·
                  refine ⟨48789042181411184868094645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 65052056241881579824126193 48789042181411184868094645)
                  ·
                    refine ⟨4573972704507298581383873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 48789042181411184868094645 4573972704507298581383873)
                    ·
                      refine ⟨3430479528380473936037905, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4573972704507298581383873 3430479528380473936037905)
                      ·
                        rfl

theorem cell23_6680835_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 2, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 2, 1, 2, 5, 2].length) (baseStart_6680835 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6680835 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6680835 prefixEnd_6680835 := by exact prefixLift 6680835
  have htrace : WordTrace (prefixWord ++ tailWord_6680835) baseStart_6680835 baseEnd_6680835 := by
    simpa [prefixWord, tailWord_6680835, baseEnd_6680835] using wordTrace_append hprefix tailTrace_6680835
  have hstable : (prefixWord ++ tailWord_6680835).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6680835).length < 2 ^ (prefixWord ++ tailWord_6680835).sum := by decide
  have hdescent : baseEnd_6680835 < baseStart_6680835 := by decide
  rcases family_descends (prefixWord ++ tailWord_6680835) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6680865 : List Nat := [1, 2, 3, 2, 1, 1, 3, 3, 2, 1, 4]
def baseStart_6680865 : Nat := 118140960795 + 6680865 * 2 ^ 59
def prefixEnd_6680865 : Nat := 4983230072969 + 3 ^ 40 * 6680865 * 2
def baseEnd_6680865 : Nat := 3430494932800108818662767

theorem tailTrace_6680865 : CollatzResearch.WordTrace tailWord_6680865 prefixEnd_6680865 3430494932800108818662767 := by
  unfold tailWord_6680865
  simp only [CollatzResearch.WordTrace]
  refine ⟨243671164941374580747388049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162447443294249720498258699 243671164941374580747388049)
  ·
    refine ⟨182753373706030935560541037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 243671164941374580747388049 182753373706030935560541037)
    ·
      refine ⟨68532515139761600835202889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 182753373706030935560541037 68532515139761600835202889)
      ·
        refine ⟨51399386354821200626402167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68532515139761600835202889 51399386354821200626402167)
        ·
          refine ⟨77099079532231800939603251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51399386354821200626402167 77099079532231800939603251)
          ·
            refine ⟨115648619298347701409404877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77099079532231800939603251 115648619298347701409404877)
            ·
              refine ⟨43368232236880388028526829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 115648619298347701409404877 43368232236880388028526829)
              ·
                refine ⟨16263087088830145510697561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 43368232236880388028526829 16263087088830145510697561)
                ·
                  refine ⟨12197315316622609133023171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16263087088830145510697561 12197315316622609133023171)
                  ·
                    refine ⟨18295972974933913699534757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12197315316622609133023171 18295972974933913699534757)
                    ·
                      refine ⟨3430494932800108818662767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18295972974933913699534757 3430494932800108818662767)
                      ·
                        rfl

theorem cell23_6680865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 3, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 3, 3, 2, 1, 4].length) (baseStart_6680865 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6680865 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6680865 prefixEnd_6680865 := by exact prefixLift 6680865
  have htrace : WordTrace (prefixWord ++ tailWord_6680865) baseStart_6680865 baseEnd_6680865 := by
    simpa [prefixWord, tailWord_6680865, baseEnd_6680865] using wordTrace_append hprefix tailTrace_6680865
  have hstable : (prefixWord ++ tailWord_6680865).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6680865).length < 2 ^ (prefixWord ++ tailWord_6680865).sum := by decide
  have hdescent : baseEnd_6680865 < baseStart_6680865 := by decide
  rcases family_descends (prefixWord ++ tailWord_6680865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6680888 : List Nat := [2, 1, 2, 1, 3, 1, 2, 3, 8]
def baseStart_6680888 : Nat := 118140960795 + 6680888 * 2 ^ 59
def prefixEnd_6680888 : Nat := 4983230072969 + 3 ^ 40 * 6680888 * 2
def baseEnd_6680888 : Nat := 381167415872795803186129

theorem tailTrace_6680888 : CollatzResearch.WordTrace tailWord_6680888 prefixEnd_6680888 381167415872795803186129 := by
  unfold tailWord_6680888
  simp only [CollatzResearch.WordTrace]
  refine ⟨121836001910145627837737659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 162448002546860837116983545 121836001910145627837737659)
  ·
    refine ⟨182754002865218441756606489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121836001910145627837737659 182754002865218441756606489)
    ·
      refine ⟨137065502148913831317454867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 182754002865218441756606489 137065502148913831317454867)
      ·
        refine ⟨205598253223370746976182301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 137065502148913831317454867 205598253223370746976182301)
        ·
          refine ⟨77099344958764030116068363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 205598253223370746976182301 77099344958764030116068363)
          ·
            refine ⟨115649017438146045174102545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77099344958764030116068363 115649017438146045174102545)
            ·
              refine ⟨86736763078609533880576909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 115649017438146045174102545 86736763078609533880576909)
              ·
                refine ⟨32526286154478575205216341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 86736763078609533880576909 32526286154478575205216341)
                ·
                  refine ⟨381167415872795803186129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 32526286154478575205216341 381167415872795803186129)
                  ·
                    rfl

theorem cell23_6680888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 2, 3, 8].length) (baseStart_6680888 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6680888 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6680888 prefixEnd_6680888 := by exact prefixLift 6680888
  have htrace : WordTrace (prefixWord ++ tailWord_6680888) baseStart_6680888 baseEnd_6680888 := by
    simpa [prefixWord, tailWord_6680888, baseEnd_6680888] using wordTrace_append hprefix tailTrace_6680888
  have hstable : (prefixWord ++ tailWord_6680888).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6680888).length < 2 ^ (prefixWord ++ tailWord_6680888).sum := by decide
  have hdescent : baseEnd_6680888 < baseStart_6680888 := by decide
  rcases family_descends (prefixWord ++ tailWord_6680888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6680932 : List Nat := [2, 3, 1, 1, 3, 1, 1, 2, 5, 1, 3]
def baseStart_6680932 : Nat := 118140960795 + 6680932 * 2 ^ 59
def prefixEnd_6680932 : Nat := 4983230072969 + 3 ^ 40 * 6680932 * 2
def baseEnd_6680932 : Nat := 3430529336003960056524959

theorem tailTrace_6680932 : CollatzResearch.WordTrace tailWord_6680932 prefixEnd_6680932 3430529336003960056524959 := by
  unfold tailWord_6680932
  simp only [CollatzResearch.WordTrace]
  refine ⟨121836804316065925595038525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 162449072421421234126718033 121836804316065925595038525)
  ·
    refine ⟨45688801618524722098139447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 121836804316065925595038525 45688801618524722098139447)
    ·
      refine ⟨68533202427787083147209171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45688801618524722098139447 68533202427787083147209171)
      ·
        refine ⟨102799803641680624720813757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68533202427787083147209171 102799803641680624720813757)
        ·
          refine ⟨38549926365630234270305159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 102799803641680624720813757 38549926365630234270305159)
          ·
            refine ⟨57824889548445351405457739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38549926365630234270305159 57824889548445351405457739)
            ·
              refine ⟨86737334322668027108186609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57824889548445351405457739 86737334322668027108186609)
              ·
                refine ⟨65053000742001020331139957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 86737334322668027108186609 65053000742001020331139957)
                ·
                  refine ⟨6098718819562595656044371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 65053000742001020331139957 6098718819562595656044371)
                  ·
                    refine ⟨9148078229343893484066557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6098718819562595656044371 9148078229343893484066557)
                    ·
                      refine ⟨3430529336003960056524959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9148078229343893484066557 3430529336003960056524959)
                      ·
                        rfl

theorem cell23_6680932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 1, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 1, 2, 5, 1, 3].length) (baseStart_6680932 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6680932 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6680932 prefixEnd_6680932 := by exact prefixLift 6680932
  have htrace : WordTrace (prefixWord ++ tailWord_6680932) baseStart_6680932 baseEnd_6680932 := by
    simpa [prefixWord, tailWord_6680932, baseEnd_6680932] using wordTrace_append hprefix tailTrace_6680932
  have hstable : (prefixWord ++ tailWord_6680932).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6680932).length < 2 ^ (prefixWord ++ tailWord_6680932).sum := by decide
  have hdescent : baseEnd_6680932 < baseStart_6680932 := by decide
  rcases family_descends (prefixWord ++ tailWord_6680932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6680949 : List Nat := [1, 3, 4, 1, 2, 1, 1, 3, 3, 1, 3]
def baseStart_6680949 : Nat := 118140960795 + 6680949 * 2 ^ 59
def prefixEnd_6680949 : Nat := 4983230072969 + 3 ^ 40 * 6680949 * 2
def baseEnd_6680949 : Nat := 3430538065175086490012381

theorem tailTrace_6680949 : CollatzResearch.WordTrace tailWord_6680949 prefixEnd_6680949 3430538065175086490012381 := by
  unfold tailWord_6680949
  simp only [CollatzResearch.WordTrace]
  refine ⟨243674228673070263093445901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162449485782046842062297267 243674228673070263093445901)
  ·
    refine ⟨91377835752401348660042213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 243674228673070263093445901 91377835752401348660042213)
    ·
      refine ⟨17133344203575252873757915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 91377835752401348660042213 17133344203575252873757915)
      ·
        refine ⟨25700016305362879310636873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17133344203575252873757915 25700016305362879310636873)
        ·
          refine ⟨19275012229022159482977655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25700016305362879310636873 19275012229022159482977655)
          ·
            refine ⟨28912518343533239224466483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19275012229022159482977655 28912518343533239224466483)
            ·
              refine ⟨43368777515299858836699725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28912518343533239224466483 43368777515299858836699725)
              ·
                refine ⟨16263291568237447063762397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 43368777515299858836699725 16263291568237447063762397)
                ·
                  refine ⟨6098734338089042648910899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16263291568237447063762397 6098734338089042648910899)
                  ·
                    refine ⟨9148101507133563973366349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6098734338089042648910899 9148101507133563973366349)
                    ·
                      refine ⟨3430538065175086490012381, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9148101507133563973366349 3430538065175086490012381)
                      ·
                        rfl

theorem cell23_6680949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 1, 3, 3, 1, 3].length) (baseStart_6680949 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6680949 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6680949 prefixEnd_6680949 := by exact prefixLift 6680949
  have htrace : WordTrace (prefixWord ++ tailWord_6680949) baseStart_6680949 baseEnd_6680949 := by
    simpa [prefixWord, tailWord_6680949, baseEnd_6680949] using wordTrace_append hprefix tailTrace_6680949
  have hstable : (prefixWord ++ tailWord_6680949).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6680949).length < 2 ^ (prefixWord ++ tailWord_6680949).sum := by decide
  have hdescent : baseEnd_6680949 < baseStart_6680949 := by decide
  rcases family_descends (prefixWord ++ tailWord_6680949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6680972 : List Nat := [2, 2, 1, 2, 1, 4, 1, 4, 1, 1, 4]
def baseStart_6680972 : Nat := 118140960795 + 6680972 * 2 ^ 59
def prefixEnd_6680972 : Nat := 4983230072969 + 3 ^ 40 * 6680972 * 2
def baseEnd_6680972 : Nat := 3430549875230139900024775

theorem tailTrace_6680972 : CollatzResearch.WordTrace tailWord_6680972 prefixEnd_6680972 3430549875230139900024775 := by
  unfold tailWord_6680972
  simp only [CollatzResearch.WordTrace]
  refine ⟨121837533775993469010766585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 162450045034657958681022113 121837533775993469010766585)
  ·
    refine ⟨91378150331995101758074939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 121837533775993469010766585 91378150331995101758074939)
    ·
      refine ⟨137067225497992652637112409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91378150331995101758074939 137067225497992652637112409)
      ·
        refine ⟨102800419123494489477834307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 137067225497992652637112409 102800419123494489477834307)
        ·
          refine ⟨154200628685241734216751461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 102800419123494489477834307 154200628685241734216751461)
          ·
            refine ⟨28912617878482825165640899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 154200628685241734216751461 28912617878482825165640899)
            ·
              refine ⟨43368926817724237748461349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28912617878482825165640899 43368926817724237748461349)
              ·
                refine ⟨8131673778323294577836503, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 43368926817724237748461349 8131673778323294577836503)
                ·
                  refine ⟨12197510667484941866754755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8131673778323294577836503 12197510667484941866754755)
                  ·
                    refine ⟨18296266001227412800132133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12197510667484941866754755 18296266001227412800132133)
                    ·
                      refine ⟨3430549875230139900024775, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18296266001227412800132133 3430549875230139900024775)
                      ·
                        rfl

theorem cell23_6680972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 1, 4, 1, 1, 4].length) (baseStart_6680972 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6680972 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6680972 prefixEnd_6680972 := by exact prefixLift 6680972
  have htrace : WordTrace (prefixWord ++ tailWord_6680972) baseStart_6680972 baseEnd_6680972 := by
    simpa [prefixWord, tailWord_6680972, baseEnd_6680972] using wordTrace_append hprefix tailTrace_6680972
  have hstable : (prefixWord ++ tailWord_6680972).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6680972).length < 2 ^ (prefixWord ++ tailWord_6680972).sum := by decide
  have hdescent : baseEnd_6680972 < baseStart_6680972 := by decide
  rcases family_descends (prefixWord ++ tailWord_6680972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6680985 : List Nat := [1, 2, 1, 2, 1, 4, 2, 1, 3, 2, 4]
def baseStart_6680985 : Nat := 118140960795 + 6680985 * 2 ^ 59
def prefixEnd_6680985 : Nat := 4983230072969 + 3 ^ 40 * 6680985 * 2
def baseEnd_6680985 : Nat := 3430556550478648349162215

theorem tailTrace_6680985 : CollatzResearch.WordTrace tailWord_6680985 prefixEnd_6680985 3430556550478648349162215 := by
  unfold tailWord_6680985
  simp only [CollatzResearch.WordTrace]
  refine ⟨243675541700939841241756409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162450361133959894161170939 243675541700939841241756409)
  ·
    refine ⟨182756656275704880931317307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 243675541700939841241756409 182756656275704880931317307)
    ·
      refine ⟨274134984413557321396975961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 182756656275704880931317307 274134984413557321396975961)
      ·
        refine ⟨205601238310167991047731971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 274134984413557321396975961 205601238310167991047731971)
        ·
          refine ⟨308401857465251986571597957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 205601238310167991047731971 308401857465251986571597957)
          ·
            refine ⟨57825348274734747482174617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 308401857465251986571597957 57825348274734747482174617)
            ·
              refine ⟨43369011206051060611630963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 57825348274734747482174617 43369011206051060611630963)
              ·
                refine ⟨65053516809076590917446445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43369011206051060611630963 65053516809076590917446445)
                ·
                  refine ⟨24395068803403721594042417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 65053516809076590917446445 24395068803403721594042417)
                  ·
                    refine ⟨18296301602552791195531813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24395068803403721594042417 18296301602552791195531813)
                    ·
                      refine ⟨3430556550478648349162215, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18296301602552791195531813 3430556550478648349162215)
                      ·
                        rfl

theorem cell23_6680985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 2, 1, 3, 2, 4].length) (baseStart_6680985 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6680985 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6680985 prefixEnd_6680985 := by exact prefixLift 6680985
  have htrace : WordTrace (prefixWord ++ tailWord_6680985) baseStart_6680985 baseEnd_6680985 := by
    simpa [prefixWord, tailWord_6680985, baseEnd_6680985] using wordTrace_append hprefix tailTrace_6680985
  have hstable : (prefixWord ++ tailWord_6680985).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6680985).length < 2 ^ (prefixWord ++ tailWord_6680985).sum := by decide
  have hdescent : baseEnd_6680985 < baseStart_6680985 := by decide
  rcases family_descends (prefixWord ++ tailWord_6680985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6680992 : List Nat := [2, 1, 1, 4, 1, 4, 2, 1, 1, 1, 5]
def baseStart_6680992 : Nat := 118140960795 + 6680992 * 2 ^ 59
def prefixEnd_6680992 : Nat := 4983230072969 + 3 ^ 40 * 6680992 * 2
def baseEnd_6680992 : Nat := 3430560144843229821774683

theorem tailTrace_6680992 : CollatzResearch.WordTrace tailWord_6680992 prefixEnd_6680992 3430560144843229821774683 := by
  unfold tailWord_6680992
  simp only [CollatzResearch.WordTrace]
  refine ⟨121837898505957240718630615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 162450531341276320958174153 121837898505957240718630615)
  ·
    refine ⟨182756847758935861077945923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121837898505957240718630615 182756847758935861077945923)
    ·
      refine ⟨274135271638403791616918885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 182756847758935861077945923 274135271638403791616918885)
      ·
        refine ⟨51400363432200710928172291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 274135271638403791616918885 51400363432200710928172291)
        ·
          refine ⟨77100545148301066392258437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51400363432200710928172291 77100545148301066392258437)
          ·
            refine ⟨14456352215306449948548457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 77100545148301066392258437 14456352215306449948548457)
            ·
              refine ⟨10842264161479837461411343, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14456352215306449948548457 10842264161479837461411343)
              ·
                refine ⟨16263396242219756192117015, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10842264161479837461411343 16263396242219756192117015)
                ·
                  refine ⟨24395094363329634288175523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16263396242219756192117015 24395094363329634288175523)
                  ·
                    refine ⟨36592641544994451432263285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24395094363329634288175523 36592641544994451432263285)
                    ·
                      refine ⟨3430560144843229821774683, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36592641544994451432263285 3430560144843229821774683)
                      ·
                        rfl

theorem cell23_6680992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 4, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 4, 2, 1, 1, 1, 5].length) (baseStart_6680992 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6680992 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6680992 prefixEnd_6680992 := by exact prefixLift 6680992
  have htrace : WordTrace (prefixWord ++ tailWord_6680992) baseStart_6680992 baseEnd_6680992 := by
    simpa [prefixWord, tailWord_6680992, baseEnd_6680992] using wordTrace_append hprefix tailTrace_6680992
  have hstable : (prefixWord ++ tailWord_6680992).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6680992).length < 2 ^ (prefixWord ++ tailWord_6680992).sum := by decide
  have hdescent : baseEnd_6680992 < baseStart_6680992 := by decide
  rcases family_descends (prefixWord ++ tailWord_6680992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6680995 : List Nat := [1, 1, 1, 4, 1, 6, 9]
def baseStart_6680995 : Nat := 118140960795 + 6680995 * 2 ^ 59
def prefixEnd_6680995 : Nat := 4983230072969 + 3 ^ 40 * 6680995 * 2
def baseEnd_6680995 : Nat := 42352613398582633457249

theorem tailTrace_6680995 : CollatzResearch.WordTrace tailWord_6680995 prefixEnd_6680995 42352613398582633457249 := by
  unfold tailWord_6680995
  simp only [CollatzResearch.WordTrace]
  refine ⟨243675906430903612949620439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162450604287269075299746959 243675906430903612949620439)
  ·
    refine ⟨365513859646355419424430659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 243675906430903612949620439 365513859646355419424430659)
    ·
      refine ⟨548270789469533129136645989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 365513859646355419424430659 548270789469533129136645989)
      ·
        refine ⟨102800773025537461713121123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 548270789469533129136645989 102800773025537461713121123)
        ·
          refine ⟨154201159538306192569681685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 102800773025537461713121123 154201159538306192569681685)
          ·
            refine ⟨7228179353358102776703829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 154201159538306192569681685 7228179353358102776703829)
            ·
              refine ⟨42352613398582633457249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 7228179353358102776703829 42352613398582633457249)
              ·
                rfl

theorem cell23_6680995_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 6, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 6, 9].length) (baseStart_6680995 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6680995 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6680995 prefixEnd_6680995 := by exact prefixLift 6680995
  have htrace : WordTrace (prefixWord ++ tailWord_6680995) baseStart_6680995 baseEnd_6680995 := by
    simpa [prefixWord, tailWord_6680995, baseEnd_6680995] using wordTrace_append hprefix tailTrace_6680995
  have hstable : (prefixWord ++ tailWord_6680995).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6680995).length < 2 ^ (prefixWord ++ tailWord_6680995).sum := by decide
  have hdescent : baseEnd_6680995 < baseStart_6680995 := by decide
  rcases family_descends (prefixWord ++ tailWord_6680995) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6681000 : List Nat := [2, 1, 6, 1, 1, 2, 3, 2, 1, 1, 3]
def baseStart_6681000 : Nat := 118140960795 + 6681000 * 2 ^ 59
def prefixEnd_6681000 : Nat := 4983230072969 + 3 ^ 40 * 6681000 * 2
def baseEnd_6681000 : Nat := 3430564252688465790474647

theorem tailTrace_6681000 : CollatzResearch.WordTrace tailWord_6681000 prefixEnd_6681000 3430564252688465790474647 := by
  unfold tailWord_6681000
  simp only [CollatzResearch.WordTrace]
  refine ⟨121838044397942749401776227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 162450725863923665869034969 121838044397942749401776227)
  ·
    refine ⟨182757066596914124102664341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121838044397942749401776227 182757066596914124102664341)
    ·
      refine ⟨8566737496730349567312391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 182757066596914124102664341 8566737496730349567312391)
      ·
        refine ⟨12850106245095524350968587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8566737496730349567312391 12850106245095524350968587)
        ·
          refine ⟨19275159367643286526452881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12850106245095524350968587 19275159367643286526452881)
          ·
            refine ⟨14456369525732464894839661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19275159367643286526452881 14456369525732464894839661)
            ·
              refine ⟨5421138572149674335564873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14456369525732464894839661 5421138572149674335564873)
              ·
                refine ⟨4065853929112255751673655, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5421138572149674335564873 4065853929112255751673655)
                ·
                  refine ⟨6098780893668383627510483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4065853929112255751673655 6098780893668383627510483)
                  ·
                    refine ⟨9148171340502575441265725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6098780893668383627510483 9148171340502575441265725)
                    ·
                      refine ⟨3430564252688465790474647, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9148171340502575441265725 3430564252688465790474647)
                      ·
                        rfl

theorem cell23_6681000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 2, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 2, 3, 2, 1, 1, 3].length) (baseStart_6681000 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6681000 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6681000 prefixEnd_6681000 := by exact prefixLift 6681000
  have htrace : WordTrace (prefixWord ++ tailWord_6681000) baseStart_6681000 baseEnd_6681000 := by
    simpa [prefixWord, tailWord_6681000, baseEnd_6681000] using wordTrace_append hprefix tailTrace_6681000
  have hstable : (prefixWord ++ tailWord_6681000).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6681000).length < 2 ^ (prefixWord ++ tailWord_6681000).sum := by decide
  have hdescent : baseEnd_6681000 < baseStart_6681000 := by decide
  rcases family_descends (prefixWord ++ tailWord_6681000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6681065 : List Nat := [1, 2, 1, 1, 1, 2, 1, 4, 4, 1, 5]
def baseStart_6681065 : Nat := 118140960795 + 6681065 * 2 ^ 59
def prefixEnd_6681065 : Nat := 4983230072969 + 3 ^ 40 * 6681065 * 2
def baseEnd_6681065 : Nat := 3430597628931008036161847

theorem tailTrace_6681065 : CollatzResearch.WordTrace tailWord_6681065 prefixEnd_6681065 3430597628931008036161847 := by
  unfold tailWord_6681065
  simp only [CollatzResearch.WordTrace]
  refine ⟨243678459540650014904668649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162452306360433343269779099 243678459540650014904668649)
  ·
    refine ⟨182758844655487511178501487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 243678459540650014904668649 182758844655487511178501487)
    ·
      refine ⟨274138266983231266767752231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 182758844655487511178501487 274138266983231266767752231)
      ·
        refine ⟨411207400474846900151628347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 274138266983231266767752231 411207400474846900151628347)
        ·
          refine ⟨616811100712270350227442521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 411207400474846900151628347 616811100712270350227442521)
          ·
            refine ⟨462608325534202762670581891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 616811100712270350227442521 462608325534202762670581891)
            ·
              refine ⟨693912488301304144005872837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 462608325534202762670581891 693912488301304144005872837)
              ·
                refine ⟨130108591556494527001101157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 693912488301304144005872837 130108591556494527001101157)
                ·
                  refine ⟨24395360916842723812706467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 130108591556494527001101157 24395360916842723812706467)
                  ·
                    refine ⟨36593041375264085719059701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24395360916842723812706467 36593041375264085719059701)
                    ·
                      refine ⟨3430597628931008036161847, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36593041375264085719059701 3430597628931008036161847)
                      ·
                        rfl

theorem cell23_6681065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 4, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 4, 4, 1, 5].length) (baseStart_6681065 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6681065 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6681065 prefixEnd_6681065 := by exact prefixLift 6681065
  have htrace : WordTrace (prefixWord ++ tailWord_6681065) baseStart_6681065 baseEnd_6681065 := by
    simpa [prefixWord, tailWord_6681065, baseEnd_6681065] using wordTrace_append hprefix tailTrace_6681065
  have hstable : (prefixWord ++ tailWord_6681065).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6681065).length < 2 ^ (prefixWord ++ tailWord_6681065).sum := by decide
  have hdescent : baseEnd_6681065 < baseStart_6681065 := by decide
  rcases family_descends (prefixWord ++ tailWord_6681065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6681130 : List Nat := [3, 1, 4, 1, 1, 3, 3, 1, 2, 2, 2]
def baseStart_6681130 : Nat := 118140960795 + 6681130 * 2 ^ 59
def prefixEnd_6681130 : Nat := 4983230072969 + 3 ^ 40 * 6681130 * 2
def baseEnd_6681130 : Nat := 3430631005173550281849049

theorem tailTrace_6681130 : CollatzResearch.WordTrace tailWord_6681130 prefixEnd_6681130 3430631005173550281849049 := by
  unfold tailWord_6681130
  simp only [CollatzResearch.WordTrace]
  refine ⟨60920207571353632751446211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 162453886856943020670523229 60920207571353632751446211)
  ·
    refine ⟨91380311357030449127169317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60920207571353632751446211 91380311357030449127169317)
    ·
      refine ⟨17133808379443209211344247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 91380311357030449127169317 17133808379443209211344247)
      ·
        refine ⟨25700712569164813817016371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17133808379443209211344247 25700712569164813817016371)
        ·
          refine ⟨38551068853747220725524557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25700712569164813817016371 38551068853747220725524557)
          ·
            refine ⟨14456650820155207772071709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38551068853747220725524557 14456650820155207772071709)
            ·
              refine ⟨5421244057558202914526891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14456650820155207772071709 5421244057558202914526891)
              ·
                refine ⟨8131866086337304371790337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5421244057558202914526891 8131866086337304371790337)
                ·
                  refine ⟨6098899564752978278842753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8131866086337304371790337 6098899564752978278842753)
                  ·
                    refine ⟨4574174673564733709132065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6098899564752978278842753 4574174673564733709132065)
                    ·
                      refine ⟨3430631005173550281849049, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4574174673564733709132065 3430631005173550281849049)
                      ·
                        rfl

theorem cell23_6681130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 3, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 3, 3, 1, 2, 2, 2].length) (baseStart_6681130 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6681130 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6681130 prefixEnd_6681130 := by exact prefixLift 6681130
  have htrace : WordTrace (prefixWord ++ tailWord_6681130) baseStart_6681130 baseEnd_6681130 := by
    simpa [prefixWord, tailWord_6681130, baseEnd_6681130] using wordTrace_append hprefix tailTrace_6681130
  have hstable : (prefixWord ++ tailWord_6681130).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6681130).length < 2 ^ (prefixWord ++ tailWord_6681130).sum := by decide
  have hdescent : baseEnd_6681130 < baseStart_6681130 := by decide
  rcases family_descends (prefixWord ++ tailWord_6681130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6681152 : List Nat := [2, 1, 1, 2, 2, 2, 4, 1, 1, 3, 4]
def baseStart_6681152 : Nat := 118140960795 + 6681152 * 2 ^ 59
def prefixEnd_6681152 : Nat := 4983230072969 + 3 ^ 40 * 6681152 * 2
def baseEnd_6681152 : Nat := 3430642301747949195773947

theorem tailTrace_6681152 : CollatzResearch.WordTrace tailWord_6681152 prefixEnd_6681152 3430642301747949195773947 := by
  unfold tailWord_6681152
  simp only [CollatzResearch.WordTrace]
  refine ⟨121840816345667414381542855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 162454421794223219175390473 121840816345667414381542855)
  ·
    refine ⟨182761224518501121572314283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121840816345667414381542855 182761224518501121572314283)
    ·
      refine ⟨274141836777751682358471425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 182761224518501121572314283 274141836777751682358471425)
      ·
        refine ⟨205606377583313761768853569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 274141836777751682358471425 205606377583313761768853569)
        ·
          refine ⟨154204783187485321326640177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 205606377583313761768853569 154204783187485321326640177)
          ·
            refine ⟨115653587390613990994980133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 154204783187485321326640177 115653587390613990994980133)
            ·
              refine ⟨21685047635740123311558775, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 115653587390613990994980133 21685047635740123311558775)
              ·
                refine ⟨32527571453610184967338163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21685047635740123311558775 32527571453610184967338163)
                ·
                  refine ⟨48791357180415277451007245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32527571453610184967338163 48791357180415277451007245)
                  ·
                    refine ⟨18296758942655729044127717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 48791357180415277451007245 18296758942655729044127717)
                    ·
                      refine ⟨3430642301747949195773947, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18296758942655729044127717 3430642301747949195773947)
                      ·
                        rfl

theorem cell23_6681152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 4, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 4, 1, 1, 3, 4].length) (baseStart_6681152 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6681152 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6681152 prefixEnd_6681152 := by exact prefixLift 6681152
  have htrace : WordTrace (prefixWord ++ tailWord_6681152) baseStart_6681152 baseEnd_6681152 := by
    simpa [prefixWord, tailWord_6681152, baseEnd_6681152] using wordTrace_append hprefix tailTrace_6681152
  have hstable : (prefixWord ++ tailWord_6681152).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6681152).length < 2 ^ (prefixWord ++ tailWord_6681152).sum := by decide
  have hdescent : baseEnd_6681152 < baseStart_6681152 := by decide
  rcases family_descends (prefixWord ++ tailWord_6681152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6681169 : List Nat := [1, 2, 2, 1, 3, 4, 1, 2, 2, 1, 4]
def baseStart_6681169 : Nat := 118140960795 + 6681169 * 2 ^ 59
def prefixEnd_6681169 : Nat := 4983230072969 + 3 ^ 40 * 6681169 * 2
def baseEnd_6681169 : Nat := 3430651030919075629261369

theorem tailTrace_6681169 : CollatzResearch.WordTrace tailWord_6681169 prefixEnd_6681169 3430651030919075629261369 := by
  unfold tailWord_6681169
  simp only [CollatzResearch.WordTrace]
  refine ⟨243682252732273240666454561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162454835154848827110969707 243682252732273240666454561)
  ·
    refine ⟨182761689549204930499840921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 243682252732273240666454561 182761689549204930499840921)
    ·
      refine ⟨137071267161903697874880691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 182761689549204930499840921 137071267161903697874880691)
      ·
        refine ⟨205606900742855546812321037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 137071267161903697874880691 205606900742855546812321037)
        ·
          refine ⟨77102587778570830054620389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 205606900742855546812321037 77102587778570830054620389)
          ·
            refine ⟨14456735208482030635241323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 77102587778570830054620389 14456735208482030635241323)
            ·
              refine ⟨21685102812723045952861985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14456735208482030635241323 21685102812723045952861985)
              ·
                refine ⟨16263827109542284464646489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21685102812723045952861985 16263827109542284464646489)
                ·
                  refine ⟨12197870332156713348484867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16263827109542284464646489 12197870332156713348484867)
                  ·
                    refine ⟨18296805498235070022727301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12197870332156713348484867 18296805498235070022727301)
                    ·
                      refine ⟨3430651030919075629261369, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18296805498235070022727301 3430651030919075629261369)
                      ·
                        rfl

theorem cell23_6681169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 4, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 4, 1, 2, 2, 1, 4].length) (baseStart_6681169 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6681169 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6681169 prefixEnd_6681169 := by exact prefixLift 6681169
  have htrace : WordTrace (prefixWord ++ tailWord_6681169) baseStart_6681169 baseEnd_6681169 := by
    simpa [prefixWord, tailWord_6681169, baseEnd_6681169] using wordTrace_append hprefix tailTrace_6681169
  have hstable : (prefixWord ++ tailWord_6681169).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6681169).length < 2 ^ (prefixWord ++ tailWord_6681169).sum := by decide
  have hdescent : baseEnd_6681169 < baseStart_6681169 := by decide
  rcases family_descends (prefixWord ++ tailWord_6681169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6681226 : List Nat := [3, 1, 2, 3, 3, 1, 2, 2, 6]
def baseStart_6681226 : Nat := 118140960795 + 6681226 * 2 ^ 59
def prefixEnd_6681226 : Nat := 4983230072969 + 3 ^ 40 * 6681226 * 2
def baseEnd_6681226 : Nat := 381186699924042434027623

theorem tailTrace_6681226 : CollatzResearch.WordTrace tailWord_6681226 prefixEnd_6681226 381186699924042434027623 := by
  unfold tailWord_6681226
  simp only [CollatzResearch.WordTrace]
  refine ⟨60921082923266684850319883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 162456221128711159600853021 60921082923266684850319883)
  ·
    refine ⟨91381624384900027275479825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60921082923266684850319883 91381624384900027275479825)
    ·
      refine ⟨68536218288675020456609869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 91381624384900027275479825 68536218288675020456609869)
      ·
        refine ⟨25701081858253132671228701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 68536218288675020456609869 25701081858253132671228701)
        ·
          refine ⟨9637905696844924751710763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25701081858253132671228701 9637905696844924751710763)
          ·
            refine ⟨14456858545267387127566145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9637905696844924751710763 14456858545267387127566145)
            ·
              refine ⟨10842643908950540345674609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14456858545267387127566145 10842643908950540345674609)
              ·
                refine ⟨8131982931712905259255957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10842643908950540345674609 8131982931712905259255957)
                ·
                  refine ⟨381186699924042434027623, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8131982931712905259255957 381186699924042434027623)
                  ·
                    rfl

theorem cell23_6681226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 3, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 3, 1, 2, 2, 6].length) (baseStart_6681226 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6681226 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6681226 prefixEnd_6681226 := by exact prefixLift 6681226
  have htrace : WordTrace (prefixWord ++ tailWord_6681226) baseStart_6681226 baseEnd_6681226 := by
    simpa [prefixWord, tailWord_6681226, baseEnd_6681226] using wordTrace_append hprefix tailTrace_6681226
  have hstable : (prefixWord ++ tailWord_6681226).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6681226).length < 2 ^ (prefixWord ++ tailWord_6681226).sum := by decide
  have hdescent : baseEnd_6681226 < baseStart_6681226 := by decide
  rcases family_descends (prefixWord ++ tailWord_6681226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6681263 : List Nat := [1, 1, 2, 1, 2, 7, 1, 1, 2, 3, 2]
def baseStart_6681263 : Nat := 118140960795 + 6681263 * 2 ^ 59
def prefixEnd_6681263 : Nat := 4983230072969 + 3 ^ 40 * 6681263 * 2
def baseEnd_6681263 : Nat := 3430699298100598261485937

theorem tailTrace_6681263 : CollatzResearch.WordTrace tailWord_6681263 prefixEnd_6681263 3430699298100598261485937 := by
  unfold tailWord_6681263
  simp only [CollatzResearch.WordTrace]
  refine ⟨243685681193932694720376443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162457120795955129813584295 243685681193932694720376443)
  ·
    refine ⟨365528521790899042080564665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 243685681193932694720376443 365528521790899042080564665)
    ·
      refine ⟨274146391343174281560423499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 365528521790899042080564665 274146391343174281560423499)
      ·
        refine ⟨411219587014761422340635249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 274146391343174281560423499 411219587014761422340635249)
        ·
          refine ⟨308414690261071066755476437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 411219587014761422340635249 308414690261071066755476437)
          ·
            refine ⟨7228469302993853127081479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 308414690261071066755476437 7228469302993853127081479)
            ·
              refine ⟨10842703954490779690622219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7228469302993853127081479 10842703954490779690622219)
              ·
                refine ⟨16264055931736169535933329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10842703954490779690622219 16264055931736169535933329)
                ·
                  refine ⟨12198041948802127151949997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16264055931736169535933329 12198041948802127151949997)
                  ·
                    refine ⟨4574265730800797681981249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12198041948802127151949997 4574265730800797681981249)
                    ·
                      refine ⟨3430699298100598261485937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4574265730800797681981249 3430699298100598261485937)
                      ·
                        rfl

theorem cell23_6681263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 7, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 7, 1, 1, 2, 3, 2].length) (baseStart_6681263 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6681263 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6681263 prefixEnd_6681263 := by exact prefixLift 6681263
  have htrace : WordTrace (prefixWord ++ tailWord_6681263) baseStart_6681263 baseEnd_6681263 := by
    simpa [prefixWord, tailWord_6681263, baseEnd_6681263] using wordTrace_append hprefix tailTrace_6681263
  have hstable : (prefixWord ++ tailWord_6681263).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6681263).length < 2 ^ (prefixWord ++ tailWord_6681263).sum := by decide
  have hdescent : baseEnd_6681263 < baseStart_6681263 := by decide
  rcases family_descends (prefixWord ++ tailWord_6681263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6681272 : List Nat := [2, 1, 2, 1, 2, 1, 1, 1, 5, 1, 6]
def baseStart_6681272 : Nat := 118140960795 + 6681272 * 2 ^ 59
def prefixEnd_6681272 : Nat := 4983230072969 + 3 ^ 40 * 6681272 * 2
def baseEnd_6681272 : Nat := 3430703919426488726273395

theorem tailTrace_6681272 : CollatzResearch.WordTrace tailWord_6681272 prefixEnd_6681272 3430703919426488726273395 := by
  unfold tailWord_6681272
  simp only [CollatzResearch.WordTrace]
  refine ⟨121843004725450044628727035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 162457339633933392838302713 121843004725450044628727035)
  ·
    refine ⟨182764507088175066943090553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121843004725450044628727035 182764507088175066943090553)
    ·
      refine ⟨137073380316131300207317915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 182764507088175066943090553 137073380316131300207317915)
      ·
        refine ⟨205610070474196950310976873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 137073380316131300207317915 205610070474196950310976873)
        ·
          refine ⟨154207552855647712733232655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 205610070474196950310976873 154207552855647712733232655)
          ·
            refine ⟨231311329283471569099848983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 154207552855647712733232655 231311329283471569099848983)
            ·
              refine ⟨346966993925207353649773475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 231311329283471569099848983 346966993925207353649773475)
              ·
                refine ⟨520450490887811030474660213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 346966993925207353649773475 520450490887811030474660213)
                ·
                  refine ⟨48792233520732284106999395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 520450490887811030474660213 48792233520732284106999395)
                  ·
                    refine ⟨73188350281098426160499093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 48792233520732284106999395 73188350281098426160499093)
                    ·
                      refine ⟨3430703919426488726273395, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 73188350281098426160499093 3430703919426488726273395)
                      ·
                        rfl

theorem cell23_6681272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 1, 5, 1, 6].length) (baseStart_6681272 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6681272 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6681272 prefixEnd_6681272 := by exact prefixLift 6681272
  have htrace : WordTrace (prefixWord ++ tailWord_6681272) baseStart_6681272 baseEnd_6681272 := by
    simpa [prefixWord, tailWord_6681272, baseEnd_6681272] using wordTrace_append hprefix tailTrace_6681272
  have hstable : (prefixWord ++ tailWord_6681272).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6681272).length < 2 ^ (prefixWord ++ tailWord_6681272).sum := by decide
  have hdescent : baseEnd_6681272 < baseStart_6681272 := by decide
  rcases family_descends (prefixWord ++ tailWord_6681272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6681276 : List Nat := [2, 2, 2, 3, 1, 1, 3, 3, 1, 1, 4]
def baseStart_6681276 : Nat := 118140960795 + 6681276 * 2 ^ 59
def prefixEnd_6681276 : Nat := 4983230072969 + 3 ^ 40 * 6681276 * 2
def baseEnd_6681276 : Nat := 3430705973349106710623377

theorem tailTrace_6681276 : CollatzResearch.WordTrace tailWord_6681276 prefixEnd_6681276 3430705973349106710623377 := by
  unfold tailWord_6681276
  simp only [CollatzResearch.WordTrace]
  refine ⟨121843077671442798970299841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 162457436895257065293733121 121843077671442798970299841)
  ·
    refine ⟨91382308253582099227724881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 121843077671442798970299841 91382308253582099227724881)
    ·
      refine ⟨68536731190186574420793661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 91382308253582099227724881 68536731190186574420793661)
      ·
        refine ⟨25701274196319965407797623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 68536731190186574420793661 25701274196319965407797623)
        ·
          refine ⟨38551911294479948111696435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25701274196319965407797623 38551911294479948111696435)
          ·
            refine ⟨57827866941719922167544653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38551911294479948111696435 57827866941719922167544653)
            ·
              refine ⟨21685450103144970812829245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 57827866941719922167544653 21685450103144970812829245)
              ·
                refine ⟨8132043788679364054810967, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21685450103144970812829245 8132043788679364054810967)
                ·
                  refine ⟨12198065683019046082216451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8132043788679364054810967 12198065683019046082216451)
                  ·
                    refine ⟨18297098524528569123324677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12198065683019046082216451 18297098524528569123324677)
                    ·
                      refine ⟨3430705973349106710623377, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18297098524528569123324677 3430705973349106710623377)
                      ·
                        rfl

theorem cell23_6681276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 3, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 3, 3, 1, 1, 4].length) (baseStart_6681276 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6681276 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6681276 prefixEnd_6681276 := by exact prefixLift 6681276
  have htrace : WordTrace (prefixWord ++ tailWord_6681276) baseStart_6681276 baseEnd_6681276 := by
    simpa [prefixWord, tailWord_6681276, baseEnd_6681276] using wordTrace_append hprefix tailTrace_6681276
  have hstable : (prefixWord ++ tailWord_6681276).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6681276).length < 2 ^ (prefixWord ++ tailWord_6681276).sum := by decide
  have hdescent : baseEnd_6681276 < baseStart_6681276 := by decide
  rcases family_descends (prefixWord ++ tailWord_6681276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6681303 : List Nat := [1, 1, 3, 2, 1, 5, 3, 1, 2, 4]
def baseStart_6681303 : Nat := 118140960795 + 6681303 * 2 ^ 59
def prefixEnd_6681303 : Nat := 4983230072969 + 3 ^ 40 * 6681303 * 2
def baseEnd_6681303 : Nat := 1143573279108926034995251

theorem tailTrace_6681303 : CollatzResearch.WordTrace tailWord_6681303 prefixEnd_6681303 1143573279108926034995251 := by
  unfold tailWord_6681303
  simp only [CollatzResearch.WordTrace]
  refine ⟨243687140113787781551832563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162458093409191854367888375 243687140113787781551832563)
  ·
    refine ⟨365530710170681672327748845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 243687140113787781551832563 365530710170681672327748845)
    ·
      refine ⟨137074016314005627122905817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 365530710170681672327748845 137074016314005627122905817)
      ·
        refine ⟨102805512235504220342179363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 137074016314005627122905817 102805512235504220342179363)
        ·
          refine ⟨154208268353256330513269045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 102805512235504220342179363 154208268353256330513269045)
          ·
            refine ⟨14457025158117780985618973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 154208268353256330513269045 14457025158117780985618973)
            ·
              refine ⟨5421384434294167869607115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14457025158117780985618973 5421384434294167869607115)
              ·
                refine ⟨8132076651441251804410673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5421384434294167869607115 8132076651441251804410673)
                ·
                  refine ⟨6099057488580938853308005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8132076651441251804410673 6099057488580938853308005)
                  ·
                    refine ⟨1143573279108926034995251, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6099057488580938853308005 1143573279108926034995251)
                    ·
                      rfl

theorem cell23_6681303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 5, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 5, 3, 1, 2, 4].length) (baseStart_6681303 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6681303 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6681303 prefixEnd_6681303 := by exact prefixLift 6681303
  have htrace : WordTrace (prefixWord ++ tailWord_6681303) baseStart_6681303 baseEnd_6681303 := by
    simpa [prefixWord, tailWord_6681303, baseEnd_6681303] using wordTrace_append hprefix tailTrace_6681303
  have hstable : (prefixWord ++ tailWord_6681303).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6681303).length < 2 ^ (prefixWord ++ tailWord_6681303).sum := by decide
  have hdescent : baseEnd_6681303 < baseStart_6681303 := by decide
  rcases family_descends (prefixWord ++ tailWord_6681303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6681313 : List Nat := [1, 2, 3, 1, 4, 2, 2, 2, 1, 2, 3]
def baseStart_6681313 : Nat := 118140960795 + 6681313 * 2 ^ 59
def prefixEnd_6681313 : Nat := 4983230072969 + 3 ^ 40 * 6681313 * 2
def baseEnd_6681313 : Nat := 3430724972133323065860707

theorem tailTrace_6681313 : CollatzResearch.WordTrace tailWord_6681313 prefixEnd_6681313 3430724972133323065860707 := by
  unfold tailWord_6681313
  simp only [CollatzResearch.WordTrace]
  refine ⟨243687504843751553259696593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162458336562501035506464395 243687504843751553259696593)
  ·
    refine ⟨182765628632813664944772445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 243687504843751553259696593 182765628632813664944772445)
    ·
      refine ⟨68537110737305124354289667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 182765628632813664944772445 68537110737305124354289667)
      ·
        refine ⟨102805666105957686531434501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68537110737305124354289667 102805666105957686531434501)
        ·
          refine ⟨19276062394867066224643969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 102805666105957686531434501 19276062394867066224643969)
          ·
            refine ⟨14457046796150299668482977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19276062394867066224643969 14457046796150299668482977)
            ·
              refine ⟨10842785097112724751362233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14457046796150299668482977 10842785097112724751362233)
              ·
                refine ⟨8132088822834543563521675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10842785097112724751362233 8132088822834543563521675)
                ·
                  refine ⟨12198133234251815345282513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8132088822834543563521675 12198133234251815345282513)
                  ·
                    refine ⟨9148599925688861508961885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12198133234251815345282513 9148599925688861508961885)
                    ·
                      refine ⟨3430724972133323065860707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9148599925688861508961885 3430724972133323065860707)
                      ·
                        rfl

theorem cell23_6681313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 2, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 2, 2, 2, 1, 2, 3].length) (baseStart_6681313 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6681313 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6681313 prefixEnd_6681313 := by exact prefixLift 6681313
  have htrace : WordTrace (prefixWord ++ tailWord_6681313) baseStart_6681313 baseEnd_6681313 := by
    simpa [prefixWord, tailWord_6681313, baseEnd_6681313] using wordTrace_append hprefix tailTrace_6681313
  have hstable : (prefixWord ++ tailWord_6681313).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6681313).length < 2 ^ (prefixWord ++ tailWord_6681313).sum := by decide
  have hdescent : baseEnd_6681313 < baseStart_6681313 := by decide
  rcases family_descends (prefixWord ++ tailWord_6681313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
