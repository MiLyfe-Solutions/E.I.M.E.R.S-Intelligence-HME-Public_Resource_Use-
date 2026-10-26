import V185TrunkScan20Chunk052

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental

namespace V185TrunkScan20Incremental

def tailWord_322730 : List Nat := [3, 1, 5, 1, 1, 9]
def baseStart_322730 : Nat := 118140960795 + 322730 * 2 ^ 59
def prefixEnd_322730 : Nat := 4983230072969 + 3 ^ 40 * 322730 * 2
def baseEnd_322730 : Nat := 5455657995905433780767

theorem tailTrace_322730 : CollatzResearch.WordTrace tailWord_322730 prefixEnd_322730 5455657995905433780767 := by
  unfold tailWord_322730
  simp only [CollatzResearch.WordTrace]
  refine ⟨2942732530202950685237411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7847286747207868493966429 2942732530202950685237411)
  ·
    refine ⟨4414098795304426027856117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2942732530202950685237411 4414098795304426027856117)
    ·
      refine ⟨413821762059789940111511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 4414098795304426027856117 413821762059789940111511)
      ·
        refine ⟨620732643089684910167267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 413821762059789940111511 620732643089684910167267)
        ·
          refine ⟨931098964634527365250901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 620732643089684910167267 931098964634527365250901)
          ·
            refine ⟨5455657995905433780767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 931098964634527365250901 5455657995905433780767)
            ·
              rfl

theorem cell20_322730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 9].length) (baseStart_322730 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_322730 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_322730 prefixEnd_322730 := by exact prefixLift 322730
  have htrace : WordTrace (prefixWord ++ tailWord_322730) baseStart_322730 baseEnd_322730 := by
    simpa [prefixWord, tailWord_322730, baseEnd_322730] using wordTrace_append hprefix tailTrace_322730
  have hstable : (prefixWord ++ tailWord_322730).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_322730).length < 2 ^ (prefixWord ++ tailWord_322730).sum := by decide
  have hdescent : baseEnd_322730 < baseStart_322730 := by decide
  rcases family_descends (prefixWord ++ tailWord_322730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_322733 : List Nat := [1, 5, 2, 1, 3, 1, 2, 2, 3]
def baseStart_322733 : Nat := 118140960795 + 322733 * 2 ^ 59
def prefixEnd_322733 : Nat := 4983230072969 + 3 ^ 40 * 322733 * 2
def baseEnd_322733 : Nat := 147304135171192034980697

theorem tailTrace_322733 : CollatzResearch.WordTrace tailWord_322733 prefixEnd_322733 147304135171192034980697 := by
  unfold tailWord_322733
  simp only [CollatzResearch.WordTrace]
  refine ⟨11771039539800934253308853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7847359693200622835539235 11771039539800934253308853)
  ·
    refine ⟨1103534956856337586247705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 11771039539800934253308853 1103534956856337586247705)
    ·
      refine ⟨827651217642253189685779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1103534956856337586247705 827651217642253189685779)
      ·
        refine ⟨1241476826463379784528669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 827651217642253189685779 1241476826463379784528669)
        ·
          refine ⟨465553809923767419198251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1241476826463379784528669 465553809923767419198251)
          ·
            refine ⟨698330714885651128797377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 465553809923767419198251 698330714885651128797377)
            ·
              refine ⟨523748036164238346598033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 698330714885651128797377 523748036164238346598033)
              ·
                refine ⟨392811027123178759948525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 523748036164238346598033 392811027123178759948525)
                ·
                  refine ⟨147304135171192034980697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 392811027123178759948525 147304135171192034980697)
                  ·
                    rfl

theorem cell20_322733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 3, 1, 2, 2, 3].length) (baseStart_322733 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_322733 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_322733 prefixEnd_322733 := by exact prefixLift 322733
  have htrace : WordTrace (prefixWord ++ tailWord_322733) baseStart_322733 baseEnd_322733 := by
    simpa [prefixWord, tailWord_322733, baseEnd_322733] using wordTrace_append hprefix tailTrace_322733
  have hstable : (prefixWord ++ tailWord_322733).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_322733).length < 2 ^ (prefixWord ++ tailWord_322733).sum := by decide
  have hdescent : baseEnd_322733 < baseStart_322733 := by decide
  rcases family_descends (prefixWord ++ tailWord_322733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_322751 : List Nat := [1, 1, 2, 2, 2, 2, 5, 5]
def baseStart_322751 : Nat := 118140960795 + 322751 * 2 ^ 59
def prefixEnd_322751 : Nat := 4983230072969 + 3 ^ 40 * 322751 * 2
def baseEnd_322751 : Nat := 49104116953887990793541

theorem tailTrace_322751 : CollatzResearch.WordTrace tailWord_322751 prefixEnd_322751 49104116953887990793541 := by
  unfold tailWord_322751
  simp only [CollatzResearch.WordTrace]
  refine ⟨11771696053735723327464107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7847797369157148884976071 11771696053735723327464107)
  ·
    refine ⟨17657544080603584991196161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11771696053735723327464107 17657544080603584991196161)
    ·
      refine ⟨13243158060452688743397121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17657544080603584991196161 13243158060452688743397121)
      ·
        refine ⟨9932368545339516557547841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13243158060452688743397121 9932368545339516557547841)
        ·
          refine ⟨7449276409004637418160881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9932368545339516557547841 7449276409004637418160881)
          ·
            refine ⟨5586957306753478063620661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7449276409004637418160881 5586957306753478063620661)
            ·
              refine ⟨523777247508138568464437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 5586957306753478063620661 523777247508138568464437)
              ·
                refine ⟨49104116953887990793541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 523777247508138568464437 49104116953887990793541)
                ·
                  rfl

theorem cell20_322751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 5, 5].length) (baseStart_322751 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_322751 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_322751 prefixEnd_322751 := by exact prefixLift 322751
  have htrace : WordTrace (prefixWord ++ tailWord_322751) baseStart_322751 baseEnd_322751 := by
    simpa [prefixWord, tailWord_322751, baseEnd_322751] using wordTrace_append hprefix tailTrace_322751
  have hstable : (prefixWord ++ tailWord_322751).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_322751).length < 2 ^ (prefixWord ++ tailWord_322751).sum := by decide
  have hdescent : baseEnd_322751 < baseStart_322751 := by decide
  rcases family_descends (prefixWord ++ tailWord_322751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_322774 : List Nat := [5, 2, 1, 2, 2, 1, 2, 3, 2]
def baseStart_322774 : Nat := 118140960795 + 322774 * 2 ^ 59
def prefixEnd_322774 : Nat := 4983230072969 + 3 ^ 40 * 322774 * 2
def baseEnd_322774 : Nat := 147322848688378114613863

theorem tailTrace_322774 : CollatzResearch.WordTrace tailWord_322774 prefixEnd_322774 147322848688378114613863 := by
  unfold tailWord_322774
  simp only [CollatzResearch.WordTrace]
  refine ⟨735783433290774890971961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 7848356621768265503700917 735783433290774890971961)
  ·
    refine ⟨551837574968081168228971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 735783433290774890971961 551837574968081168228971)
    ·
      refine ⟨827756362452121752343457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 551837574968081168228971 827756362452121752343457)
      ·
        refine ⟨620817271839091314257593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 827756362452121752343457 620817271839091314257593)
        ·
          refine ⟨465612953879318485693195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 620817271839091314257593 465612953879318485693195)
          ·
            refine ⟨698419430818977728539793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 465612953879318485693195 698419430818977728539793)
            ·
              refine ⟨523814573114233296404845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 698419430818977728539793 523814573114233296404845)
              ·
                refine ⟨196430464917837486151817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 523814573114233296404845 196430464917837486151817)
                ·
                  refine ⟨147322848688378114613863, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 196430464917837486151817 147322848688378114613863)
                  ·
                    rfl

theorem cell20_322774_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 2, 1, 2, 3, 2].length) (baseStart_322774 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_322774 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_322774 prefixEnd_322774 := by exact prefixLift 322774
  have htrace : WordTrace (prefixWord ++ tailWord_322774) baseStart_322774 baseEnd_322774 := by
    simpa [prefixWord, tailWord_322774, baseEnd_322774] using wordTrace_append hprefix tailTrace_322774
  have hstable : (prefixWord ++ tailWord_322774).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_322774).length < 2 ^ (prefixWord ++ tailWord_322774).sum := by decide
  have hdescent : baseEnd_322774 < baseStart_322774 := by decide
  rcases family_descends (prefixWord ++ tailWord_322774) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_322799 : List Nat := [1, 1, 2, 1, 7, 1, 2, 1, 4]
def baseStart_322799 : Nat := 118140960795 + 322799 * 2 ^ 59
def prefixEnd_322799 : Nat := 4983230072969 + 3 ^ 40 * 322799 * 2
def baseEnd_322799 : Nat := 147334259369589138780427

theorem tailTrace_322799 : CollatzResearch.WordTrace tailWord_322799 prefixEnd_322799 147334259369589138780427 := by
  unfold tailWord_322799
  simp only [CollatzResearch.WordTrace]
  refine ⟨11773446757561827525211451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7848964505041218350140967 11773446757561827525211451)
  ·
    refine ⟨17660170136342741287817177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11773446757561827525211451 17660170136342741287817177)
    ·
      refine ⟨13245127602257055965862883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17660170136342741287817177 13245127602257055965862883)
      ·
        refine ⟨19867691403385583948794325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13245127602257055965862883 19867691403385583948794325)
        ·
          refine ⟨465649017266849623799867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 19867691403385583948794325 465649017266849623799867)
          ·
            refine ⟨698473525900274435699801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 465649017266849623799867 698473525900274435699801)
            ·
              refine ⟨523855144425205826774851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 698473525900274435699801 523855144425205826774851)
              ·
                refine ⟨785782716637808740162277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 523855144425205826774851 785782716637808740162277)
                ·
                  refine ⟨147334259369589138780427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 785782716637808740162277 147334259369589138780427)
                  ·
                    rfl

theorem cell20_322799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 7, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 7, 1, 2, 1, 4].length) (baseStart_322799 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_322799 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_322799 prefixEnd_322799 := by exact prefixLift 322799
  have htrace : WordTrace (prefixWord ++ tailWord_322799) baseStart_322799 baseEnd_322799 := by
    simpa [prefixWord, tailWord_322799, baseEnd_322799] using wordTrace_append hprefix tailTrace_322799
  have hstable : (prefixWord ++ tailWord_322799).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_322799).length < 2 ^ (prefixWord ++ tailWord_322799).sum := by decide
  have hdescent : baseEnd_322799 < baseStart_322799 := by decide
  rcases family_descends (prefixWord ++ tailWord_322799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_322827 : List Nat := [1, 1, 1, 1, 5, 4, 1, 6]
def baseStart_322827 : Nat := 118140960795 + 322827 * 2 ^ 59
def prefixEnd_322827 : Nat := 4983230072969 + 3 ^ 40 * 322827 * 2
def baseEnd_322827 : Nat := 49115679777515161948993

theorem tailTrace_322827 : CollatzResearch.WordTrace tailWord_322827 prefixEnd_322827 49115679777515161948993 := by
  unfold tailWord_322827
  simp only [CollatzResearch.WordTrace]
  refine ⟨11774468001460388307230735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7849645334306925538153823 11774468001460388307230735)
  ·
    refine ⟨17661702002190582460846103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11774468001460388307230735 17661702002190582460846103)
    ·
      refine ⟨26492553003285873691269155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17661702002190582460846103 26492553003285873691269155)
      ·
        refine ⟨39738829504928810536903733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26492553003285873691269155 39738829504928810536903733)
        ·
          refine ⟨3725515266087075987834725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 39738829504928810536903733 3725515266087075987834725)
          ·
            refine ⟨698534112391326747719011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3725515266087075987834725 698534112391326747719011)
            ·
              refine ⟨1047801168586990121578517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 698534112391326747719011 1047801168586990121578517)
              ·
                refine ⟨49115679777515161948993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1047801168586990121578517 49115679777515161948993)
                ·
                  rfl

theorem cell20_322827_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 4, 1, 6].length) (baseStart_322827 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_322827 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_322827 prefixEnd_322827 := by exact prefixLift 322827
  have htrace : WordTrace (prefixWord ++ tailWord_322827) baseStart_322827 baseEnd_322827 := by
    simpa [prefixWord, tailWord_322827, baseEnd_322827] using wordTrace_append hprefix tailTrace_322827
  have hstable : (prefixWord ++ tailWord_322827).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_322827).length < 2 ^ (prefixWord ++ tailWord_322827).sum := by decide
  have hdescent : baseEnd_322827 < baseStart_322827 := by decide
  rcases family_descends (prefixWord ++ tailWord_322827) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_322861 : List Nat := [1, 5, 3, 1, 1, 2, 2, 5]
def baseStart_322861 : Nat := 118140960795 + 322861 * 2 ^ 59
def prefixEnd_322861 : Nat := 4983230072969 + 3 ^ 40 * 322861 * 2
def baseEnd_322861 : Nat := 49120852619664159571169

theorem tailTrace_322861 : CollatzResearch.WordTrace tailWord_322861 prefixEnd_322861 49120852619664159571169 := by
  unfold tailWord_322861
  simp only [CollatzResearch.WordTrace]
  refine ⟨11775708083337212113968437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7850472055558141409312291 11775708083337212113968437)
  ·
    refine ⟨1103972632812863635684541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 11775708083337212113968437 1103972632812863635684541)
    ·
      refine ⟨413989737304823863381703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1103972632812863635684541 413989737304823863381703)
      ·
        refine ⟨620984605957235795072555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 413989737304823863381703 620984605957235795072555)
        ·
          refine ⟨931476908935853692608833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 620984605957235795072555 931476908935853692608833)
          ·
            refine ⟨698607681701890269456625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 931476908935853692608833 698607681701890269456625)
            ·
              refine ⟨523955761276417702092469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 698607681701890269456625 523955761276417702092469)
              ·
                refine ⟨49120852619664159571169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 523955761276417702092469 49120852619664159571169)
                ·
                  rfl

theorem cell20_322861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 2, 2, 5].length) (baseStart_322861 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_322861 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_322861 prefixEnd_322861 := by exact prefixLift 322861
  have htrace : WordTrace (prefixWord ++ tailWord_322861) baseStart_322861 baseEnd_322861 := by
    simpa [prefixWord, tailWord_322861, baseEnd_322861] using wordTrace_append hprefix tailTrace_322861
  have hstable : (prefixWord ++ tailWord_322861).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_322861).length < 2 ^ (prefixWord ++ tailWord_322861).sum := by decide
  have hdescent : baseEnd_322861 < baseStart_322861 := by decide
  rcases family_descends (prefixWord ++ tailWord_322861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_322865 : List Nat := [1, 2, 2, 3, 3, 1, 1, 7]
def baseStart_322865 : Nat := 118140960795 + 322865 * 2 ^ 59
def prefixEnd_322865 : Nat := 4983230072969 + 3 ^ 40 * 322865 * 2
def baseEnd_322865 : Nat := 49121461189328747526719

theorem tailTrace_322865 : CollatzResearch.WordTrace tailWord_322865 prefixEnd_322865 49121461189328747526719 := by
  unfold tailWord_322865
  simp only [CollatzResearch.WordTrace]
  refine ⟨11775853975322720797114049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7850569316881813864742699 11775853975322720797114049)
  ·
    refine ⟨8831890481492040597835537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11775853975322720797114049 8831890481492040597835537)
    ·
      refine ⟨6623917861119030448376653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8831890481492040597835537 6623917861119030448376653)
      ·
        refine ⟨2483969197919636418141245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6623917861119030448376653 2483969197919636418141245)
        ·
          refine ⟨931488449219863656802967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2483969197919636418141245 931488449219863656802967)
          ·
            refine ⟨1397232673829795485204451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 931488449219863656802967 1397232673829795485204451)
            ·
              refine ⟨2095849010744693227806677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1397232673829795485204451 2095849010744693227806677)
              ·
                refine ⟨49121461189328747526719, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2095849010744693227806677 49121461189328747526719)
                ·
                  rfl

theorem cell20_322865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 1, 7].length) (baseStart_322865 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_322865 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_322865 prefixEnd_322865 := by exact prefixLift 322865
  have htrace : WordTrace (prefixWord ++ tailWord_322865) baseStart_322865 baseEnd_322865 := by
    simpa [prefixWord, tailWord_322865, baseEnd_322865] using wordTrace_append hprefix tailTrace_322865
  have hstable : (prefixWord ++ tailWord_322865).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_322865).length < 2 ^ (prefixWord ++ tailWord_322865).sum := by decide
  have hdescent : baseEnd_322865 < baseStart_322865 := by decide
  rcases family_descends (prefixWord ++ tailWord_322865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_322868 : List Nat := [2, 5, 1, 1, 1, 1, 3, 3, 3]
def baseStart_322868 : Nat := 118140960795 + 322868 * 2 ^ 59
def prefixEnd_322868 : Nat := 4983230072969 + 3 ^ 40 * 322868 * 2
def baseEnd_322868 : Nat := 147365752849731565480145

theorem tailTrace_322868 : CollatzResearch.WordTrace tailWord_322868 prefixEnd_322868 147365752849731565480145 := by
  unfold tailWord_322868
  simp only [CollatzResearch.WordTrace]
  refine ⟨5887981697155926154736629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7850642262874568206315505 5887981697155926154736629)
  ·
    refine ⟨551998284108368077006559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 5887981697155926154736629 551998284108368077006559)
    ·
      refine ⟨827997426162552115509839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 551998284108368077006559 827997426162552115509839)
      ·
        refine ⟨1241996139243828173264759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 827997426162552115509839 1241996139243828173264759)
        ·
          refine ⟨1862994208865742259897139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1241996139243828173264759 1862994208865742259897139)
          ·
            refine ⟨2794491313298613389845709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1862994208865742259897139 2794491313298613389845709)
            ·
              refine ⟨1047934242486980021192141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2794491313298613389845709 1047934242486980021192141)
              ·
                refine ⟨392975340932617507947053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1047934242486980021192141 392975340932617507947053)
                ·
                  refine ⟨147365752849731565480145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 392975340932617507947053 147365752849731565480145)
                  ·
                    rfl

theorem cell20_322868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 3, 3, 3].length) (baseStart_322868 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_322868 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_322868 prefixEnd_322868 := by exact prefixLift 322868
  have htrace : WordTrace (prefixWord ++ tailWord_322868) baseStart_322868 baseEnd_322868 := by
    simpa [prefixWord, tailWord_322868, baseEnd_322868] using wordTrace_append hprefix tailTrace_322868
  have hstable : (prefixWord ++ tailWord_322868).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_322868).length < 2 ^ (prefixWord ++ tailWord_322868).sum := by decide
  have hdescent : baseEnd_322868 < baseStart_322868 := by decide
  rcases family_descends (prefixWord ++ tailWord_322868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_322951 : List Nat := [1, 1, 4, 2, 2, 2, 1, 5, 2]
def baseStart_322951 : Nat := 118140960795 + 322951 * 2 ^ 59
def prefixEnd_322951 : Nat := 4983230072969 + 3 ^ 40 * 322951 * 2
def baseEnd_322951 : Nat := 147403636311352165713139

theorem tailTrace_322951 : CollatzResearch.WordTrace tailWord_322951 prefixEnd_322951 147403636311352165713139 := by
  unfold tailWord_322951
  simp only [CollatzResearch.WordTrace]
  refine ⟨11778990653011157484744707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7852660435340771656496471 11778990653011157484744707)
  ·
    refine ⟨17668485979516736227117061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11778990653011157484744707 17668485979516736227117061)
    ·
      refine ⟨3312841121159388042584449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 17668485979516736227117061 3312841121159388042584449)
      ·
        refine ⟨2484630840869541031938337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3312841121159388042584449 2484630840869541031938337)
        ·
          refine ⟨1863473130652155773953753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2484630840869541031938337 1863473130652155773953753)
          ·
            refine ⟨1397604847989116830465315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1863473130652155773953753 1397604847989116830465315)
            ·
              refine ⟨2096407271983675245697973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1397604847989116830465315 2096407271983675245697973)
              ·
                refine ⟨196538181748469554284185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2096407271983675245697973 196538181748469554284185)
                ·
                  refine ⟨147403636311352165713139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 196538181748469554284185 147403636311352165713139)
                  ·
                    rfl

theorem cell20_322951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 1, 5, 2].length) (baseStart_322951 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_322951 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_322951 prefixEnd_322951 := by exact prefixLift 322951
  have htrace : WordTrace (prefixWord ++ tailWord_322951) baseStart_322951 baseEnd_322951 := by
    simpa [prefixWord, tailWord_322951, baseEnd_322951] using wordTrace_append hprefix tailTrace_322951
  have hstable : (prefixWord ++ tailWord_322951).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_322951).length < 2 ^ (prefixWord ++ tailWord_322951).sum := by decide
  have hdescent : baseEnd_322951 < baseStart_322951 := by decide
  rcases family_descends (prefixWord ++ tailWord_322951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_322955 : List Nat := [1, 1, 1, 1, 4, 3, 1, 2, 6]
def baseStart_322955 : Nat := 118140960795 + 322955 * 2 ^ 59
def prefixEnd_322955 : Nat := 4983230072969 + 3 ^ 40 * 322955 * 2
def baseEnd_322955 : Nat := 147405462020345929579789

theorem tailTrace_322955 : CollatzResearch.WordTrace tailWord_322955 prefixEnd_322955 147405462020345929579789 := by
  unfold tailWord_322955
  simp only [CollatzResearch.WordTrace]
  refine ⟨11779136544996666167890319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7852757696664444111926879 11779136544996666167890319)
  ·
    refine ⟨17668704817494999251835479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11779136544996666167890319 17668704817494999251835479)
    ·
      refine ⟨26503057226242498877753219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17668704817494999251835479 26503057226242498877753219)
      ·
        refine ⟨39754585839363748316629829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26503057226242498877753219 39754585839363748316629829)
        ·
          refine ⟨7453984844880702809368093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 39754585839363748316629829 7453984844880702809368093)
          ·
            refine ⟨2795244316830263553513035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7453984844880702809368093 2795244316830263553513035)
            ·
              refine ⟨4192866475245395330269553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2795244316830263553513035 4192866475245395330269553)
              ·
                refine ⟨3144649856434046497702165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4192866475245395330269553 3144649856434046497702165)
                ·
                  refine ⟨147405462020345929579789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3144649856434046497702165 147405462020345929579789)
                  ·
                    rfl

theorem cell20_322955_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 1, 2, 6].length) (baseStart_322955 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_322955 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_322955 prefixEnd_322955 := by exact prefixLift 322955
  have htrace : WordTrace (prefixWord ++ tailWord_322955) baseStart_322955 baseEnd_322955 := by
    simpa [prefixWord, tailWord_322955, baseEnd_322955] using wordTrace_append hprefix tailTrace_322955
  have hstable : (prefixWord ++ tailWord_322955).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_322955).length < 2 ^ (prefixWord ++ tailWord_322955).sum := by decide
  have hdescent : baseEnd_322955 < baseStart_322955 := by decide
  rcases family_descends (prefixWord ++ tailWord_322955) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_322958 : List Nat := [4, 1, 1, 4, 2, 1, 7]
def baseStart_322958 : Nat := 118140960795 + 322958 * 2 ^ 59
def prefixEnd_322958 : Nat := 4983230072969 + 3 ^ 40 * 322958 * 2
def baseEnd_322958 : Nat := 16378536811343472497753

theorem tailTrace_322958 : CollatzResearch.WordTrace tailWord_322958 prefixEnd_322958 16378536811343472497753 := by
  unfold tailWord_322958
  simp only [CollatzResearch.WordTrace]
  refine ⟨1472405745498224710031191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 7852830642657198453499685 1472405745498224710031191)
  ·
    refine ⟨2208608618247337065046787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1472405745498224710031191 2208608618247337065046787)
    ·
      refine ⟨3312912927371005597570181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2208608618247337065046787 3312912927371005597570181)
      ·
        refine ⟨621171173882063549544409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3312912927371005597570181 621171173882063549544409)
        ·
          refine ⟨465878380411547662158307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 621171173882063549544409 465878380411547662158307)
          ·
            refine ⟨698817570617321493237461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 465878380411547662158307 698817570617321493237461)
            ·
              refine ⟨16378536811343472497753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 698817570617321493237461 16378536811343472497753)
              ·
                rfl

theorem cell20_322958_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 2, 1, 7].length) (baseStart_322958 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_322958 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_322958 prefixEnd_322958 := by exact prefixLift 322958
  have htrace : WordTrace (prefixWord ++ tailWord_322958) baseStart_322958 baseEnd_322958 := by
    simpa [prefixWord, tailWord_322958, baseEnd_322958] using wordTrace_append hprefix tailTrace_322958
  have hstable : (prefixWord ++ tailWord_322958).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_322958).length < 2 ^ (prefixWord ++ tailWord_322958).sum := by decide
  have hdescent : baseEnd_322958 < baseStart_322958 := by decide
  rcases family_descends (prefixWord ++ tailWord_322958) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_322965 : List Nat := [1, 3, 2, 1, 1, 2, 5, 2, 3]
def baseStart_322965 : Nat := 118140960795 + 322965 * 2 ^ 59
def prefixEnd_322965 : Nat := 4983230072969 + 3 ^ 40 * 322965 * 2
def baseEnd_322965 : Nat := 147410026292830339246415

theorem tailTrace_322965 : CollatzResearch.WordTrace tailWord_322965 prefixEnd_322965 147410026292830339246415 := by
  unfold tailWord_322965
  simp only [CollatzResearch.WordTrace]
  refine ⟨11779501274960437875754349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7853000849973625250502899 11779501274960437875754349)
  ·
    refine ⟨4417312978110164203407881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11779501274960437875754349 4417312978110164203407881)
    ·
      refine ⟨3312984733582623152555911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4417312978110164203407881 3312984733582623152555911)
      ·
        refine ⟨4969477100373934728833867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3312984733582623152555911 4969477100373934728833867)
        ·
          refine ⟨7454215650560902093250801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4969477100373934728833867 7454215650560902093250801)
          ·
            refine ⟨5590661737920676569938101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7454215650560902093250801 5590661737920676569938101)
            ·
              refine ⟨524124537930063428431697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 5590661737920676569938101 524124537930063428431697)
              ·
                refine ⟨393093403447547571323773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 524124537930063428431697 393093403447547571323773)
                ·
                  refine ⟨147410026292830339246415, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 393093403447547571323773 147410026292830339246415)
                  ·
                    rfl

theorem cell20_322965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 5, 2, 3].length) (baseStart_322965 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_322965 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_322965 prefixEnd_322965 := by exact prefixLift 322965
  have htrace : WordTrace (prefixWord ++ tailWord_322965) baseStart_322965 baseEnd_322965 := by
    simpa [prefixWord, tailWord_322965, baseEnd_322965] using wordTrace_append hprefix tailTrace_322965
  have hstable : (prefixWord ++ tailWord_322965).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_322965).length < 2 ^ (prefixWord ++ tailWord_322965).sum := by decide
  have hdescent : baseEnd_322965 < baseStart_322965 := by decide
  rcases family_descends (prefixWord ++ tailWord_322965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_322989 : List Nat := [1, 5, 2, 2, 1, 1, 2, 2, 4]
def baseStart_322989 : Nat := 118140960795 + 322989 * 2 ^ 59
def prefixEnd_322989 : Nat := 4983230072969 + 3 ^ 40 * 322989 * 2
def baseEnd_322989 : Nat := 147420980546792922446317

theorem tailTrace_322989 : CollatzResearch.WordTrace tailWord_322989 prefixEnd_322989 147420980546792922446317 := by
  unfold tailWord_322989
  simp only [CollatzResearch.WordTrace]
  refine ⟨11780376626873489974628021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7853584417915659983085347 11780376626873489974628021)
  ·
    refine ⟨1104410308769389685121377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 11780376626873489974628021 1104410308769389685121377)
    ·
      refine ⟨828307731577042263841033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1104410308769389685121377 828307731577042263841033)
      ·
        refine ⟨621230798682781697880775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 828307731577042263841033 621230798682781697880775)
        ·
          refine ⟨931846198024172546821163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 621230798682781697880775 931846198024172546821163)
          ·
            refine ⟨1397769297036258820231745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 931846198024172546821163 1397769297036258820231745)
            ·
              refine ⟨1048326972777194115173809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1397769297036258820231745 1048326972777194115173809)
              ·
                refine ⟨786245229582895586380357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1048326972777194115173809 786245229582895586380357)
                ·
                  refine ⟨147420980546792922446317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 786245229582895586380357 147420980546792922446317)
                  ·
                    rfl

theorem cell20_322989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 2, 2, 4].length) (baseStart_322989 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_322989 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_322989 prefixEnd_322989 := by exact prefixLift 322989
  have htrace : WordTrace (prefixWord ++ tailWord_322989) baseStart_322989 baseEnd_322989 := by
    simpa [prefixWord, tailWord_322989, baseEnd_322989] using wordTrace_append hprefix tailTrace_322989
  have hstable : (prefixWord ++ tailWord_322989).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_322989).length < 2 ^ (prefixWord ++ tailWord_322989).sum := by decide
  have hdescent : baseEnd_322989 < baseStart_322989 := by decide
  rcases family_descends (prefixWord ++ tailWord_322989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_323037 : List Nat := [1, 4, 3, 1, 1, 4, 2, 1, 3]
def baseStart_323037 : Nat := 118140960795 + 323037 * 2 ^ 59
def prefixEnd_323037 : Nat := 4983230072969 + 3 ^ 40 * 323037 * 2
def baseEnd_323037 : Nat := 147442889054718088846121

theorem tailTrace_323037 : CollatzResearch.WordTrace tailWord_323037 prefixEnd_323037 147442889054718088846121 := by
  unfold tailWord_323037
  simp only [CollatzResearch.WordTrace]
  refine ⟨11782127330699594172375365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7854751553799729448250243 11782127330699594172375365)
  ·
    refine ⟨2209148874506173907320381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 11782127330699594172375365 2209148874506173907320381)
    ·
      refine ⟨828430827939815215245143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2209148874506173907320381 828430827939815215245143)
      ·
        refine ⟨1242646241909722822867715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 828430827939815215245143 1242646241909722822867715)
        ·
          refine ⟨1863969362864584234301573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1242646241909722822867715 1863969362864584234301573)
          ·
            refine ⟨349494255537109543931545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1863969362864584234301573 349494255537109543931545)
            ·
              refine ⟨262120691652832157948659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 349494255537109543931545 262120691652832157948659)
              ·
                refine ⟨393181037479248236922989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 262120691652832157948659 393181037479248236922989)
                ·
                  refine ⟨147442889054718088846121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 393181037479248236922989 147442889054718088846121)
                  ·
                    rfl

theorem cell20_323037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 4, 2, 1, 3].length) (baseStart_323037 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_323037 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_323037 prefixEnd_323037 := by exact prefixLift 323037
  have htrace : WordTrace (prefixWord ++ tailWord_323037) baseStart_323037 baseEnd_323037 := by
    simpa [prefixWord, tailWord_323037, baseEnd_323037] using wordTrace_append hprefix tailTrace_323037
  have hstable : (prefixWord ++ tailWord_323037).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_323037).length < 2 ^ (prefixWord ++ tailWord_323037).sum := by decide
  have hdescent : baseEnd_323037 < baseStart_323037 := by decide
  rcases family_descends (prefixWord ++ tailWord_323037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_323041 : List Nat := [1, 2, 3, 1, 2, 4, 1, 3, 3]
def baseStart_323041 : Nat := 118140960795 + 323041 * 2 ^ 59
def prefixEnd_323041 : Nat := 4983230072969 + 3 ^ 40 * 323041 * 2
def baseEnd_323041 : Nat := 147444714763711852712771

theorem tailTrace_323041 : CollatzResearch.WordTrace tailWord_323041 prefixEnd_323041 147444714763711852712771 := by
  unfold tailWord_323041
  simp only [CollatzResearch.WordTrace]
  refine ⟨11782273222685102855520977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7854848815123401903680651 11782273222685102855520977)
  ·
    refine ⟨8836704917013827141640733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11782273222685102855520977 8836704917013827141640733)
    ·
      refine ⟨3313764343880185178115275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8836704917013827141640733 3313764343880185178115275)
      ·
        refine ⟨4970646515820277767172913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3313764343880185178115275 4970646515820277767172913)
        ·
          refine ⟨3727984886865208325379685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4970646515820277767172913 3727984886865208325379685)
          ·
            refine ⟨698997166287226561008691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3727984886865208325379685 698997166287226561008691)
            ·
              refine ⟨1048495749430839841513037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 698997166287226561008691 1048495749430839841513037)
              ·
                refine ⟨393185906036564940567389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1048495749430839841513037 393185906036564940567389)
                ·
                  refine ⟨147444714763711852712771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 393185906036564940567389 147444714763711852712771)
                  ·
                    rfl

theorem cell20_323041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 4, 1, 3, 3].length) (baseStart_323041 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_323041 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_323041 prefixEnd_323041 := by exact prefixLift 323041
  have htrace : WordTrace (prefixWord ++ tailWord_323041) baseStart_323041 baseEnd_323041 := by
    simpa [prefixWord, tailWord_323041, baseEnd_323041] using wordTrace_append hprefix tailTrace_323041
  have hstable : (prefixWord ++ tailWord_323041).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_323041).length < 2 ^ (prefixWord ++ tailWord_323041).sum := by decide
  have hdescent : baseEnd_323041 < baseStart_323041 := by decide
  rcases family_descends (prefixWord ++ tailWord_323041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_323079 : List Nat := [1, 1, 4, 3, 2, 1, 1, 4, 3]
def baseStart_323079 : Nat := 118140960795 + 323079 * 2 ^ 59
def prefixEnd_323079 : Nat := 4983230072969 + 3 ^ 40 * 323079 * 2
def baseEnd_323079 : Nat := 147462058999152609445949

theorem tailTrace_323079 : CollatzResearch.WordTrace tailWord_323079 prefixEnd_323079 147462058999152609445949 := by
  unfold tailWord_323079
  simp only [CollatzResearch.WordTrace]
  refine ⟨11783659196547435345404291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7855772797698290230269527 11783659196547435345404291)
  ·
    refine ⟨17675488794821153018106437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11783659196547435345404291 17675488794821153018106437)
    ·
      refine ⟨3314154149028966190894957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 17675488794821153018106437 3314154149028966190894957)
      ·
        refine ⟨1242807805885862321585609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3314154149028966190894957 1242807805885862321585609)
        ·
          refine ⟨932105854414396741189207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1242807805885862321585609 932105854414396741189207)
          ·
            refine ⟨1398158781621595111783811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 932105854414396741189207 1398158781621595111783811)
            ·
              refine ⟨2097238172432392667675717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1398158781621595111783811 2097238172432392667675717)
              ·
                refine ⟨393232157331073625189197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2097238172432392667675717 393232157331073625189197)
                ·
                  refine ⟨147462058999152609445949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 393232157331073625189197 147462058999152609445949)
                  ·
                    rfl

theorem cell20_323079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 1, 4, 3].length) (baseStart_323079 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_323079 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_323079 prefixEnd_323079 := by exact prefixLift 323079
  have htrace : WordTrace (prefixWord ++ tailWord_323079) baseStart_323079 baseEnd_323079 := by
    simpa [prefixWord, tailWord_323079, baseEnd_323079] using wordTrace_append hprefix tailTrace_323079
  have hstable : (prefixWord ++ tailWord_323079).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_323079).length < 2 ^ (prefixWord ++ tailWord_323079).sum := by decide
  have hdescent : baseEnd_323079 < baseStart_323079 := by decide
  rcases family_descends (prefixWord ++ tailWord_323079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_323082 : List Nat := [3, 1, 2, 2, 2, 2, 4, 2, 2]
def baseStart_323082 : Nat := 118140960795 + 323082 * 2 ^ 59
def prefixEnd_323082 : Nat := 4983230072969 + 3 ^ 40 * 323082 * 2
def baseEnd_323082 : Nat := 147463428280897932345937

theorem tailTrace_323082 : CollatzResearch.WordTrace tailWord_323082 prefixEnd_323082 147463428280897932345937 := by
  unfold tailWord_323082
  simp only [CollatzResearch.WordTrace]
  refine ⟨2945942153884141714440875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7855845743691044571842333 2945942153884141714440875)
  ·
    refine ⟨4418913230826212571661313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2945942153884141714440875 4418913230826212571661313)
    ·
      refine ⟨3314184923119659428745985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4418913230826212571661313 3314184923119659428745985)
      ·
        refine ⟨2485638692339744571559489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3314184923119659428745985 2485638692339744571559489)
        ·
          refine ⟨1864229019254808428669617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2485638692339744571559489 1864229019254808428669617)
          ·
            refine ⟨1398171764441106321502213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1864229019254808428669617 1398171764441106321502213)
            ·
              refine ⟨262157205832707435281665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1398171764441106321502213 262157205832707435281665)
              ·
                refine ⟨196617904374530576461249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 262157205832707435281665 196617904374530576461249)
                ·
                  refine ⟨147463428280897932345937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 196617904374530576461249 147463428280897932345937)
                  ·
                    rfl

theorem cell20_323082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 4, 2, 2].length) (baseStart_323082 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_323082 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_323082 prefixEnd_323082 := by exact prefixLift 323082
  have htrace : WordTrace (prefixWord ++ tailWord_323082) baseStart_323082 baseEnd_323082 := by
    simpa [prefixWord, tailWord_323082, baseEnd_323082] using wordTrace_append hprefix tailTrace_323082
  have hstable : (prefixWord ++ tailWord_323082).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_323082).length < 2 ^ (prefixWord ++ tailWord_323082).sum := by decide
  have hdescent : baseEnd_323082 < baseStart_323082 := by decide
  rcases family_descends (prefixWord ++ tailWord_323082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_323085 : List Nat := [1, 7, 1, 1, 3, 1, 1, 5]
def baseStart_323085 : Nat := 118140960795 + 323085 * 2 ^ 59
def prefixEnd_323085 : Nat := 4983230072969 + 3 ^ 40 * 323085 * 2
def baseEnd_323085 : Nat := 49154932520881085081975

theorem tailTrace_323085 : CollatzResearch.WordTrace tailWord_323085 prefixEnd_323085 49154932520881085081975 := by
  unfold tailWord_323085
  simp only [CollatzResearch.WordTrace]
  refine ⟨11783878034525698370122709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7855918689683798913415139 11783878034525698370122709)
  ·
    refine ⟨276184641434196055549751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 11783878034525698370122709 276184641434196055549751)
    ·
      refine ⟨414276962151294083324627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 276184641434196055549751 414276962151294083324627)
      ·
        refine ⟨621415443226941124986941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 414276962151294083324627 621415443226941124986941)
        ·
          refine ⟨233030791210102921870103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 621415443226941124986941 233030791210102921870103)
          ·
            refine ⟨349546186815154382805155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 233030791210102921870103 349546186815154382805155)
            ·
              refine ⟨524319280222731574207733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 349546186815154382805155 524319280222731574207733)
              ·
                refine ⟨49154932520881085081975, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 524319280222731574207733 49154932520881085081975)
                ·
                  rfl

theorem cell20_323085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 3, 1, 1, 5].length) (baseStart_323085 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_323085 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_323085 prefixEnd_323085 := by exact prefixLift 323085
  have htrace : WordTrace (prefixWord ++ tailWord_323085) baseStart_323085 baseEnd_323085 := by
    simpa [prefixWord, tailWord_323085, baseEnd_323085] using wordTrace_append hprefix tailTrace_323085
  have hstable : (prefixWord ++ tailWord_323085).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_323085).length < 2 ^ (prefixWord ++ tailWord_323085).sum := by decide
  have hdescent : baseEnd_323085 < baseStart_323085 := by decide
  rcases family_descends (prefixWord ++ tailWord_323085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_323093 : List Nat := [1, 3, 2, 1, 3, 2, 3, 5]
def baseStart_323093 : Nat := 118140960795 + 323093 * 2 ^ 59
def prefixEnd_323093 : Nat := 4983230072969 + 3 ^ 40 * 323093 * 2
def baseEnd_323093 : Nat := 49156149660210260993075

theorem tailTrace_323093 : CollatzResearch.WordTrace tailWord_323093 prefixEnd_323093 49156149660210260993075 := by
  unfold tailWord_323093
  simp only [CollatzResearch.WordTrace]
  refine ⟨11784169818496715736413933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7856113212331143824275955 11784169818496715736413933)
  ·
    refine ⟨4419063681936268401155225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11784169818496715736413933 4419063681936268401155225)
    ·
      refine ⟨3314297761452201300866419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4419063681936268401155225 3314297761452201300866419)
      ·
        refine ⟨4971446642178301951299629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3314297761452201300866419 4971446642178301951299629)
        ·
          refine ⟨1864292490816863231737361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4971446642178301951299629 1864292490816863231737361)
          ·
            refine ⟨1398219368112647423803021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1864292490816863231737361 1398219368112647423803021)
            ·
              refine ⟨524332263042242783926133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1398219368112647423803021 524332263042242783926133)
              ·
                refine ⟨49156149660210260993075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 524332263042242783926133 49156149660210260993075)
                ·
                  rfl

theorem cell20_323093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 3, 5].length) (baseStart_323093 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_323093 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_323093 prefixEnd_323093 := by exact prefixLift 323093
  have htrace : WordTrace (prefixWord ++ tailWord_323093) baseStart_323093 baseEnd_323093 := by
    simpa [prefixWord, tailWord_323093, baseEnd_323093] using wordTrace_append hprefix tailTrace_323093
  have hstable : (prefixWord ++ tailWord_323093).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_323093).length < 2 ^ (prefixWord ++ tailWord_323093).sum := by decide
  have hdescent : baseEnd_323093 < baseStart_323093 := by decide
  rcases family_descends (prefixWord ++ tailWord_323093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_323152 : List Nat := [2, 1, 1, 1, 1, 3, 4, 7]
def baseStart_323152 : Nat := 118140960795 + 323152 * 2 ^ 59
def prefixEnd_323152 : Nat := 4983230072969 + 3 ^ 40 * 323152 * 2
def baseEnd_323152 : Nat := 49165126062762933337439

theorem tailTrace_323152 : CollatzResearch.WordTrace tailWord_323152 prefixEnd_323152 49165126062762933337439 := by
  unfold tailWord_323152
  simp only [CollatzResearch.WordTrace]
  refine ⟨5893160862641484406405855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7857547816855312541874473 5893160862641484406405855)
  ·
    refine ⟨8839741293962226609608783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5893160862641484406405855 8839741293962226609608783)
    ·
      refine ⟨13259611940943339914413175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8839741293962226609608783 13259611940943339914413175)
      ·
        refine ⟨19889417911415009871619763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13259611940943339914413175 19889417911415009871619763)
        ·
          refine ⟨29834126867122514807429645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19889417911415009871619763 29834126867122514807429645)
          ·
            refine ⟨11187797575170943052786117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29834126867122514807429645 11187797575170943052786117)
            ·
              refine ⟨2097712045344551822397397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11187797575170943052786117 2097712045344551822397397)
              ·
                refine ⟨49165126062762933337439, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2097712045344551822397397 49165126062762933337439)
                ·
                  rfl

theorem cell20_323152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 4, 7].length) (baseStart_323152 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_323152 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_323152 prefixEnd_323152 := by exact prefixLift 323152
  have htrace : WordTrace (prefixWord ++ tailWord_323152) baseStart_323152 baseEnd_323152 := by
    simpa [prefixWord, tailWord_323152, baseEnd_323152] using wordTrace_append hprefix tailTrace_323152
  have hstable : (prefixWord ++ tailWord_323152).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_323152).length < 2 ^ (prefixWord ++ tailWord_323152).sum := by decide
  have hdescent : baseEnd_323152 < baseStart_323152 := by decide
  rcases family_descends (prefixWord ++ tailWord_323152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_323165 : List Nat := [1, 4, 4, 2, 1, 1, 1, 6]
def baseStart_323165 : Nat := 118140960795 + 323165 * 2 ^ 59
def prefixEnd_323165 : Nat := 4983230072969 + 3 ^ 40 * 323165 * 2
def baseEnd_323165 : Nat := 49167103914172844192977

theorem tailTrace_323165 : CollatzResearch.WordTrace tailWord_323165 prefixEnd_323165 49167103914172844192977 := by
  unfold tailWord_323165
  simp only [CollatzResearch.WordTrace]
  refine ⟨11786795874235872033034949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7857863916157248022023299 11786795874235872033034949)
  ·
    refine ⟨2210024226419226006194053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 11786795874235872033034949 2210024226419226006194053)
    ·
      refine ⟨414379542453604876161385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2210024226419226006194053 414379542453604876161385)
      ·
        refine ⟨310784656840203657121039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 414379542453604876161385 310784656840203657121039)
        ·
          refine ⟨466176985260305485681559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 310784656840203657121039 466176985260305485681559)
          ·
            refine ⟨699265477890458228522339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 466176985260305485681559 699265477890458228522339)
            ·
              refine ⟨1048898216835687342783509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 699265477890458228522339 1048898216835687342783509)
              ·
                refine ⟨49167103914172844192977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1048898216835687342783509 49167103914172844192977)
                ·
                  rfl

theorem cell20_323165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 1, 1, 1, 6].length) (baseStart_323165 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_323165 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_323165 prefixEnd_323165 := by exact prefixLift 323165
  have htrace : WordTrace (prefixWord ++ tailWord_323165) baseStart_323165 baseEnd_323165 := by
    simpa [prefixWord, tailWord_323165, baseEnd_323165] using wordTrace_append hprefix tailTrace_323165
  have hstable : (prefixWord ++ tailWord_323165).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_323165).length < 2 ^ (prefixWord ++ tailWord_323165).sum := by decide
  have hdescent : baseEnd_323165 < baseStart_323165 := by decide
  rcases family_descends (prefixWord ++ tailWord_323165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_323207 : List Nat := [1, 1, 4, 2, 1, 4, 2, 5]
def baseStart_323207 : Nat := 118140960795 + 323207 * 2 ^ 59
def prefixEnd_323207 : Nat := 4983230072969 + 3 ^ 40 * 323207 * 2
def baseEnd_323207 : Nat := 49173493895651017726253

theorem tailTrace_323207 : CollatzResearch.WordTrace tailWord_323207 prefixEnd_323207 49173493895651017726253 := by
  unfold tailWord_323207
  simp only [CollatzResearch.WordTrace]
  refine ⟨11788327740083713206063875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7858885160055808804042583 11788327740083713206063875)
  ·
    refine ⟨17682491610125569809095813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11788327740083713206063875 17682491610125569809095813)
    ·
      refine ⟨3315467176898544339205465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 17682491610125569809095813 3315467176898544339205465)
      ·
        refine ⟨2486600382673908254404099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3315467176898544339205465 2486600382673908254404099)
        ·
          refine ⟨3729900574010862381606149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2486600382673908254404099 3729900574010862381606149)
          ·
            refine ⟨699356357627036696551153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3729900574010862381606149 699356357627036696551153)
            ·
              refine ⟨524517268220277522413365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 699356357627036696551153 524517268220277522413365)
              ·
                refine ⟨49173493895651017726253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 524517268220277522413365 49173493895651017726253)
                ·
                  rfl

theorem cell20_323207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 4, 2, 5].length) (baseStart_323207 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_323207 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_323207 prefixEnd_323207 := by exact prefixLift 323207
  have htrace : WordTrace (prefixWord ++ tailWord_323207) baseStart_323207 baseEnd_323207 := by
    simpa [prefixWord, tailWord_323207, baseEnd_323207] using wordTrace_append hprefix tailTrace_323207
  have hstable : (prefixWord ++ tailWord_323207).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_323207).length < 2 ^ (prefixWord ++ tailWord_323207).sum := by decide
  have hdescent : baseEnd_323207 < baseStart_323207 := by decide
  rcases family_descends (prefixWord ++ tailWord_323207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_323210 : List Nat := [3, 1, 2, 3, 2, 1, 4, 1, 3]
def baseStart_323210 : Nat := 118140960795 + 323210 * 2 ^ 59
def prefixEnd_323210 : Nat := 4983230072969 + 3 ^ 40 * 323210 * 2
def baseEnd_323210 : Nat := 147521850968698376078747

theorem tailTrace_323210 : CollatzResearch.WordTrace tailWord_323210 prefixEnd_323210 147521850968698376078747 := by
  unfold tailWord_323210
  simp only [CollatzResearch.WordTrace]
  refine ⟨2947109289768211179605771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7858958106048563145615389 2947109289768211179605771)
  ·
    refine ⟨4420663934652316769408657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2947109289768211179605771 4420663934652316769408657)
    ·
      refine ⟨3315497950989237577056493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4420663934652316769408657 3315497950989237577056493)
      ·
        refine ⟨1243311731620964091396185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3315497950989237577056493 1243311731620964091396185)
        ·
          refine ⟨932483798715723068547139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1243311731620964091396185 932483798715723068547139)
          ·
            refine ⟨1398725698073584602820709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 932483798715723068547139 1398725698073584602820709)
            ·
              refine ⟨262261068388797113028883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1398725698073584602820709 262261068388797113028883)
              ·
                refine ⟨393391602583195669543325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 262261068388797113028883 393391602583195669543325)
                ·
                  refine ⟨147521850968698376078747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 393391602583195669543325 147521850968698376078747)
                  ·
                    rfl

theorem cell20_323210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 4, 1, 3].length) (baseStart_323210 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_323210 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_323210 prefixEnd_323210 := by exact prefixLift 323210
  have htrace : WordTrace (prefixWord ++ tailWord_323210) baseStart_323210 baseEnd_323210 := by
    simpa [prefixWord, tailWord_323210, baseEnd_323210] using wordTrace_append hprefix tailTrace_323210
  have hstable : (prefixWord ++ tailWord_323210).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_323210).length < 2 ^ (prefixWord ++ tailWord_323210).sum := by decide
  have hdescent : baseEnd_323210 < baseStart_323210 := by decide
  rcases family_descends (prefixWord ++ tailWord_323210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_323221 : List Nat := [1, 3, 2, 1, 1, 1, 1, 6, 4]
def baseStart_323221 : Nat := 118140960795 + 323221 * 2 ^ 59
def prefixEnd_323221 : Nat := 4983230072969 + 3 ^ 40 * 323221 * 2
def baseEnd_323221 : Nat := 147526871668431226712035

theorem tailTrace_323221 : CollatzResearch.WordTrace tailWord_323221 prefixEnd_323221 147526871668431226712035 := by
  unfold tailWord_323221
  simp only [CollatzResearch.WordTrace]
  refine ⟨11788838362032993597073517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7859225574688662398049011 11788838362032993597073517)
  ·
    refine ⟨4420814385762372598902569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11788838362032993597073517 4420814385762372598902569)
    ·
      refine ⟨3315610789321779449176927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4420814385762372598902569 3315610789321779449176927)
      ·
        refine ⟨4973416183982669173765391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3315610789321779449176927 4973416183982669173765391)
        ·
          refine ⟨7460124275974003760648087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4973416183982669173765391 7460124275974003760648087)
          ·
            refine ⟨11190186413961005640972131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7460124275974003760648087 11190186413961005640972131)
            ·
              refine ⟨16785279620941508461458197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11190186413961005640972131 16785279620941508461458197)
              ·
                refine ⟨786809982231633209130853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 16785279620941508461458197 786809982231633209130853)
                ·
                  refine ⟨147526871668431226712035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 786809982231633209130853 147526871668431226712035)
                  ·
                    rfl

theorem cell20_323221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 6, 4].length) (baseStart_323221 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_323221 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_323221 prefixEnd_323221 := by exact prefixLift 323221
  have htrace : WordTrace (prefixWord ++ tailWord_323221) baseStart_323221 baseEnd_323221 := by
    simpa [prefixWord, tailWord_323221, baseEnd_323221] using wordTrace_append hprefix tailTrace_323221
  have hstable : (prefixWord ++ tailWord_323221).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_323221).length < 2 ^ (prefixWord ++ tailWord_323221).sum := by decide
  have hdescent : baseEnd_323221 < baseStart_323221 := by decide
  rcases family_descends (prefixWord ++ tailWord_323221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_323255 : List Nat := [1, 1, 3, 1, 5, 2, 1, 4, 2]
def baseStart_323255 : Nat := 118140960795 + 323255 * 2 ^ 59
def prefixEnd_323255 : Nat := 4983230072969 + 3 ^ 40 * 323255 * 2
def baseEnd_323255 : Nat := 147542390194878219578563

theorem tailTrace_323255 : CollatzResearch.WordTrace tailWord_323255 prefixEnd_323255 147542390194878219578563 := by
  unfold tailWord_323255
  simp only [CollatzResearch.WordTrace]
  refine ⟨11790078443909817403811219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7860052295939878269207479 11790078443909817403811219)
  ·
    refine ⟨17685117665864726105716829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11790078443909817403811219 17685117665864726105716829)
    ·
      refine ⟨6631919124699272289643811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17685117665864726105716829 6631919124699272289643811)
      ·
        refine ⟨9947878687048908434465717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6631919124699272289643811 9947878687048908434465717)
        ·
          refine ⟨932613626910835165731161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 9947878687048908434465717 932613626910835165731161)
          ·
            refine ⟨699460220183126374298371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 932613626910835165731161 699460220183126374298371)
            ·
              refine ⟨1049190330274689561447557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 699460220183126374298371 1049190330274689561447557)
              ·
                refine ⟨196723186926504292771417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1049190330274689561447557 196723186926504292771417)
                ·
                  refine ⟨147542390194878219578563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 196723186926504292771417 147542390194878219578563)
                  ·
                    rfl

theorem cell20_323255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 2, 1, 4, 2].length) (baseStart_323255 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_323255 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_323255 prefixEnd_323255 := by exact prefixLift 323255
  have htrace : WordTrace (prefixWord ++ tailWord_323255) baseStart_323255 baseEnd_323255 := by
    simpa [prefixWord, tailWord_323255, baseEnd_323255] using wordTrace_append hprefix tailTrace_323255
  have hstable : (prefixWord ++ tailWord_323255).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_323255).length < 2 ^ (prefixWord ++ tailWord_323255).sum := by decide
  have hdescent : baseEnd_323255 < baseStart_323255 := by decide
  rcases family_descends (prefixWord ++ tailWord_323255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_323262 : List Nat := [4, 2, 1, 1, 2, 4, 1, 5]
def baseStart_323262 : Nat := 118140960795 + 323262 * 2 ^ 59
def prefixEnd_323262 : Nat := 4983230072969 + 3 ^ 40 * 323262 * 2
def baseEnd_323262 : Nat := 49181861728539102115067

theorem tailTrace_323262 : CollatzResearch.WordTrace tailWord_323262 prefixEnd_323262 49181861728539102115067 := by
  unfold tailWord_323262
  simp only [CollatzResearch.WordTrace]
  refine ⟨1473791719360557199914505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 7860222503256305066210693 1473791719360557199914505)
  ·
    refine ⟨1105343789520417899935879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1473791719360557199914505 1105343789520417899935879)
    ·
      refine ⟨1658015684280626849903819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1105343789520417899935879 1658015684280626849903819)
      ·
        refine ⟨2487023526420940274855729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1658015684280626849903819 2487023526420940274855729)
        ·
          refine ⟨1865267644815705206141797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2487023526420940274855729 1865267644815705206141797)
          ·
            refine ⟨349737683402944726151587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1865267644815705206141797 349737683402944726151587)
            ·
              refine ⟨524606525104417089227381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 349737683402944726151587 524606525104417089227381)
              ·
                refine ⟨49181861728539102115067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 524606525104417089227381 49181861728539102115067)
                ·
                  rfl

theorem cell20_323262_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 4, 1, 5].length) (baseStart_323262 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_323262 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_323262 prefixEnd_323262 := by exact prefixLift 323262
  have htrace : WordTrace (prefixWord ++ tailWord_323262) baseStart_323262 baseEnd_323262 := by
    simpa [prefixWord, tailWord_323262, baseEnd_323262] using wordTrace_append hprefix tailTrace_323262
  have hstable : (prefixWord ++ tailWord_323262).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_323262).length < 2 ^ (prefixWord ++ tailWord_323262).sum := by decide
  have hdescent : baseEnd_323262 < baseStart_323262 := by decide
  rcases family_descends (prefixWord ++ tailWord_323262) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_323303 : List Nat := [1, 1, 5, 4, 1, 2, 1, 2, 3]
def baseStart_323303 : Nat := 118140960795 + 323303 * 2 ^ 59
def prefixEnd_323303 : Nat := 4983230072969 + 3 ^ 40 * 323303 * 2
def baseEnd_323303 : Nat := 147564298702803385978367

theorem tailTrace_323303 : CollatzResearch.WordTrace tailWord_323303 prefixEnd_323303 147564298702803385978367 := by
  unfold tailWord_323303
  simp only [CollatzResearch.WordTrace]
  refine ⟨11791829147735921601558563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7861219431823947734372375 11791829147735921601558563)
  ·
    refine ⟨17687743721603882402337845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11791829147735921601558563 17687743721603882402337845)
    ·
      refine ⟨1658225973900363975219173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 17687743721603882402337845 1658225973900363975219173)
      ·
        refine ⟨310917370106318245353595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1658225973900363975219173 310917370106318245353595)
        ·
          refine ⟨466376055159477368030393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 310917370106318245353595 466376055159477368030393)
          ·
            refine ⟨349782041369608026022795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 466376055159477368030393 349782041369608026022795)
            ·
              refine ⟨524673062054412039034193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 349782041369608026022795 524673062054412039034193)
              ·
                refine ⟨393504796540809029275645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 524673062054412039034193 393504796540809029275645)
                ·
                  refine ⟨147564298702803385978367, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 393504796540809029275645 147564298702803385978367)
                  ·
                    rfl

theorem cell20_323303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 1, 2, 1, 2, 3].length) (baseStart_323303 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_323303 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_323303 prefixEnd_323303 := by exact prefixLift 323303
  have htrace : WordTrace (prefixWord ++ tailWord_323303) baseStart_323303 baseEnd_323303 := by
    simpa [prefixWord, tailWord_323303, baseEnd_323303] using wordTrace_append hprefix tailTrace_323303
  have hstable : (prefixWord ++ tailWord_323303).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_323303).length < 2 ^ (prefixWord ++ tailWord_323303).sum := by decide
  have hdescent : baseEnd_323303 < baseStart_323303 := by decide
  rcases family_descends (prefixWord ++ tailWord_323303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_323314 : List Nat := [3, 2, 1, 3, 1, 1, 4, 1, 4]
def baseStart_323314 : Nat := 118140960795 + 323314 * 2 ^ 59
def prefixEnd_323314 : Nat := 4983230072969 + 3 ^ 40 * 323314 * 2
def baseEnd_323314 : Nat := 147569319402536236611655

theorem tailTrace_323314 : CollatzResearch.WordTrace tailWord_323314 prefixEnd_323314 147569319402536236611655 := by
  unfold tailWord_323314
  simp only [CollatzResearch.WordTrace]
  refine ⟨2948057587674017620052249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7861486900464046986805997 2948057587674017620052249)
  ·
    refine ⟨2211043190755513215039187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2948057587674017620052249 2211043190755513215039187)
    ·
      refine ⟨3316564786133269822558781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2211043190755513215039187 3316564786133269822558781)
      ·
        refine ⟨1243711794799976183459543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3316564786133269822558781 1243711794799976183459543)
        ·
          refine ⟨1865567692199964275189315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1243711794799976183459543 1865567692199964275189315)
          ·
            refine ⟨2798351538299946412783973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1865567692199964275189315 2798351538299946412783973)
            ·
              refine ⟨524690913431239952396995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2798351538299946412783973 524690913431239952396995)
              ·
                refine ⟨787036370146859928595493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 524690913431239952396995 787036370146859928595493)
                ·
                  refine ⟨147569319402536236611655, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 787036370146859928595493 147569319402536236611655)
                  ·
                    rfl

theorem cell20_323314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 4, 1, 4].length) (baseStart_323314 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_323314 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_323314 prefixEnd_323314 := by exact prefixLift 323314
  have htrace : WordTrace (prefixWord ++ tailWord_323314) baseStart_323314 baseEnd_323314 := by
    simpa [prefixWord, tailWord_323314, baseEnd_323314] using wordTrace_append hprefix tailTrace_323314
  have hstable : (prefixWord ++ tailWord_323314).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_323314).length < 2 ^ (prefixWord ++ tailWord_323314).sum := by decide
  have hdescent : baseEnd_323314 < baseStart_323314 := by decide
  rcases family_descends (prefixWord ++ tailWord_323314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_323338 : List Nat := [3, 1, 2, 2, 1, 5, 2, 4]
def baseStart_323338 : Nat := 118140960795 + 323338 * 2 ^ 59
def prefixEnd_323338 : Nat := 4983230072969 + 3 ^ 40 * 323338 * 2
def baseEnd_323338 : Nat := 49193424552166273270519

theorem tailTrace_323338 : CollatzResearch.WordTrace tailWord_323338 prefixEnd_323338 49193424552166273270519 := by
  unfold tailWord_323338
  simp only [CollatzResearch.WordTrace]
  refine ⟨2948276425652280644770667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7862070468406081719388445 2948276425652280644770667)
  ·
    refine ⟨4422414638478420967156001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2948276425652280644770667 4422414638478420967156001)
    ·
      refine ⟨3316810978858815725367001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4422414638478420967156001 3316810978858815725367001)
      ·
        refine ⟨2487608234144111794025251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3316810978858815725367001 2487608234144111794025251)
        ·
          refine ⟨3731412351216167691037877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2487608234144111794025251 3731412351216167691037877)
          ·
            refine ⟨349819907926515721034801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 3731412351216167691037877 349819907926515721034801)
            ·
              refine ⟨262364930944886790776101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 349819907926515721034801 262364930944886790776101)
              ·
                refine ⟨49193424552166273270519, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 262364930944886790776101 49193424552166273270519)
                ·
                  rfl

theorem cell20_323338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 5, 2, 4].length) (baseStart_323338 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_323338 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_323338 prefixEnd_323338 := by exact prefixLift 323338
  have htrace : WordTrace (prefixWord ++ tailWord_323338) baseStart_323338 baseEnd_323338 := by
    simpa [prefixWord, tailWord_323338, baseEnd_323338] using wordTrace_append hprefix tailTrace_323338
  have hstable : (prefixWord ++ tailWord_323338).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_323338).length < 2 ^ (prefixWord ++ tailWord_323338).sum := by decide
  have hdescent : baseEnd_323338 < baseStart_323338 := by decide
  rcases family_descends (prefixWord ++ tailWord_323338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_323379 : List Nat := [1, 1, 1, 2, 8, 1, 2, 1, 3]
def baseStart_323379 : Nat := 118140960795 + 323379 * 2 ^ 59
def prefixEnd_323379 : Nat := 4983230072969 + 3 ^ 40 * 323379 * 2
def baseEnd_323379 : Nat := 147598987173684899444723

theorem tailTrace_323379 : CollatzResearch.WordTrace tailWord_323379 prefixEnd_323379 147598987173684899444723 := by
  unfold tailWord_323379
  simp only [CollatzResearch.WordTrace]
  refine ⟨11794601095460586581325191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7863067396973724387550127 11794601095460586581325191)
  ·
    refine ⟨17691901643190879871987787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11794601095460586581325191 17691901643190879871987787)
    ·
      refine ⟨26537852464786319807981681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17691901643190879871987787 26537852464786319807981681)
      ·
        refine ⟨19903389348589739855986261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26537852464786319807981681 19903389348589739855986261)
        ·
          refine ⟨233242843928786013937339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 19903389348589739855986261 233242843928786013937339)
          ·
            refine ⟨349864265893179020906009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 233242843928786013937339 349864265893179020906009)
            ·
              refine ⟨262398199419884265679507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 349864265893179020906009 262398199419884265679507)
              ·
                refine ⟨393597299129826398519261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 262398199419884265679507 393597299129826398519261)
                ·
                  refine ⟨147598987173684899444723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 393597299129826398519261 147598987173684899444723)
                  ·
                    rfl

theorem cell20_323379_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 8, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 8, 1, 2, 1, 3].length) (baseStart_323379 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_323379 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_323379 prefixEnd_323379 := by exact prefixLift 323379
  have htrace : WordTrace (prefixWord ++ tailWord_323379) baseStart_323379 baseEnd_323379 := by
    simpa [prefixWord, tailWord_323379, baseEnd_323379] using wordTrace_append hprefix tailTrace_323379
  have hstable : (prefixWord ++ tailWord_323379).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_323379).length < 2 ^ (prefixWord ++ tailWord_323379).sum := by decide
  have hdescent : baseEnd_323379 < baseStart_323379 := by decide
  rcases family_descends (prefixWord ++ tailWord_323379) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_323420 : List Nat := [2, 2, 4, 2, 3, 1, 2, 2, 2]
def baseStart_323420 : Nat := 118140960795 + 323420 * 2 ^ 59
def prefixEnd_323420 : Nat := 4983230072969 + 3 ^ 40 * 323420 * 2
def baseEnd_323420 : Nat := 147617700690870979077889

theorem tailTrace_323420 : CollatzResearch.WordTrace tailWord_323420 prefixEnd_323420 147617700690870979077889 := by
  unfold tailWord_323420
  simp only [CollatzResearch.WordTrace]
  refine ⟨5898048244156025291783857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7864064325541367055711809 5898048244156025291783857)
  ·
    refine ⟨4423536183117018968837893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5898048244156025291783857 4423536183117018968837893)
    ·
      refine ⟨829413034334441056657105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4423536183117018968837893 829413034334441056657105)
      ·
        refine ⟨622059775750830792492829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 829413034334441056657105 622059775750830792492829)
        ·
          refine ⟨233272415906561547184811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 622059775750830792492829 233272415906561547184811)
          ·
            refine ⟨349908623859842320777217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 233272415906561547184811 349908623859842320777217)
            ·
              refine ⟨262431467894881740582913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 349908623859842320777217 262431467894881740582913)
              ·
                refine ⟨196823600921161305437185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 262431467894881740582913 196823600921161305437185)
                ·
                  refine ⟨147617700690870979077889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 196823600921161305437185 147617700690870979077889)
                  ·
                    rfl

theorem cell20_323420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 3, 1, 2, 2, 2].length) (baseStart_323420 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_323420 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_323420 prefixEnd_323420 := by exact prefixLift 323420
  have htrace : WordTrace (prefixWord ++ tailWord_323420) baseStart_323420 baseEnd_323420 := by
    simpa [prefixWord, tailWord_323420, baseEnd_323420] using wordTrace_append hprefix tailTrace_323420
  have hstable : (prefixWord ++ tailWord_323420).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_323420).length < 2 ^ (prefixWord ++ tailWord_323420).sum := by decide
  have hdescent : baseEnd_323420 < baseStart_323420 := by decide
  rcases family_descends (prefixWord ++ tailWord_323420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_323424 : List Nat := [2, 1, 1, 3, 3, 4, 2, 2, 2]
def baseStart_323424 : Nat := 118140960795 + 323424 * 2 ^ 59
def prefixEnd_323424 : Nat := 4983230072969 + 3 ^ 40 * 323424 * 2
def baseEnd_323424 : Nat := 147619526399864742944539

theorem tailTrace_323424 : CollatzResearch.WordTrace tailWord_323424 prefixEnd_323424 147619526399864742944539 := by
  unfold tailWord_323424
  simp only [CollatzResearch.WordTrace]
  refine ⟨5898121190148779633356663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7864161586865039511142217 5898121190148779633356663)
  ·
    refine ⟨8847181785223169450034995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5898121190148779633356663 8847181785223169450034995)
    ·
      refine ⟨13270772677834754175052493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8847181785223169450034995 13270772677834754175052493)
      ·
        refine ⟨4976539754188032815644685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13270772677834754175052493 4976539754188032815644685)
        ·
          refine ⟨1866202407820512305866757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4976539754188032815644685 1866202407820512305866757)
          ·
            refine ⟨349912951466346057350017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1866202407820512305866757 349912951466346057350017)
            ·
              refine ⟨262434713599759543012513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 349912951466346057350017 262434713599759543012513)
              ·
                refine ⟨196826035199819657259385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 262434713599759543012513 196826035199819657259385)
                ·
                  refine ⟨147619526399864742944539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 196826035199819657259385 147619526399864742944539)
                  ·
                    rfl

theorem cell20_323424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 4, 2, 2, 2].length) (baseStart_323424 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_323424 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_323424 prefixEnd_323424 := by exact prefixLift 323424
  have htrace : WordTrace (prefixWord ++ tailWord_323424) baseStart_323424 baseEnd_323424 := by
    simpa [prefixWord, tailWord_323424, baseEnd_323424] using wordTrace_append hprefix tailTrace_323424
  have hstable : (prefixWord ++ tailWord_323424).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_323424).length < 2 ^ (prefixWord ++ tailWord_323424).sum := by decide
  have hdescent : baseEnd_323424 < baseStart_323424 := by decide
  rcases family_descends (prefixWord ++ tailWord_323424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_323449 : List Nat := [1, 2, 1, 3, 2, 2, 3, 2, 4]
def baseStart_323449 : Nat := 118140960795 + 323449 * 2 ^ 59
def prefixEnd_323449 : Nat := 4983230072969 + 3 ^ 40 * 323449 * 2
def baseEnd_323449 : Nat := 147630937081075767111103

theorem tailTrace_323449 : CollatzResearch.WordTrace tailWord_323449 prefixEnd_323449 147630937081075767111103 := by
  unfold tailWord_323449
  simp only [CollatzResearch.WordTrace]
  refine ⟨11797154205206988536373401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7864769470137992357582267 11797154205206988536373401)
  ·
    refine ⟨8847865653905241402280051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11797154205206988536373401 8847865653905241402280051)
    ·
      refine ⟨13271798480857862103420077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8847865653905241402280051 13271798480857862103420077)
      ·
        refine ⟨4976924430321698288782529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13271798480857862103420077 4976924430321698288782529)
        ·
          refine ⟨3732693322741273716586897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4976924430321698288782529 3732693322741273716586897)
          ·
            refine ⟨2799519992055955287440173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3732693322741273716586897 2799519992055955287440173)
            ·
              refine ⟨1049819997020983232790065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2799519992055955287440173 1049819997020983232790065)
              ·
                refine ⟨787364997765737424592549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1049819997020983232790065 787364997765737424592549)
                ·
                  refine ⟨147630937081075767111103, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 787364997765737424592549 147630937081075767111103)
                  ·
                    rfl

theorem cell20_323449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 3, 2, 4].length) (baseStart_323449 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_323449 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_323449 prefixEnd_323449 := by exact prefixLift 323449
  have htrace : WordTrace (prefixWord ++ tailWord_323449) baseStart_323449 baseEnd_323449 := by
    simpa [prefixWord, tailWord_323449, baseEnd_323449] using wordTrace_append hprefix tailTrace_323449
  have hstable : (prefixWord ++ tailWord_323449).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_323449).length < 2 ^ (prefixWord ++ tailWord_323449).sum := by decide
  have hdescent : baseEnd_323449 < baseStart_323449 := by decide
  rcases family_descends (prefixWord ++ tailWord_323449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_323476 : List Nat := [2, 4, 2, 1, 1, 4, 1, 2, 3]
def baseStart_323476 : Nat := 118140960795 + 323476 * 2 ^ 59
def prefixEnd_323476 : Nat := 4983230072969 + 3 ^ 40 * 323476 * 2
def baseEnd_323476 : Nat := 147643260616783673210993

theorem tailTrace_323476 : CollatzResearch.WordTrace tailWord_323476 prefixEnd_323476 147643260616783673210993 := by
  unfold tailWord_323476
  simp only [CollatzResearch.WordTrace]
  refine ⟨5899069488054586073803141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7865425984072781431737521 5899069488054586073803141)
  ·
    refine ⟨1106075529010234888838089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5899069488054586073803141 1106075529010234888838089)
    ·
      refine ⟨829556646757676166628567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1106075529010234888838089 829556646757676166628567)
      ·
        refine ⟨1244334970136514249942851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 829556646757676166628567 1244334970136514249942851)
        ·
          refine ⟨1866502455204771374914277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1244334970136514249942851 1866502455204771374914277)
          ·
            refine ⟨349969210350894632796427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1866502455204771374914277 349969210350894632796427)
            ·
              refine ⟨524953815526341949194641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 349969210350894632796427 524953815526341949194641)
              ·
                refine ⟨393715361644756461895981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 524953815526341949194641 393715361644756461895981)
                ·
                  refine ⟨147643260616783673210993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 393715361644756461895981 147643260616783673210993)
                  ·
                    rfl

theorem cell20_323476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 4, 1, 2, 3].length) (baseStart_323476 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_323476 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_323476 prefixEnd_323476 := by exact prefixLift 323476
  have htrace : WordTrace (prefixWord ++ tailWord_323476) baseStart_323476 baseEnd_323476 := by
    simpa [prefixWord, tailWord_323476, baseEnd_323476] using wordTrace_append hprefix tailTrace_323476
  have hstable : (prefixWord ++ tailWord_323476).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_323476).length < 2 ^ (prefixWord ++ tailWord_323476).sum := by decide
  have hdescent : baseEnd_323476 < baseStart_323476 := by decide
  rcases family_descends (prefixWord ++ tailWord_323476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_323518 : List Nat := [4, 2, 1, 1, 1, 3, 1, 2, 5]
def baseStart_323518 : Nat := 118140960795 + 323518 * 2 ^ 59
def prefixEnd_323518 : Nat := 4983230072969 + 3 ^ 40 * 323518 * 2
def baseEnd_323518 : Nat := 147662430561218193810821

theorem tailTrace_323518 : CollatzResearch.WordTrace tailWord_323518 prefixEnd_323518 147662430561218193810821 := by
  unfold tailWord_323518
  simp only [CollatzResearch.WordTrace]
  refine ⟨1474958855244626665079401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 7866447227971342213756805 1474958855244626665079401)
  ·
    refine ⟨1106219141433469998809551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1474958855244626665079401 1106219141433469998809551)
    ·
      refine ⟨1659328712150204998214327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1106219141433469998809551 1659328712150204998214327)
      ·
        refine ⟨2488993068225307497321491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1659328712150204998214327 2488993068225307497321491)
        ·
          refine ⟨3733489602337961245982237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2488993068225307497321491 3733489602337961245982237)
          ·
            refine ⟨1400058600876735467243339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3733489602337961245982237 1400058600876735467243339)
            ·
              refine ⟨2100087901315103200865009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1400058600876735467243339 2100087901315103200865009)
              ·
                refine ⟨1575065925986327400648757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2100087901315103200865009 1575065925986327400648757)
                ·
                  refine ⟨147662430561218193810821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1575065925986327400648757 147662430561218193810821)
                  ·
                    rfl

theorem cell20_323518_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 1, 2, 5].length) (baseStart_323518 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_323518 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_323518 prefixEnd_323518 := by exact prefixLift 323518
  have htrace : WordTrace (prefixWord ++ tailWord_323518) baseStart_323518 baseEnd_323518 := by
    simpa [prefixWord, tailWord_323518, baseEnd_323518] using wordTrace_append hprefix tailTrace_323518
  have hstable : (prefixWord ++ tailWord_323518).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_323518).length < 2 ^ (prefixWord ++ tailWord_323518).sum := by decide
  have hdescent : baseEnd_323518 < baseStart_323518 := by decide
  rcases family_descends (prefixWord ++ tailWord_323518) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_323532 : List Nat := [2, 2, 1, 4, 1, 2, 8]
def baseStart_323532 : Nat := 118140960795 + 323532 * 2 ^ 59
def prefixEnd_323532 : Nat := 4983230072969 + 3 ^ 40 * 323532 * 2
def baseEnd_323532 : Nat := 16407646726966263038233

theorem tailTrace_323532 : CollatzResearch.WordTrace tailWord_323532 prefixEnd_323532 16407646726966263038233 := by
  unfold tailWord_323532
  simp only [CollatzResearch.WordTrace]
  refine ⟨5900090731953146855822425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7866787642604195807763233 5900090731953146855822425)
  ·
    refine ⟨4425068048964860141866819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5900090731953146855822425 4425068048964860141866819)
    ·
      refine ⟨6637602073447290212800229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4425068048964860141866819 6637602073447290212800229)
      ·
        refine ⟨1244550388771366914900043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6637602073447290212800229 1244550388771366914900043)
        ·
          refine ⟨1866825583157050372350065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1244550388771366914900043 1866825583157050372350065)
          ·
            refine ⟨1400119187367787779262549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1866825583157050372350065 1400119187367787779262549)
            ·
              refine ⟨16407646726966263038233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1400119187367787779262549 16407646726966263038233)
              ·
                rfl

theorem cell20_323532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 8].length) (baseStart_323532 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_323532 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_323532 prefixEnd_323532 := by exact prefixLift 323532
  have htrace : WordTrace (prefixWord ++ tailWord_323532) baseStart_323532 baseEnd_323532 := by
    simpa [prefixWord, tailWord_323532, baseEnd_323532] using wordTrace_append hprefix tailTrace_323532
  have hstable : (prefixWord ++ tailWord_323532).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_323532).length < 2 ^ (prefixWord ++ tailWord_323532).sum := by decide
  have hdescent : baseEnd_323532 < baseStart_323532 := by decide
  rcases family_descends (prefixWord ++ tailWord_323532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_323538 : List Nat := [3, 2, 2, 3, 3, 1, 1, 1, 4]
def baseStart_323538 : Nat := 118140960795 + 323538 * 2 ^ 59
def prefixEnd_323538 : Nat := 4983230072969 + 3 ^ 40 * 323538 * 2
def baseEnd_323538 : Nat := 147671559106187013144073

theorem tailTrace_323538 : CollatzResearch.WordTrace tailWord_323538 prefixEnd_323538 147671559106187013144073 := by
  unfold tailWord_323538
  simp only [CollatzResearch.WordTrace]
  refine ⟨2950100075471139184090817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7866933534589704490908845 2950100075471139184090817)
  ·
    refine ⟨2212575056603354388068113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2950100075471139184090817 2212575056603354388068113)
    ·
      refine ⟨1659431292452515791051085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2212575056603354388068113 1659431292452515791051085)
      ·
        refine ⟨622286734669693421644157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1659431292452515791051085 622286734669693421644157)
        ·
          refine ⟨233357525501135033116559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 622286734669693421644157 233357525501135033116559)
          ·
            refine ⟨350036288251702549674839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 233357525501135033116559 350036288251702549674839)
            ·
              refine ⟨525054432377553824512259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 350036288251702549674839 525054432377553824512259)
              ·
                refine ⟨787581648566330736768389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 525054432377553824512259 787581648566330736768389)
                ·
                  refine ⟨147671559106187013144073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 787581648566330736768389 147671559106187013144073)
                  ·
                    rfl

theorem cell20_323538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 3, 1, 1, 1, 4].length) (baseStart_323538 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_323538 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_323538 prefixEnd_323538 := by exact prefixLift 323538
  have htrace : WordTrace (prefixWord ++ tailWord_323538) baseStart_323538 baseEnd_323538 := by
    simpa [prefixWord, tailWord_323538, baseEnd_323538] using wordTrace_append hprefix tailTrace_323538
  have hstable : (prefixWord ++ tailWord_323538).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_323538).length < 2 ^ (prefixWord ++ tailWord_323538).sum := by decide
  have hdescent : baseEnd_323538 < baseStart_323538 := by decide
  rcases family_descends (prefixWord ++ tailWord_323538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_323556 : List Nat := [2, 3, 1, 1, 1, 1, 5, 3, 3]
def baseStart_323556 : Nat := 118140960795 + 323556 * 2 ^ 59
def prefixEnd_323556 : Nat := 4983230072969 + 3 ^ 40 * 323556 * 2
def baseEnd_323556 : Nat := 147679774796658950543999

theorem tailTrace_323556 : CollatzResearch.WordTrace tailWord_323556 prefixEnd_323556 147679774796658950543999 := by
  unfold tailWord_323556
  simp only [CollatzResearch.WordTrace]
  refine ⟨5900528407909672905259261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7867371210546230540345681 5900528407909672905259261)
  ·
    refine ⟨2212698152966127339472223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5900528407909672905259261 2212698152966127339472223)
    ·
      refine ⟨3319047229449191009208335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2212698152966127339472223 3319047229449191009208335)
      ·
        refine ⟨4978570844173786513812503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3319047229449191009208335 4978570844173786513812503)
        ·
          refine ⟨7467856266260679770718755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4978570844173786513812503 7467856266260679770718755)
          ·
            refine ⟨11201784399391019656078133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7467856266260679770718755 11201784399391019656078133)
            ·
              refine ⟨1050167287442908092757325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 11201784399391019656078133 1050167287442908092757325)
              ·
                refine ⟨393812732791090534783997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1050167287442908092757325 393812732791090534783997)
                ·
                  refine ⟨147679774796658950543999, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 393812732791090534783997 147679774796658950543999)
                  ·
                    rfl

theorem cell20_323556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 5, 3, 3].length) (baseStart_323556 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_323556 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_323556 prefixEnd_323556 := by exact prefixLift 323556
  have htrace : WordTrace (prefixWord ++ tailWord_323556) baseStart_323556 baseEnd_323556 := by
    simpa [prefixWord, tailWord_323556, baseEnd_323556] using wordTrace_append hprefix tailTrace_323556
  have hstable : (prefixWord ++ tailWord_323556).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_323556).length < 2 ^ (prefixWord ++ tailWord_323556).sum := by decide
  have hdescent : baseEnd_323556 < baseStart_323556 := by decide
  rcases family_descends (prefixWord ++ tailWord_323556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_323580 : List Nat := [2, 2, 2, 1, 2, 2, 2, 5, 2]
def baseStart_323580 : Nat := 118140960795 + 323580 * 2 ^ 59
def prefixEnd_323580 : Nat := 4983230072969 + 3 ^ 40 * 323580 * 2
def baseEnd_323580 : Nat := 147690729050621533743901

theorem tailTrace_323580 : CollatzResearch.WordTrace tailWord_323580 prefixEnd_323580 147690729050621533743901 := by
  unfold tailWord_323580
  simp only [CollatzResearch.WordTrace]
  refine ⟨5900966083866198954696097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7867954778488265272928129 5900966083866198954696097)
  ·
    refine ⟨4425724562899649216022073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5900966083866198954696097 4425724562899649216022073)
    ·
      refine ⟨3319293422174736912016555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4425724562899649216022073 3319293422174736912016555)
      ·
        refine ⟨4978940133262105368024833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3319293422174736912016555 4978940133262105368024833)
        ·
          refine ⟨3734205099946579026018625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4978940133262105368024833 3734205099946579026018625)
          ·
            refine ⟨2800653824959934269513969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3734205099946579026018625 2800653824959934269513969)
            ·
              refine ⟨2100490368719950702135477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2800653824959934269513969 2100490368719950702135477)
              ·
                refine ⟨196920972067495378325201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2100490368719950702135477 196920972067495378325201)
                ·
                  refine ⟨147690729050621533743901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 196920972067495378325201 147690729050621533743901)
                  ·
                    rfl

theorem cell20_323580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 2, 5, 2].length) (baseStart_323580 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_323580 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_323580 prefixEnd_323580 := by exact prefixLift 323580
  have htrace : WordTrace (prefixWord ++ tailWord_323580) baseStart_323580 baseEnd_323580 := by
    simpa [prefixWord, tailWord_323580, baseEnd_323580] using wordTrace_append hprefix tailTrace_323580
  have hstable : (prefixWord ++ tailWord_323580).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_323580).length < 2 ^ (prefixWord ++ tailWord_323580).sum := by decide
  have hdescent : baseEnd_323580 < baseStart_323580 := by decide
  rcases family_descends (prefixWord ++ tailWord_323580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_323584 : List Nat := [2, 1, 1, 2, 1, 1, 1, 3, 8]
def baseStart_323584 : Nat := 118140960795 + 323584 * 2 ^ 59
def prefixEnd_323584 : Nat := 4983230072969 + 3 ^ 40 * 323584 * 2
def baseEnd_323584 : Nat := 147692554759615297610551

theorem tailTrace_323584 : CollatzResearch.WordTrace tailWord_323584 prefixEnd_323584 147692554759615297610551 := by
  unfold tailWord_323584
  simp only [CollatzResearch.WordTrace]
  refine ⟨5901039029858953296268903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7868052039811937728358537 5901039029858953296268903)
  ·
    refine ⟨8851558544788429944403355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5901039029858953296268903 8851558544788429944403355)
    ·
      refine ⟨13277337817182644916605033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8851558544788429944403355 13277337817182644916605033)
      ·
        refine ⟨9958003362886983687453775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13277337817182644916605033 9958003362886983687453775)
        ·
          refine ⟨14937005044330475531180663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9958003362886983687453775 14937005044330475531180663)
          ·
            refine ⟨22405507566495713296770995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14937005044330475531180663 22405507566495713296770995)
            ·
              refine ⟨33608261349743569945156493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22405507566495713296770995 33608261349743569945156493)
              ·
                refine ⟨12603098006153838729433685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 33608261349743569945156493 12603098006153838729433685)
                ·
                  refine ⟨147692554759615297610551, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 12603098006153838729433685 147692554759615297610551)
                  ·
                    rfl

theorem cell20_323584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 3, 8].length) (baseStart_323584 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_323584 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_323584 prefixEnd_323584 := by exact prefixLift 323584
  have htrace : WordTrace (prefixWord ++ tailWord_323584) baseStart_323584 baseEnd_323584 := by
    simpa [prefixWord, tailWord_323584, baseEnd_323584] using wordTrace_append hprefix tailTrace_323584
  have hstable : (prefixWord ++ tailWord_323584).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_323584).length < 2 ^ (prefixWord ++ tailWord_323584).sum := by decide
  have hdescent : baseEnd_323584 < baseStart_323584 := by decide
  rcases family_descends (prefixWord ++ tailWord_323584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_323649 : List Nat := [1, 2, 5, 1, 2, 1, 3, 2, 3]
def baseStart_323649 : Nat := 118140960795 + 323649 * 2 ^ 59
def prefixEnd_323649 : Nat := 4983230072969 + 3 ^ 40 * 323649 * 2
def baseEnd_323649 : Nat := 147722222530763960443619

theorem tailTrace_323649 : CollatzResearch.WordTrace tailWord_323649 prefixEnd_323649 147722222530763960443619 := by
  unfold tailWord_323649
  simp only [CollatzResearch.WordTrace]
  refine ⟨11804448804482422693654001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7869632536321615129102667 11804448804482422693654001)
  ·
    refine ⟨8853336603361817020240501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11804448804482422693654001 8853336603361817020240501)
    ·
      refine ⟨830000306565170345647547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 8853336603361817020240501 830000306565170345647547)
      ·
        refine ⟨1245000459847755518471321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 830000306565170345647547 1245000459847755518471321)
        ·
          refine ⟨933750344885816638853491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1245000459847755518471321 933750344885816638853491)
          ·
            refine ⟨1400625517328724958280237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 933750344885816638853491 1400625517328724958280237)
            ·
              refine ⟨525234568998271859355089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1400625517328724958280237 525234568998271859355089)
              ·
                refine ⟨393925926748703894516317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 525234568998271859355089 393925926748703894516317)
                ·
                  refine ⟨147722222530763960443619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 393925926748703894516317 147722222530763960443619)
                  ·
                    rfl

theorem cell20_323649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 3, 2, 3].length) (baseStart_323649 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_323649 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_323649 prefixEnd_323649 := by exact prefixLift 323649
  have htrace : WordTrace (prefixWord ++ tailWord_323649) baseStart_323649 baseEnd_323649 := by
    simpa [prefixWord, tailWord_323649, baseEnd_323649] using wordTrace_append hprefix tailTrace_323649
  have hstable : (prefixWord ++ tailWord_323649).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_323649).length < 2 ^ (prefixWord ++ tailWord_323649).sum := by decide
  have hdescent : baseEnd_323649 < baseStart_323649 := by decide
  rcases family_descends (prefixWord ++ tailWord_323649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_323666 : List Nat := [3, 2, 2, 1, 4, 1, 3, 1, 3]
def baseStart_323666 : Nat := 118140960795 + 323666 * 2 ^ 59
def prefixEnd_323666 : Nat := 4983230072969 + 3 ^ 40 * 323666 * 2
def baseEnd_323666 : Nat := 147729981793987456876883

theorem tailTrace_323666 : CollatzResearch.WordTrace tailWord_323666 prefixEnd_323666 147729981793987456876883 := by
  unfold tailWord_323666
  simp only [CollatzResearch.WordTrace]
  refine ⟨2951267211355208649255713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7870045896947223064681901 2951267211355208649255713)
  ·
    refine ⟨2213450408516406486941785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2951267211355208649255713 2213450408516406486941785)
    ·
      refine ⟨1660087806387304865206339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2213450408516406486941785 1660087806387304865206339)
      ·
        refine ⟨2490131709580957297809509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1660087806387304865206339 2490131709580957297809509)
        ·
          refine ⟨466899695546429493339283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2490131709580957297809509 466899695546429493339283)
          ·
            refine ⟨700349543319644240008925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 466899695546429493339283 700349543319644240008925)
            ·
              refine ⟨262631078744866590003347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 700349543319644240008925 262631078744866590003347)
              ·
                refine ⟨393946618117299885005021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 262631078744866590003347 393946618117299885005021)
                ·
                  refine ⟨147729981793987456876883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 393946618117299885005021 147729981793987456876883)
                  ·
                    rfl

theorem cell20_323666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 4, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 4, 1, 3, 1, 3].length) (baseStart_323666 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_323666 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_323666 prefixEnd_323666 := by exact prefixLift 323666
  have htrace : WordTrace (prefixWord ++ tailWord_323666) baseStart_323666 baseEnd_323666 := by
    simpa [prefixWord, tailWord_323666, baseEnd_323666] using wordTrace_append hprefix tailTrace_323666
  have hstable : (prefixWord ++ tailWord_323666).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_323666).length < 2 ^ (prefixWord ++ tailWord_323666).sum := by decide
  have hdescent : baseEnd_323666 < baseStart_323666 := by decide
  rcases family_descends (prefixWord ++ tailWord_323666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_323690 : List Nat := [3, 1, 3, 2, 3, 2, 1, 3, 2]
def baseStart_323690 : Nat := 118140960795 + 323690 * 2 ^ 59
def prefixEnd_323690 : Nat := 4983230072969 + 3 ^ 40 * 323690 * 2
def baseEnd_323690 : Nat := 147740936047950040076785

theorem tailTrace_323690 : CollatzResearch.WordTrace tailWord_323690 prefixEnd_323690 147740936047950040076785 := by
  unfold tailWord_323690
  simp only [CollatzResearch.WordTrace]
  refine ⟨2951486049333471673974131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7870629464889257797264349 2951486049333471673974131)
  ·
    refine ⟨4427229074000207510961197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2951486049333471673974131 4427229074000207510961197)
    ·
      refine ⟨1660210902750077816610449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4427229074000207510961197 1660210902750077816610449)
      ·
        refine ⟨1245158177062558362457837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1660210902750077816610449 1245158177062558362457837)
        ·
          refine ⟨466934316398459385921689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1245158177062558362457837 466934316398459385921689)
          ·
            refine ⟨350200737298844539441267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 466934316398459385921689 350200737298844539441267)
            ·
              refine ⟨525301105948266809161901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 350200737298844539441267 525301105948266809161901)
              ·
                refine ⟨196987914730600053435713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 525301105948266809161901 196987914730600053435713)
                ·
                  refine ⟨147740936047950040076785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 196987914730600053435713 147740936047950040076785)
                  ·
                    rfl

theorem cell20_323690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 3, 2, 1, 3, 2].length) (baseStart_323690 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_323690 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_323690 prefixEnd_323690 := by exact prefixLift 323690
  have htrace : WordTrace (prefixWord ++ tailWord_323690) baseStart_323690 baseEnd_323690 := by
    simpa [prefixWord, tailWord_323690, baseEnd_323690] using wordTrace_append hprefix tailTrace_323690
  have hstable : (prefixWord ++ tailWord_323690).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_323690).length < 2 ^ (prefixWord ++ tailWord_323690).sum := by decide
  have hdescent : baseEnd_323690 < baseStart_323690 := by decide
  rcases family_descends (prefixWord ++ tailWord_323690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_323715 : List Nat := [1, 1, 1, 3, 3, 3, 3, 1, 4]
def baseStart_323715 : Nat := 118140960795 + 323715 * 2 ^ 59
def prefixEnd_323715 : Nat := 4983230072969 + 3 ^ 40 * 323715 * 2
def baseEnd_323715 : Nat := 147752346729161064243349

theorem tailTrace_323715 : CollatzResearch.WordTrace tailWord_323715 prefixEnd_323715 147752346729161064243349 := by
  unfold tailWord_323715
  simp only [CollatzResearch.WordTrace]
  refine ⟨11806856022243315965556599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7871237348162210643704399 11806856022243315965556599)
  ·
    refine ⟨17710284033364973948334899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11806856022243315965556599 17710284033364973948334899)
    ·
      refine ⟨26565426050047460922502349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17710284033364973948334899 26565426050047460922502349)
      ·
        refine ⟨9962034768767797845938381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26565426050047460922502349 9962034768767797845938381)
        ·
          refine ⟨3735763038287924192226893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9962034768767797845938381 3735763038287924192226893)
          ·
            refine ⟨1400911139357971572085085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3735763038287924192226893 1400911139357971572085085)
            ·
              refine ⟨525341677259239339531907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1400911139357971572085085 525341677259239339531907)
              ·
                refine ⟨788012515888859009297861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 525341677259239339531907 788012515888859009297861)
                ·
                  refine ⟨147752346729161064243349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 788012515888859009297861 147752346729161064243349)
                  ·
                    rfl

theorem cell20_323715_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 3, 1, 4].length) (baseStart_323715 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_323715 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_323715 prefixEnd_323715 := by exact prefixLift 323715
  have htrace : WordTrace (prefixWord ++ tailWord_323715) baseStart_323715 baseEnd_323715 := by
    simpa [prefixWord, tailWord_323715, baseEnd_323715] using wordTrace_append hprefix tailTrace_323715
  have hstable : (prefixWord ++ tailWord_323715).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_323715).length < 2 ^ (prefixWord ++ tailWord_323715).sum := by decide
  have hdescent : baseEnd_323715 < baseStart_323715 := by decide
  rcases family_descends (prefixWord ++ tailWord_323715) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_323722 : List Nat := [3, 1, 2, 3, 1, 2, 1, 7]
def baseStart_323722 : Nat := 118140960795 + 323722 * 2 ^ 59
def prefixEnd_323722 : Nat := 4983230072969 + 3 ^ 40 * 323722 * 2
def baseEnd_323722 : Nat := 49251847239966717003329

theorem tailTrace_323722 : CollatzResearch.WordTrace tailWord_323722 prefixEnd_323722 49251847239966717003329 := by
  unfold tailWord_323722
  simp only [CollatzResearch.WordTrace]
  refine ⟨2951777833304489040265355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7871407555478637440707613 2951777833304489040265355)
  ·
    refine ⟨4427666749956733560398033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2951777833304489040265355 4427666749956733560398033)
    ·
      refine ⟨3320750062467550170298525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4427666749956733560398033 3320750062467550170298525)
      ·
        refine ⟨1245281273425331313861947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3320750062467550170298525 1245281273425331313861947)
        ·
          refine ⟨1867921910137996970792921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1245281273425331313861947 1867921910137996970792921)
          ·
            refine ⟨1400941432603497728094691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1867921910137996970792921 1400941432603497728094691)
            ·
              refine ⟨2101412148905246592142037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1400941432603497728094691 2101412148905246592142037)
              ·
                refine ⟨49251847239966717003329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2101412148905246592142037 49251847239966717003329)
                ·
                  rfl

theorem cell20_323722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 1, 7].length) (baseStart_323722 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_323722 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_323722 prefixEnd_323722 := by exact prefixLift 323722
  have htrace : WordTrace (prefixWord ++ tailWord_323722) baseStart_323722 baseEnd_323722 := by
    simpa [prefixWord, tailWord_323722, baseEnd_323722] using wordTrace_append hprefix tailTrace_323722
  have hstable : (prefixWord ++ tailWord_323722).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_323722).length < 2 ^ (prefixWord ++ tailWord_323722).sum := by decide
  have hdescent : baseEnd_323722 < baseStart_323722 := by decide
  rcases family_descends (prefixWord ++ tailWord_323722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_323808 : List Nat := [2, 1, 1, 3, 1, 3, 4, 3, 2]
def baseStart_323808 : Nat := 118140960795 + 323808 * 2 ^ 59
def prefixEnd_323808 : Nat := 4983230072969 + 3 ^ 40 * 323808 * 2
def baseEnd_323808 : Nat := 147794794463266074142969

theorem tailTrace_323808 : CollatzResearch.WordTrace tailWord_323808 prefixEnd_323808 147794794463266074142969 := by
  unfold tailWord_323808
  simp only [CollatzResearch.WordTrace]
  refine ⟨5905124005453196424346039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7873498673937595232461385 5905124005453196424346039)
  ·
    refine ⟨8857686008179794636519059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5905124005453196424346039 8857686008179794636519059)
    ·
      refine ⟨13286529012269691954778589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8857686008179794636519059 13286529012269691954778589)
      ·
        refine ⟨4982448379601134483041971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13286529012269691954778589 4982448379601134483041971)
        ·
          refine ⟨7473672569401701724562957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4982448379601134483041971 7473672569401701724562957)
          ·
            refine ⟨2802627213525638146711109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7473672569401701724562957 2802627213525638146711109)
            ·
              refine ⟨525492602536057152508333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2802627213525638146711109 525492602536057152508333)
              ·
                refine ⟨197059725951021432190625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 525492602536057152508333 197059725951021432190625)
                ·
                  refine ⟨147794794463266074142969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 197059725951021432190625 147794794463266074142969)
                  ·
                    rfl

theorem cell20_323808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 4, 3, 2].length) (baseStart_323808 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_323808 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_323808 prefixEnd_323808 := by exact prefixLift 323808
  have htrace : WordTrace (prefixWord ++ tailWord_323808) baseStart_323808 baseEnd_323808 := by
    simpa [prefixWord, tailWord_323808, baseEnd_323808] using wordTrace_append hprefix tailTrace_323808
  have hstable : (prefixWord ++ tailWord_323808).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_323808).length < 2 ^ (prefixWord ++ tailWord_323808).sum := by decide
  have hdescent : baseEnd_323808 < baseStart_323808 := by decide
  rcases family_descends (prefixWord ++ tailWord_323808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_323812 : List Nat := [2, 3, 1, 1, 1, 2, 1, 1, 8]
def baseStart_323812 : Nat := 118140960795 + 323812 * 2 ^ 59
def prefixEnd_323812 : Nat := 4983230072969 + 3 ^ 40 * 323812 * 2
def baseEnd_323812 : Nat := 147796620172259838009619

theorem tailTrace_323812 : CollatzResearch.WordTrace tailWord_323812 prefixEnd_323812 147796620172259838009619 := by
  unfold tailWord_323812
  simp only [CollatzResearch.WordTrace]
  refine ⟨5905196951445950765918845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7873595935261267687891793 5905196951445950765918845)
  ·
    refine ⟨2214448856792231537219567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5905196951445950765918845 2214448856792231537219567)
    ·
      refine ⟨3321673285188347305829351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2214448856792231537219567 3321673285188347305829351)
      ·
        refine ⟨4982509927782520958744027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3321673285188347305829351 4982509927782520958744027)
        ·
          refine ⟨7473764891673781438116041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4982509927782520958744027 7473764891673781438116041)
          ·
            refine ⟨5605323668755336078587031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7473764891673781438116041 5605323668755336078587031)
            ·
              refine ⟨8407985503133004117880547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5605323668755336078587031 8407985503133004117880547)
              ·
                refine ⟨12611978254699506176820821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8407985503133004117880547 12611978254699506176820821)
                ·
                  refine ⟨147796620172259838009619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 12611978254699506176820821 147796620172259838009619)
                  ·
                    rfl

theorem cell20_323812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 1, 1, 8].length) (baseStart_323812 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_323812 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_323812 prefixEnd_323812 := by exact prefixLift 323812
  have htrace : WordTrace (prefixWord ++ tailWord_323812) baseStart_323812 baseEnd_323812 := by
    simpa [prefixWord, tailWord_323812, baseEnd_323812] using wordTrace_append hprefix tailTrace_323812
  have hstable : (prefixWord ++ tailWord_323812).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_323812).length < 2 ^ (prefixWord ++ tailWord_323812).sum := by decide
  have hdescent : baseEnd_323812 < baseStart_323812 := by decide
  rcases family_descends (prefixWord ++ tailWord_323812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_323819 : List Nat := [1, 1, 1, 1, 2, 5, 9]
def baseStart_323819 : Nat := 118140960795 + 323819 * 2 ^ 59
def prefixEnd_323819 : Nat := 4983230072969 + 3 ^ 40 * 323819 * 2
def baseEnd_323819 : Nat := 16422201684777658308473

theorem tailTrace_323819 : CollatzResearch.WordTrace tailWord_323819 prefixEnd_323819 16422201684777658308473 := by
  unfold tailWord_323819
  simp only [CollatzResearch.WordTrace]
  refine ⟨11810649213866541727342511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7873766142577694484895007 11810649213866541727342511)
  ·
    refine ⟨17715973820799812591013767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11810649213866541727342511 17715973820799812591013767)
    ·
      refine ⟨26573960731199718886520651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17715973820799812591013767 26573960731199718886520651)
      ·
        refine ⟨39860941096799578329780977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26573960731199718886520651 39860941096799578329780977)
        ·
          refine ⟨29895705822599683747335733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39860941096799578329780977 29895705822599683747335733)
          ·
            refine ⟨2802722420868720351312725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 29895705822599683747335733 2802722420868720351312725)
            ·
              refine ⟨16422201684777658308473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 2802722420868720351312725 16422201684777658308473)
              ·
                rfl

theorem cell20_323819_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 9].length) (baseStart_323819 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_323819 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_323819 prefixEnd_323819 := by exact prefixLift 323819
  have htrace : WordTrace (prefixWord ++ tailWord_323819) baseStart_323819 baseEnd_323819 := by
    simpa [prefixWord, tailWord_323819, baseEnd_323819] using wordTrace_append hprefix tailTrace_323819
  have hstable : (prefixWord ++ tailWord_323819).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_323819).length < 2 ^ (prefixWord ++ tailWord_323819).sum := by decide
  have hdescent : baseEnd_323819 < baseStart_323819 := by decide
  rcases family_descends (prefixWord ++ tailWord_323819) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_323863 : List Nat := [1, 1, 3, 4, 1, 4, 1, 3, 2]
def baseStart_323863 : Nat := 118140960795 + 323863 * 2 ^ 59
def prefixEnd_323863 : Nat := 4983230072969 + 3 ^ 40 * 323863 * 2
def baseEnd_323863 : Nat := 147819897961930327309411

theorem tailTrace_323863 : CollatzResearch.WordTrace tailWord_323863 prefixEnd_323863 147819897961930327309411 := by
  unfold tailWord_323863
  simp only [CollatzResearch.WordTrace]
  refine ⟨11812254025707137241944243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7874836017138091494629495 11812254025707137241944243)
  ·
    refine ⟨17718381038560705862916365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11812254025707137241944243 17718381038560705862916365)
    ·
      refine ⟨6644392889460264698593637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17718381038560705862916365 6644392889460264698593637)
      ·
        refine ⟨1245823666773799630986307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6644392889460264698593637 1245823666773799630986307)
        ·
          refine ⟨1868735500160699446479461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1245823666773799630986307 1868735500160699446479461)
          ·
            refine ⟨350387906280131146214899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1868735500160699446479461 350387906280131146214899)
            ·
              refine ⟨525581859420196719322349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 350387906280131146214899 525581859420196719322349)
              ·
                refine ⟨197093197282573769745881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 525581859420196719322349 197093197282573769745881)
                ·
                  refine ⟨147819897961930327309411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 197093197282573769745881 147819897961930327309411)
                  ·
                    rfl

theorem cell20_323863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 4, 1, 3, 2].length) (baseStart_323863 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_323863 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_323863 prefixEnd_323863 := by exact prefixLift 323863
  have htrace : WordTrace (prefixWord ++ tailWord_323863) baseStart_323863 baseEnd_323863 := by
    simpa [prefixWord, tailWord_323863, baseEnd_323863] using wordTrace_append hprefix tailTrace_323863
  have hstable : (prefixWord ++ tailWord_323863).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_323863).length < 2 ^ (prefixWord ++ tailWord_323863).sum := by decide
  have hdescent : baseEnd_323863 < baseStart_323863 := by decide
  rcases family_descends (prefixWord ++ tailWord_323863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_323870 : List Nat := [4, 3, 2, 1, 1, 3, 6]
def baseStart_323870 : Nat := 118140960795 + 323870 * 2 ^ 59
def prefixEnd_323870 : Nat := 4983230072969 + 3 ^ 40 * 323870 * 2
def baseEnd_323870 : Nat := 16424788105852157119561

theorem tailTrace_323870 : CollatzResearch.WordTrace tailWord_323870 prefixEnd_323870 16424788105852157119561 := by
  unfold tailWord_323870
  simp only [CollatzResearch.WordTrace]
  refine ⟨1476563667085222179681133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 7875006224454518291632709 1476563667085222179681133)
  ·
    refine ⟨553711375156958317380425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1476563667085222179681133 553711375156958317380425)
    ·
      refine ⟨415283531367718738035319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 553711375156958317380425 415283531367718738035319)
      ·
        refine ⟨622925297051578107052979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 415283531367718738035319 622925297051578107052979)
        ·
          refine ⟨934387945577367160579469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 622925297051578107052979 934387945577367160579469)
          ·
            refine ⟨350395479591512685217301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 934387945577367160579469 350395479591512685217301)
            ·
              refine ⟨16424788105852157119561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 350395479591512685217301 16424788105852157119561)
              ·
                rfl

theorem cell20_323870_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 3, 6].length) (baseStart_323870 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_323870 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_323870 prefixEnd_323870 := by exact prefixLift 323870
  have htrace : WordTrace (prefixWord ++ tailWord_323870) baseStart_323870 baseEnd_323870 := by
    simpa [prefixWord, tailWord_323870, baseEnd_323870] using wordTrace_append hprefix tailTrace_323870
  have hstable : (prefixWord ++ tailWord_323870).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_323870).length < 2 ^ (prefixWord ++ tailWord_323870).sum := by decide
  have hdescent : baseEnd_323870 < baseStart_323870 := by decide
  rcases family_descends (prefixWord ++ tailWord_323870) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_323874 : List Nat := [3, 3, 1, 1, 3, 1, 8]
def baseStart_323874 : Nat := 118140960795 + 323874 * 2 ^ 59
def prefixEnd_323874 : Nat := 4983230072969 + 3 ^ 40 * 323874 * 2
def baseEnd_323874 : Nat := 16424990962407019771411

theorem tailTrace_323874 : CollatzResearch.WordTrace tailWord_323874 prefixEnd_323874 16424990962407019771411 := by
  unfold tailWord_323874
  simp only [CollatzResearch.WordTrace]
  refine ⟨2953163807166821530148669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7875103485778190747063117 2953163807166821530148669)
  ·
    refine ⟨1107436427687558073805751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2953163807166821530148669 1107436427687558073805751)
    ·
      refine ⟨1661154641531337110708627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1107436427687558073805751 1661154641531337110708627)
      ·
        refine ⟨2491731962297005666062941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1661154641531337110708627 2491731962297005666062941)
        ·
          refine ⟨934399485861377124773603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2491731962297005666062941 934399485861377124773603)
          ·
            refine ⟨1401599228792065687160405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 934399485861377124773603 1401599228792065687160405)
            ·
              refine ⟨16424990962407019771411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1401599228792065687160405 16424990962407019771411)
              ·
                rfl

theorem cell20_323874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 8].length) (baseStart_323874 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_323874 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_323874 prefixEnd_323874 := by exact prefixLift 323874
  have htrace : WordTrace (prefixWord ++ tailWord_323874) baseStart_323874 baseEnd_323874 := by
    simpa [prefixWord, tailWord_323874, baseEnd_323874] using wordTrace_append hprefix tailTrace_323874
  have hstable : (prefixWord ++ tailWord_323874).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_323874).length < 2 ^ (prefixWord ++ tailWord_323874).sum := by decide
  have hdescent : baseEnd_323874 < baseStart_323874 := by decide
  rcases family_descends (prefixWord ++ tailWord_323874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_323880 : List Nat := [2, 1, 5, 1, 3, 1, 3, 2, 2]
def baseStart_323880 : Nat := 118140960795 + 323880 * 2 ^ 59
def prefixEnd_323880 : Nat := 4983230072969 + 3 ^ 40 * 323880 * 2
def baseEnd_323880 : Nat := 147827657225153823742675

theorem tailTrace_323880 : CollatzResearch.WordTrace tailWord_323880 prefixEnd_323880 147827657225153823742675 := by
  unfold tailWord_323880
  simp only [CollatzResearch.WordTrace]
  refine ⟨5906437033322774572656547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7875249377763699430208729 5906437033322774572656547)
  ·
    refine ⟨8859655549984161858984821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5906437033322774572656547 8859655549984161858984821)
    ·
      refine ⟨830592707811015174279827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 8859655549984161858984821 830592707811015174279827)
      ·
        refine ⟨1245889061716522761419741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 830592707811015174279827 1245889061716522761419741)
        ·
          refine ⟨467208398143696035532403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1245889061716522761419741 467208398143696035532403)
          ·
            refine ⟨700812597215544053298605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 467208398143696035532403 700812597215544053298605)
            ·
              refine ⟨262804723955829019986977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 700812597215544053298605 262804723955829019986977)
              ·
                refine ⟨197103542966871764990233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 262804723955829019986977 197103542966871764990233)
                ·
                  refine ⟨147827657225153823742675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 197103542966871764990233 147827657225153823742675)
                  ·
                    rfl

theorem cell20_323880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 3, 1, 3, 2, 2].length) (baseStart_323880 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_323880 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_323880 prefixEnd_323880 := by exact prefixLift 323880
  have htrace : WordTrace (prefixWord ++ tailWord_323880) baseStart_323880 baseEnd_323880 := by
    simpa [prefixWord, tailWord_323880, baseEnd_323880] using wordTrace_append hprefix tailTrace_323880
  have hstable : (prefixWord ++ tailWord_323880).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_323880).length < 2 ^ (prefixWord ++ tailWord_323880).sum := by decide
  have hdescent : baseEnd_323880 < baseStart_323880 := by decide
  rcases family_descends (prefixWord ++ tailWord_323880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_323888 : List Nat := [2, 1, 1, 1, 2, 2, 2, 5, 4]
def baseStart_323888 : Nat := 118140960795 + 323888 * 2 ^ 59
def prefixEnd_323888 : Nat := 4983230072969 + 3 ^ 40 * 323888 * 2
def baseEnd_323888 : Nat := 147831308643141351475975

theorem tailTrace_323888 : CollatzResearch.WordTrace tailWord_323888 prefixEnd_323888 147831308643141351475975 := by
  unfold tailWord_323888
  simp only [CollatzResearch.WordTrace]
  refine ⟨5906582925308283255802159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7875443900411044341069545 5906582925308283255802159)
  ·
    refine ⟨8859874387962424883703239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5906582925308283255802159 8859874387962424883703239)
    ·
      refine ⟨13289811581943637325554859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8859874387962424883703239 13289811581943637325554859)
      ·
        refine ⟨19934717372915455988332289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13289811581943637325554859 19934717372915455988332289)
        ·
          refine ⟨14951038029686591991249217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19934717372915455988332289 14951038029686591991249217)
          ·
            refine ⟨11213278522264943993436913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14951038029686591991249217 11213278522264943993436913)
            ·
              refine ⟨8409958891698707995077685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11213278522264943993436913 8409958891698707995077685)
              ·
                refine ⟨788433646096753874538533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 8409958891698707995077685 788433646096753874538533)
                ·
                  refine ⟨147831308643141351475975, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 788433646096753874538533 147831308643141351475975)
                  ·
                    rfl

theorem cell20_323888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 2, 5, 4].length) (baseStart_323888 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_323888 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_323888 prefixEnd_323888 := by exact prefixLift 323888
  have htrace : WordTrace (prefixWord ++ tailWord_323888) baseStart_323888 baseEnd_323888 := by
    simpa [prefixWord, tailWord_323888, baseEnd_323888] using wordTrace_append hprefix tailTrace_323888
  have hstable : (prefixWord ++ tailWord_323888).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_323888).length < 2 ^ (prefixWord ++ tailWord_323888).sum := by decide
  have hdescent : baseEnd_323888 < baseStart_323888 := by decide
  rcases family_descends (prefixWord ++ tailWord_323888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_323898 : List Nat := [3, 1, 1, 1, 4, 3, 1, 3, 3]
def baseStart_323898 : Nat := 118140960795 + 323898 * 2 ^ 59
def prefixEnd_323898 : Nat := 4983230072969 + 3 ^ 40 * 323898 * 2
def baseEnd_323898 : Nat := 147835872915625761142601

theorem tailTrace_323898 : CollatzResearch.WordTrace tailWord_323898 prefixEnd_323898 147835872915625761142601 := by
  unfold tailWord_323898
  simp only [CollatzResearch.WordTrace]
  refine ⟨2953382645145084554867087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7875687053720225479645565 2953382645145084554867087)
  ·
    refine ⟨4430073967717626832300631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2953382645145084554867087 4430073967717626832300631)
    ·
      refine ⟨6645110951576440248450947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4430073967717626832300631 6645110951576440248450947)
      ·
        refine ⟨9967666427364660372676421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6645110951576440248450947 9967666427364660372676421)
        ·
          refine ⟨1868937455130873819876829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9967666427364660372676421 1868937455130873819876829)
          ·
            refine ⟨700851545674077682453811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1868937455130873819876829 700851545674077682453811)
            ·
              refine ⟨1051277318511116523680717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 700851545674077682453811 1051277318511116523680717)
              ·
                refine ⟨394228994441668696380269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1051277318511116523680717 394228994441668696380269)
                ·
                  refine ⟨147835872915625761142601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 394228994441668696380269 147835872915625761142601)
                  ·
                    rfl

theorem cell20_323898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 3, 1, 3, 3].length) (baseStart_323898 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_323898 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_323898 prefixEnd_323898 := by exact prefixLift 323898
  have htrace : WordTrace (prefixWord ++ tailWord_323898) baseStart_323898 baseEnd_323898 := by
    simpa [prefixWord, tailWord_323898, baseEnd_323898] using wordTrace_append hprefix tailTrace_323898
  have hstable : (prefixWord ++ tailWord_323898).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_323898).length < 2 ^ (prefixWord ++ tailWord_323898).sum := by decide
  have hdescent : baseEnd_323898 < baseStart_323898 := by decide
  rcases family_descends (prefixWord ++ tailWord_323898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_323932 : List Nat := [2, 2, 4, 3, 1, 1, 2, 2, 3]
def baseStart_323932 : Nat := 118140960795 + 323932 * 2 ^ 59
def prefixEnd_323932 : Nat := 4983230072969 + 3 ^ 40 * 323932 * 2
def baseEnd_323932 : Nat := 147851391442072754009129

theorem tailTrace_323932 : CollatzResearch.WordTrace tailWord_323932 prefixEnd_323932 147851391442072754009129 := by
  unfold tailWord_323932
  simp only [CollatzResearch.WordTrace]
  refine ⟨5907385331228581013103025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7876513774971441350804033 5907385331228581013103025)
  ·
    refine ⟨4430538998421435759827269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5907385331228581013103025 4430538998421435759827269)
    ·
      refine ⟨830726062204019204967613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4430538998421435759827269 830726062204019204967613)
      ·
        refine ⟨311522273326507201862855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 830726062204019204967613 311522273326507201862855)
        ·
          refine ⟨467283409989760802794283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 311522273326507201862855 467283409989760802794283)
          ·
            refine ⟨700925114984641204191425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 467283409989760802794283 700925114984641204191425)
            ·
              refine ⟨525693836238480903143569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 700925114984641204191425 525693836238480903143569)
              ·
                refine ⟨394270377178860677357677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 525693836238480903143569 394270377178860677357677)
                ·
                  refine ⟨147851391442072754009129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 394270377178860677357677 147851391442072754009129)
                  ·
                    rfl

theorem cell20_323932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 1, 1, 2, 2, 3].length) (baseStart_323932 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_323932 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_323932 prefixEnd_323932 := by exact prefixLift 323932
  have htrace : WordTrace (prefixWord ++ tailWord_323932) baseStart_323932 baseEnd_323932 := by
    simpa [prefixWord, tailWord_323932, baseEnd_323932] using wordTrace_append hprefix tailTrace_323932
  have hstable : (prefixWord ++ tailWord_323932).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_323932).length < 2 ^ (prefixWord ++ tailWord_323932).sum := by decide
  have hdescent : baseEnd_323932 < baseStart_323932 := by decide
  rcases family_descends (prefixWord ++ tailWord_323932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_323998 : List Nat := [4, 3, 1, 2, 1, 1, 1, 3, 4]
def baseStart_323998 : Nat := 118140960795 + 323998 * 2 ^ 59
def prefixEnd_323998 : Nat := 4983230072969 + 3 ^ 40 * 323998 * 2
def baseEnd_323998 : Nat := 147881515640469857808859

theorem tailTrace_323998 : CollatzResearch.WordTrace tailWord_323998 prefixEnd_323998 147881515640469857808859 := by
  unfold tailWord_323998
  simp only [CollatzResearch.WordTrace]
  refine ⟨1477147235027256912263581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 7878118586812036865405765 1477147235027256912263581)
  ·
    refine ⟨553930213135221342098843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1477147235027256912263581 553930213135221342098843)
    ·
      refine ⟨830895319702832013148265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 553930213135221342098843 830895319702832013148265)
      ·
        refine ⟨623171489777124009861199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 830895319702832013148265 623171489777124009861199)
        ·
          refine ⟨934757234665686014791799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 623171489777124009861199 934757234665686014791799)
          ·
            refine ⟨1402135851998529022187699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 934757234665686014791799 1402135851998529022187699)
            ·
              refine ⟨2103203777997793533281549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1402135851998529022187699 2103203777997793533281549)
              ·
                refine ⟨788701416749172574980581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2103203777997793533281549 788701416749172574980581)
                ·
                  refine ⟨147881515640469857808859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 788701416749172574980581 147881515640469857808859)
                  ·
                    rfl

theorem cell20_323998_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 1, 3, 4].length) (baseStart_323998 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_323998 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_323998 prefixEnd_323998 := by exact prefixLift 323998
  have htrace : WordTrace (prefixWord ++ tailWord_323998) baseStart_323998 baseEnd_323998 := by
    simpa [prefixWord, tailWord_323998, baseEnd_323998] using wordTrace_append hprefix tailTrace_323998
  have hstable : (prefixWord ++ tailWord_323998).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_323998).length < 2 ^ (prefixWord ++ tailWord_323998).sum := by decide
  have hdescent : baseEnd_323998 < baseStart_323998 := by decide
  rcases family_descends (prefixWord ++ tailWord_323998) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_324008 : List Nat := [2, 1, 6, 1, 1, 2, 3, 1, 3]
def baseStart_324008 : Nat := 118140960795 + 324008 * 2 ^ 59
def prefixEnd_324008 : Nat := 4983230072969 + 3 ^ 40 * 324008 * 2
def baseEnd_324008 : Nat := 147886079912954267475485

theorem tailTrace_324008 : CollatzResearch.WordTrace tailWord_324008 prefixEnd_324008 147886079912954267475485 := by
  unfold tailWord_324008
  simp only [CollatzResearch.WordTrace]
  refine ⟨5908771305090913502986339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7878361740121218003981785 5908771305090913502986339)
  ·
    refine ⟨8863156957636370254479509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5908771305090913502986339 8863156957636370254479509)
    ·
      refine ⟨415460482389204855678727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 8863156957636370254479509 415460482389204855678727)
      ·
        refine ⟨623190723583807283518091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 415460482389204855678727 623190723583807283518091)
        ·
          refine ⟨934786085375710925277137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 623190723583807283518091 934786085375710925277137)
          ·
            refine ⟨701089564031783193957853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 934786085375710925277137 701089564031783193957853)
            ·
              refine ⟨262908586511918697734195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 701089564031783193957853 262908586511918697734195)
              ·
                refine ⟨394362879767878046601293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 262908586511918697734195 394362879767878046601293)
                ·
                  refine ⟨147886079912954267475485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 394362879767878046601293 147886079912954267475485)
                  ·
                    rfl

theorem cell20_324008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 2, 3, 1, 3].length) (baseStart_324008 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_324008 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_324008 prefixEnd_324008 := by exact prefixLift 324008
  have htrace : WordTrace (prefixWord ++ tailWord_324008) baseStart_324008 baseEnd_324008 := by
    simpa [prefixWord, tailWord_324008, baseEnd_324008] using wordTrace_append hprefix tailTrace_324008
  have hstable : (prefixWord ++ tailWord_324008).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_324008).length < 2 ^ (prefixWord ++ tailWord_324008).sum := by decide
  have hdescent : baseEnd_324008 < baseStart_324008 := by decide
  rcases family_descends (prefixWord ++ tailWord_324008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_324053 : List Nat := [1, 3, 2, 3, 1, 3, 3, 2, 2]
def baseStart_324053 : Nat := 118140960795 + 324053 * 2 ^ 59
def prefixEnd_324053 : Nat := 4983230072969 + 3 ^ 40 * 324053 * 2
def baseEnd_324053 : Nat := 147906619139134110975301

theorem tailTrace_324053 : CollatzResearch.WordTrace tailWord_324053 prefixEnd_324053 147906619139134110975301 := by
  unfold tailWord_324053
  simp only [CollatzResearch.WordTrace]
  refine ⟨11819183895018799691360813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7879455930012533127573875 11819183895018799691360813)
  ·
    refine ⟨4432193960632049884260305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11819183895018799691360813 4432193960632049884260305)
    ·
      refine ⟨3324145470474037413195229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4432193960632049884260305 3324145470474037413195229)
      ·
        refine ⟨1246554551427764029948211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3324145470474037413195229 1246554551427764029948211)
        ·
          refine ⟨1869831827141646044922317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1246554551427764029948211 1869831827141646044922317)
          ·
            refine ⟨701186935178117266845869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1869831827141646044922317 701186935178117266845869)
            ·
              refine ⟨262945100691793975067201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 701186935178117266845869 262945100691793975067201)
              ·
                refine ⟨197208825518845481300401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 262945100691793975067201 197208825518845481300401)
                ·
                  refine ⟨147906619139134110975301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 197208825518845481300401 147906619139134110975301)
                  ·
                    rfl

theorem cell20_324053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 3, 3, 2, 2].length) (baseStart_324053 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_324053 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_324053 prefixEnd_324053 := by exact prefixLift 324053
  have htrace : WordTrace (prefixWord ++ tailWord_324053) baseStart_324053 baseEnd_324053 := by
    simpa [prefixWord, tailWord_324053, baseEnd_324053] using wordTrace_append hprefix tailTrace_324053
  have hstable : (prefixWord ++ tailWord_324053).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_324053).length < 2 ^ (prefixWord ++ tailWord_324053).sum := by decide
  have hdescent : baseEnd_324053 < baseStart_324053 := by decide
  rcases family_descends (prefixWord ++ tailWord_324053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_324095 : List Nat := [1, 1, 2, 2, 1, 2, 4, 5, 2]
def baseStart_324095 : Nat := 118140960795 + 324095 * 2 ^ 59
def prefixEnd_324095 : Nat := 4983230072969 + 3 ^ 40 * 324095 * 2
def baseEnd_324095 : Nat := 147925789083568631575129

theorem tailTrace_324095 : CollatzResearch.WordTrace tailWord_324095 prefixEnd_324095 147925789083568631575129 := by
  unfold tailWord_324095
  simp only [CollatzResearch.WordTrace]
  refine ⟨11820715760866640864389739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7880477173911093909593159 11820715760866640864389739)
  ·
    refine ⟨17731073641299961296584609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11820715760866640864389739 17731073641299961296584609)
    ·
      refine ⟨13298305230974970972438457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17731073641299961296584609 13298305230974970972438457)
      ·
        refine ⟨9973728923231228229328843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13298305230974970972438457 9973728923231228229328843)
        ·
          refine ⟨14960593384846842343993265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9973728923231228229328843 14960593384846842343993265)
          ·
            refine ⟨11220445038635131757994949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14960593384846842343993265 11220445038635131757994949)
            ·
              refine ⟨2103833444744087204624053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11220445038635131757994949 2103833444744087204624053)
              ·
                refine ⟨197234385444758175433505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2103833444744087204624053 197234385444758175433505)
                ·
                  refine ⟨147925789083568631575129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 197234385444758175433505 147925789083568631575129)
                  ·
                    rfl

theorem cell20_324095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 4, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 4, 5, 2].length) (baseStart_324095 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_324095 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_324095 prefixEnd_324095 := by exact prefixLift 324095
  have htrace : WordTrace (prefixWord ++ tailWord_324095) baseStart_324095 baseEnd_324095 := by
    simpa [prefixWord, tailWord_324095, baseEnd_324095] using wordTrace_append hprefix tailTrace_324095
  have hstable : (prefixWord ++ tailWord_324095).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_324095).length < 2 ^ (prefixWord ++ tailWord_324095).sum := by decide
  have hdescent : baseEnd_324095 < baseStart_324095 := by decide
  rcases family_descends (prefixWord ++ tailWord_324095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_324171 : List Nat := [1, 1, 1, 1, 3, 1, 6, 4, 2]
def baseStart_324171 : Nat := 118140960795 + 324171 * 2 ^ 59
def prefixEnd_324171 : Nat := 4983230072969 + 3 ^ 40 * 324171 * 2
def baseEnd_324171 : Nat := 147960477554450145041485

theorem tailTrace_324171 : CollatzResearch.WordTrace tailWord_324171 prefixEnd_324171 147960477554450145041485 := by
  unfold tailWord_324171
  simp only [CollatzResearch.WordTrace]
  refine ⟨11823487708591305844156367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7882325139060870562770911 11823487708591305844156367)
  ·
    refine ⟨17735231562886958766234551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11823487708591305844156367 17735231562886958766234551)
    ·
      refine ⟨26602847344330438149351827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17735231562886958766234551 26602847344330438149351827)
      ·
        refine ⟨39904271016495657224027741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26602847344330438149351827 39904271016495657224027741)
        ·
          refine ⟨14964101631185871459010403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 39904271016495657224027741 14964101631185871459010403)
          ·
            refine ⟨22446152446778807188515605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14964101631185871459010403 22446152446778807188515605)
            ·
              refine ⟨1052163395942756586961669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 22446152446778807188515605 1052163395942756586961669)
              ·
                refine ⟨197280636739266860055313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1052163395942756586961669 197280636739266860055313)
                ·
                  refine ⟨147960477554450145041485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 197280636739266860055313 147960477554450145041485)
                  ·
                    rfl

theorem cell20_324171_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 6, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 6, 4, 2].length) (baseStart_324171 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_324171 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_324171 prefixEnd_324171 := by exact prefixLift 324171
  have htrace : WordTrace (prefixWord ++ tailWord_324171) baseStart_324171 baseEnd_324171 := by
    simpa [prefixWord, tailWord_324171, baseEnd_324171] using wordTrace_append hprefix tailTrace_324171
  have hstable : (prefixWord ++ tailWord_324171).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_324171).length < 2 ^ (prefixWord ++ tailWord_324171).sum := by decide
  have hdescent : baseEnd_324171 < baseStart_324171 := by decide
  rcases family_descends (prefixWord ++ tailWord_324171) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_324192 : List Nat := [2, 1, 1, 3, 2, 1, 4, 2, 4]
def baseStart_324192 : Nat := 118140960795 + 324192 * 2 ^ 59
def prefixEnd_324192 : Nat := 4983230072969 + 3 ^ 40 * 324192 * 2
def baseEnd_324192 : Nat := 147970062526667405341399

theorem tailTrace_324192 : CollatzResearch.WordTrace tailWord_324192 prefixEnd_324192 147970062526667405341399 := by
  unfold tailWord_324192
  simp only [CollatzResearch.WordTrace]
  refine ⟨5912126820757613215335415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7882835761010150953780553 5912126820757613215335415)
  ·
    refine ⟨8868190231136419823003123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5912126820757613215335415 8868190231136419823003123)
    ·
      refine ⟨13302285346704629734504685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8868190231136419823003123 13302285346704629734504685)
      ·
        refine ⟨4988357005014236150439257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13302285346704629734504685 4988357005014236150439257)
        ·
          refine ⟨3741267753760677112829443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4988357005014236150439257 3741267753760677112829443)
          ·
            refine ⟨5611901630641015669244165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3741267753760677112829443 5611901630641015669244165)
            ·
              refine ⟨1052231555745190437983281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5611901630641015669244165 1052231555745190437983281)
              ·
                refine ⟨789173666808892828487461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1052231555745190437983281 789173666808892828487461)
                ·
                  refine ⟨147970062526667405341399, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 789173666808892828487461 147970062526667405341399)
                  ·
                    rfl

theorem cell20_324192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 4, 2, 4].length) (baseStart_324192 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_324192 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_324192 prefixEnd_324192 := by exact prefixLift 324192
  have htrace : WordTrace (prefixWord ++ tailWord_324192) baseStart_324192 baseEnd_324192 := by
    simpa [prefixWord, tailWord_324192, baseEnd_324192] using wordTrace_append hprefix tailTrace_324192
  have hstable : (prefixWord ++ tailWord_324192).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_324192).length < 2 ^ (prefixWord ++ tailWord_324192).sum := by decide
  have hdescent : baseEnd_324192 < baseStart_324192 := by decide
  rcases family_descends (prefixWord ++ tailWord_324192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_324205 : List Nat := [1, 5, 1, 1, 3, 3, 1, 3, 2]
def baseStart_324205 : Nat := 118140960795 + 324205 * 2 ^ 59
def prefixEnd_324205 : Nat := 4983230072969 + 3 ^ 40 * 324205 * 2
def baseEnd_324205 : Nat := 147975996080897137908013

theorem tailTrace_324205 : CollatzResearch.WordTrace tailWord_324205 prefixEnd_324205 147975996080897137908013 := by
  unfold tailWord_324205
  simp only [CollatzResearch.WordTrace]
  refine ⟨11824727790468129650894069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7883151860312086433929379 11824727790468129650894069)
  ·
    refine ⟨1108568230356387154771319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 11824727790468129650894069 1108568230356387154771319)
    ·
      refine ⟨1662852345534580732156979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1108568230356387154771319 1662852345534580732156979)
      ·
        refine ⟨2494278518301871098235469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1662852345534580732156979 2494278518301871098235469)
        ·
          refine ⟨935354444363201661838301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2494278518301871098235469 935354444363201661838301)
          ·
            refine ⟨350757916636200623189363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 935354444363201661838301 350757916636200623189363)
            ·
              refine ⟨526136874954300934784045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 350757916636200623189363 526136874954300934784045)
              ·
                refine ⟨197301328107862850544017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 526136874954300934784045 197301328107862850544017)
                ·
                  refine ⟨147975996080897137908013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 197301328107862850544017 147975996080897137908013)
                  ·
                    rfl

theorem cell20_324205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 3, 1, 3, 2].length) (baseStart_324205 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_324205 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_324205 prefixEnd_324205 := by exact prefixLift 324205
  have htrace : WordTrace (prefixWord ++ tailWord_324205) baseStart_324205 baseEnd_324205 := by
    simpa [prefixWord, tailWord_324205, baseEnd_324205] using wordTrace_append hprefix tailTrace_324205
  have hstable : (prefixWord ++ tailWord_324205).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_324205).length < 2 ^ (prefixWord ++ tailWord_324205).sum := by decide
  have hdescent : baseEnd_324205 < baseStart_324205 := by decide
  rcases family_descends (prefixWord ++ tailWord_324205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_324251 : List Nat := [1, 1, 1, 1, 1, 1, 2, 2, 10]
def baseStart_324251 : Nat := 118140960795 + 324251 * 2 ^ 59
def prefixEnd_324251 : Nat := 4983230072969 + 3 ^ 40 * 324251 * 2
def baseEnd_324251 : Nat := 147996991734325422374491

theorem tailTrace_324251 : CollatzResearch.WordTrace tailWord_324251 prefixEnd_324251 147996991734325422374491 := by
  unfold tailWord_324251
  simp only [CollatzResearch.WordTrace]
  refine ⟨11826405548301479507068607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7884270365534319671379071 11826405548301479507068607)
  ·
    refine ⟨17739608322452219260602911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11826405548301479507068607 17739608322452219260602911)
    ·
      refine ⟨26609412483678328890904367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17739608322452219260602911 26609412483678328890904367)
      ·
        refine ⟨39914118725517493336356551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26609412483678328890904367 39914118725517493336356551)
        ·
          refine ⟨59871178088276240004534827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39914118725517493336356551 59871178088276240004534827)
          ·
            refine ⟨89806767132414360006802241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59871178088276240004534827 89806767132414360006802241)
            ·
              refine ⟨67355075349310770005101681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 89806767132414360006802241 67355075349310770005101681)
              ·
                refine ⟨50516306511983077503826261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 67355075349310770005101681 50516306511983077503826261)
                ·
                  refine ⟨147996991734325422374491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 50516306511983077503826261 147996991734325422374491)
                  ·
                    rfl

theorem cell20_324251_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 10].length) (baseStart_324251 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_324251 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_324251 prefixEnd_324251 := by exact prefixLift 324251
  have htrace : WordTrace (prefixWord ++ tailWord_324251) baseStart_324251 baseEnd_324251 := by
    simpa [prefixWord, tailWord_324251, baseEnd_324251] using wordTrace_append hprefix tailTrace_324251
  have hstable : (prefixWord ++ tailWord_324251).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_324251).length < 2 ^ (prefixWord ++ tailWord_324251).sum := by decide
  have hdescent : baseEnd_324251 < baseStart_324251 := by decide
  rcases family_descends (prefixWord ++ tailWord_324251) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_324254 : List Nat := [4, 3, 1, 1, 1, 1, 1, 8]
def baseStart_324254 : Nat := 118140960795 + 324254 * 2 ^ 59
def prefixEnd_324254 : Nat := 4983230072969 + 3 ^ 40 * 324254 * 2
def baseEnd_324254 : Nat := 49332787005356915091493

theorem tailTrace_324254 : CollatzResearch.WordTrace tailWord_324254 prefixEnd_324254 49332787005356915091493 := by
  unfold tailWord_324254
  simp only [CollatzResearch.WordTrace]
  refine ⟨1478314370911326377428477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 7884343311527074012951877 1478314370911326377428477)
  ·
    refine ⟨554367889091747391535679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1478314370911326377428477 554367889091747391535679)
    ·
      refine ⟨831551833637621087303519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 554367889091747391535679 831551833637621087303519)
      ·
        refine ⟨1247327750456431630955279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 831551833637621087303519 1247327750456431630955279)
        ·
          refine ⟨1870991625684647446432919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1247327750456431630955279 1870991625684647446432919)
          ·
            refine ⟨2806487438526971169649379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1870991625684647446432919 2806487438526971169649379)
            ·
              refine ⟨4209731157790456754474069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2806487438526971169649379 4209731157790456754474069)
              ·
                refine ⟨49332787005356915091493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 4209731157790456754474069 49332787005356915091493)
                ·
                  rfl

theorem cell20_324254_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 1, 8].length) (baseStart_324254 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_324254 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_324254 prefixEnd_324254 := by exact prefixLift 324254
  have htrace : WordTrace (prefixWord ++ tailWord_324254) baseStart_324254 baseEnd_324254 := by
    simpa [prefixWord, tailWord_324254, baseEnd_324254] using wordTrace_append hprefix tailTrace_324254
  have hstable : (prefixWord ++ tailWord_324254).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_324254).length < 2 ^ (prefixWord ++ tailWord_324254).sum := by decide
  have hdescent : baseEnd_324254 < baseStart_324254 := by decide
  rcases family_descends (prefixWord ++ tailWord_324254) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_324292 : List Nat := [2, 3, 3, 1, 1, 2, 3, 5]
def baseStart_324292 : Nat := 118140960795 + 324292 * 2 ^ 59
def prefixEnd_324292 : Nat := 4983230072969 + 3 ^ 40 * 324292 * 2
def baseEnd_324292 : Nat := 49338568417170500669219

theorem tailTrace_324292 : CollatzResearch.WordTrace tailWord_324292 prefixEnd_324292 49338568417170500669219 := by
  unfold tailWord_324292
  simp only [CollatzResearch.WordTrace]
  refine ⟨5913950470576471754655565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7885267294101962339540753 5913950470576471754655565)
  ·
    refine ⟨2217731426466176907995837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5913950470576471754655565 2217731426466176907995837)
    ·
      refine ⟨831649284924816340498439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2217731426466176907995837 831649284924816340498439)
      ·
        refine ⟨1247473927387224510747659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 831649284924816340498439 1247473927387224510747659)
        ·
          refine ⟨1871210891080836766121489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1247473927387224510747659 1871210891080836766121489)
          ·
            refine ⟨1403408168310627574591117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1871210891080836766121489 1403408168310627574591117)
            ·
              refine ⟨526278063116485340471669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1403408168310627574591117 526278063116485340471669)
              ·
                refine ⟨49338568417170500669219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 526278063116485340471669 49338568417170500669219)
                ·
                  rfl

theorem cell20_324292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 3, 5].length) (baseStart_324292 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_324292 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_324292 prefixEnd_324292 := by exact prefixLift 324292
  have htrace : WordTrace (prefixWord ++ tailWord_324292) baseStart_324292 baseEnd_324292 := by
    simpa [prefixWord, tailWord_324292, baseEnd_324292] using wordTrace_append hprefix tailTrace_324292
  have hstable : (prefixWord ++ tailWord_324292).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_324292).length < 2 ^ (prefixWord ++ tailWord_324292).sum := by decide
  have hdescent : baseEnd_324292 < baseStart_324292 := by decide
  rcases family_descends (prefixWord ++ tailWord_324292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_324320 : List Nat := [2, 1, 1, 3, 1, 2, 1, 4, 5]
def baseStart_324320 : Nat := 118140960795 + 324320 * 2 ^ 59
def prefixEnd_324320 : Nat := 4983230072969 + 3 ^ 40 * 324320 * 2
def baseEnd_324320 : Nat := 148028485214467849074209

theorem tailTrace_324320 : CollatzResearch.WordTrace tailWord_324320 prefixEnd_324320 148028485214467849074209 := by
  unfold tailWord_324320
  simp only [CollatzResearch.WordTrace]
  refine ⟨5914461092525752145665207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7885948123367669527553609 5914461092525752145665207)
  ·
    refine ⟨8871691638788628218497811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5914461092525752145665207 8871691638788628218497811)
    ·
      refine ⟨13307537458182942327746717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8871691638788628218497811 13307537458182942327746717)
      ·
        refine ⟨4990326546818603372905019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13307537458182942327746717 4990326546818603372905019)
        ·
          refine ⟨7485489820227905059357529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4990326546818603372905019 7485489820227905059357529)
          ·
            refine ⟨5614117365170928794518147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7485489820227905059357529 5614117365170928794518147)
            ·
              refine ⟨8421176047756393191777221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5614117365170928794518147 8421176047756393191777221)
              ·
                refine ⟨1578970508954323723458229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8421176047756393191777221 1578970508954323723458229)
                ·
                  refine ⟨148028485214467849074209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1578970508954323723458229 148028485214467849074209)
                  ·
                    rfl

theorem cell20_324320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 1, 4, 5].length) (baseStart_324320 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_324320 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_324320 prefixEnd_324320 := by exact prefixLift 324320
  have htrace : WordTrace (prefixWord ++ tailWord_324320) baseStart_324320 baseEnd_324320 := by
    simpa [prefixWord, tailWord_324320, baseEnd_324320] using wordTrace_append hprefix tailTrace_324320
  have hstable : (prefixWord ++ tailWord_324320).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_324320).length < 2 ^ (prefixWord ++ tailWord_324320).sum := by decide
  have hdescent : baseEnd_324320 < baseStart_324320 := by decide
  rcases family_descends (prefixWord ++ tailWord_324320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_324344 : List Nat := [2, 1, 2, 1, 1, 2, 6, 1, 4]
def baseStart_324344 : Nat := 118140960795 + 324344 * 2 ^ 59
def prefixEnd_324344 : Nat := 4983230072969 + 3 ^ 40 * 324344 * 2
def baseEnd_324344 : Nat := 148039439468430432274111

theorem tailTrace_324344 : CollatzResearch.WordTrace tailWord_324344 prefixEnd_324344 148039439468430432274111 := by
  unfold tailWord_324344
  simp only [CollatzResearch.WordTrace]
  refine ⟨5914898768482278195102043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7886531691309704260136057 5914898768482278195102043)
  ·
    refine ⟨8872348152723417292653065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5914898768482278195102043 8872348152723417292653065)
    ·
      refine ⟨6654261114542562969489799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8872348152723417292653065 6654261114542562969489799)
      ·
        refine ⟨9981391671813844454234699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6654261114542562969489799 9981391671813844454234699)
        ·
          refine ⟨14972087507720766681352049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9981391671813844454234699 14972087507720766681352049)
          ·
            refine ⟨11229065630790575011014037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14972087507720766681352049 11229065630790575011014037)
            ·
              refine ⟨526362451443308203641283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 11229065630790575011014037 526362451443308203641283)
              ·
                refine ⟨789543677164962305461925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 526362451443308203641283 789543677164962305461925)
                ·
                  refine ⟨148039439468430432274111, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 789543677164962305461925 148039439468430432274111)
                  ·
                    rfl

theorem cell20_324344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 6, 1, 4].length) (baseStart_324344 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_324344 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_324344 prefixEnd_324344 := by exact prefixLift 324344
  have htrace : WordTrace (prefixWord ++ tailWord_324344) baseStart_324344 baseEnd_324344 := by
    simpa [prefixWord, tailWord_324344, baseEnd_324344] using wordTrace_append hprefix tailTrace_324344
  have hstable : (prefixWord ++ tailWord_324344).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_324344).length < 2 ^ (prefixWord ++ tailWord_324344).sum := by decide
  have hdescent : baseEnd_324344 < baseStart_324344 := by decide
  rcases family_descends (prefixWord ++ tailWord_324344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_324396 : List Nat := [2, 2, 1, 1, 1, 4, 1, 3, 5]
def baseStart_324396 : Nat := 118140960795 + 324396 * 2 ^ 59
def prefixEnd_324396 : Nat := 4983230072969 + 3 ^ 40 * 324396 * 2
def baseEnd_324396 : Nat := 148063173685349362540565

theorem tailTrace_324396 : CollatzResearch.WordTrace tailWord_324396 prefixEnd_324396 148063173685349362540565 := by
  unfold tailWord_324396
  simp only [CollatzResearch.WordTrace]
  refine ⟨5915847066388084635548521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7887796088517446180731361 5915847066388084635548521)
  ·
    refine ⟨4436885299791063476661391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5915847066388084635548521 4436885299791063476661391)
    ·
      refine ⟨6655327949686595214992087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4436885299791063476661391 6655327949686595214992087)
      ·
        refine ⟨9982991924529892822488131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6655327949686595214992087 9982991924529892822488131)
        ·
          refine ⟨14974487886794839233732197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9982991924529892822488131 14974487886794839233732197)
          ·
            refine ⟨2807716478774032356324787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 14974487886794839233732197 2807716478774032356324787)
            ·
              refine ⟨4211574718161048534487181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2807716478774032356324787 4211574718161048534487181)
              ·
                refine ⟨1579340519310393200432693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4211574718161048534487181 1579340519310393200432693)
                ·
                  refine ⟨148063173685349362540565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1579340519310393200432693 148063173685349362540565)
                  ·
                    rfl

theorem cell20_324396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 5].length) (baseStart_324396 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_324396 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_324396 prefixEnd_324396 := by exact prefixLift 324396
  have htrace : WordTrace (prefixWord ++ tailWord_324396) baseStart_324396 baseEnd_324396 := by
    simpa [prefixWord, tailWord_324396, baseEnd_324396] using wordTrace_append hprefix tailTrace_324396
  have hstable : (prefixWord ++ tailWord_324396).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_324396).length < 2 ^ (prefixWord ++ tailWord_324396).sum := by decide
  have hdescent : baseEnd_324396 < baseStart_324396 := by decide
  rcases family_descends (prefixWord ++ tailWord_324396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_324437 : List Nat := [1, 3, 2, 2, 2, 1, 2, 5, 2]
def baseStart_324437 : Nat := 118140960795 + 324437 * 2 ^ 59
def prefixEnd_324437 : Nat := 4983230072969 + 3 ^ 40 * 324437 * 2
def baseEnd_324437 : Nat := 148081887202535442173731

theorem tailTrace_324437 : CollatzResearch.WordTrace tailWord_324437 prefixEnd_324437 148081887202535442173731 := by
  unfold tailWord_324437
  simp only [CollatzResearch.WordTrace]
  refine ⟨11833189525627633273339565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7888793017085088848893043 11833189525627633273339565)
  ·
    refine ⟨4437446072110362477502337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11833189525627633273339565 4437446072110362477502337)
    ·
      refine ⟨3328084554082771858126753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4437446072110362477502337 3328084554082771858126753)
      ·
        refine ⟨2496063415562078893595065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3328084554082771858126753 2496063415562078893595065)
        ·
          refine ⟨1872047561671559170196299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2496063415562078893595065 1872047561671559170196299)
          ·
            refine ⟨2808071342507338755294449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1872047561671559170196299 2808071342507338755294449)
            ·
              refine ⟨2106053506880504066470837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2808071342507338755294449 2106053506880504066470837)
              ·
                refine ⟨197442516270047256231641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2106053506880504066470837 197442516270047256231641)
                ·
                  refine ⟨148081887202535442173731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 197442516270047256231641 148081887202535442173731)
                  ·
                    rfl

theorem cell20_324437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 2, 5, 2].length) (baseStart_324437 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_324437 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_324437 prefixEnd_324437 := by exact prefixLift 324437
  have htrace : WordTrace (prefixWord ++ tailWord_324437) baseStart_324437 baseEnd_324437 := by
    simpa [prefixWord, tailWord_324437, baseEnd_324437] using wordTrace_append hprefix tailTrace_324437
  have hstable : (prefixWord ++ tailWord_324437).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_324437).length < 2 ^ (prefixWord ++ tailWord_324437).sum := by decide
  have hdescent : baseEnd_324437 < baseStart_324437 := by decide
  rcases family_descends (prefixWord ++ tailWord_324437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_324450 : List Nat := [3, 3, 2, 1, 3, 2, 2, 2, 2]
def baseStart_324450 : Nat := 118140960795 + 324450 * 2 ^ 59
def prefixEnd_324450 : Nat := 4983230072969 + 3 ^ 40 * 324450 * 2
def baseEnd_324450 : Nat := 148087820756765174740345

theorem tailTrace_324450 : CollatzResearch.WordTrace tailWord_324450 prefixEnd_324450 148087820756765174740345 := by
  unfold tailWord_324450
  simp only [CollatzResearch.WordTrace]
  refine ⟨2958415918645134123390701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7889109116387024329041869 2958415918645134123390701)
  ·
    refine ⟨1109405969491925296271513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2958415918645134123390701 1109405969491925296271513)
    ·
      refine ⟨832054477118943972203635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1109405969491925296271513 832054477118943972203635)
      ·
        refine ⟨1248081715678415958305453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 832054477118943972203635 1248081715678415958305453)
        ·
          refine ⟨468030643379405984364545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1248081715678415958305453 468030643379405984364545)
          ·
            refine ⟨351022982534554488273409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 468030643379405984364545 351022982534554488273409)
            ·
              refine ⟨263267236900915866205057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 351022982534554488273409 263267236900915866205057)
              ·
                refine ⟨197450427675686899653793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 263267236900915866205057 197450427675686899653793)
                ·
                  refine ⟨148087820756765174740345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 197450427675686899653793 148087820756765174740345)
                  ·
                    rfl

theorem cell20_324450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 3, 2, 2, 2, 2].length) (baseStart_324450 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_324450 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_324450 prefixEnd_324450 := by exact prefixLift 324450
  have htrace : WordTrace (prefixWord ++ tailWord_324450) baseStart_324450 baseEnd_324450 := by
    simpa [prefixWord, tailWord_324450, baseEnd_324450] using wordTrace_append hprefix tailTrace_324450
  have hstable : (prefixWord ++ tailWord_324450).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_324450).length < 2 ^ (prefixWord ++ tailWord_324450).sum := by decide
  have hdescent : baseEnd_324450 < baseStart_324450 := by decide
  rcases family_descends (prefixWord ++ tailWord_324450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_324451 : List Nat := [1, 1, 1, 5, 3, 1, 1, 4, 3]
def baseStart_324451 : Nat := 118140960795 + 324451 * 2 ^ 59
def prefixEnd_324451 : Nat := 4983230072969 + 3 ^ 40 * 324451 * 2
def baseEnd_324451 : Nat := 148088277184013615707007

theorem tailTrace_324451 : CollatzResearch.WordTrace tailWord_324451 prefixEnd_324451 148088277184013615707007 := by
  unfold tailWord_324451
  simp only [CollatzResearch.WordTrace]
  refine ⟨11833700147576913664349207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7889133431717942442899471 11833700147576913664349207)
  ·
    refine ⟨17750550221365370496523811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11833700147576913664349207 17750550221365370496523811)
    ·
      refine ⟨26625825332048055744785717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17750550221365370496523811 26625825332048055744785717)
      ·
        refine ⟨2496171124879505226073661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 26625825332048055744785717 2496171124879505226073661)
        ·
          refine ⟨936064171829814459777623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2496171124879505226073661 936064171829814459777623)
          ·
            refine ⟨1404096257744721689666435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 936064171829814459777623 1404096257744721689666435)
            ·
              refine ⟨2106144386617082534499653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1404096257744721689666435 2106144386617082534499653)
              ·
                refine ⟨394902072490702975218685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2106144386617082534499653 394902072490702975218685)
                ·
                  refine ⟨148088277184013615707007, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 394902072490702975218685 148088277184013615707007)
                  ·
                    rfl

theorem cell20_324451_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 1, 4, 3].length) (baseStart_324451 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_324451 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_324451 prefixEnd_324451 := by exact prefixLift 324451
  have htrace : WordTrace (prefixWord ++ tailWord_324451) baseStart_324451 baseEnd_324451 := by
    simpa [prefixWord, tailWord_324451, baseEnd_324451] using wordTrace_append hprefix tailTrace_324451
  have hstable : (prefixWord ++ tailWord_324451).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_324451).length < 2 ^ (prefixWord ++ tailWord_324451).sum := by decide
  have hdescent : baseEnd_324451 < baseStart_324451 := by decide
  rcases family_descends (prefixWord ++ tailWord_324451) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_324465 : List Nat := [1, 2, 2, 2, 1, 4, 3, 5]
def baseStart_324465 : Nat := 118140960795 + 324465 * 2 ^ 59
def prefixEnd_324465 : Nat := 4983230072969 + 3 ^ 40 * 324465 * 2
def baseEnd_324465 : Nat := 49364889055163929746761

theorem tailTrace_324465 : CollatzResearch.WordTrace tailWord_324465 prefixEnd_324465 49364889055163929746761 := by
  unfold tailWord_324465
  simp only [CollatzResearch.WordTrace]
  refine ⟨11834210769526194055358849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7889473846350796036905899 11834210769526194055358849)
  ·
    refine ⟨8875658077144645541519137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11834210769526194055358849 8875658077144645541519137)
    ·
      refine ⟨6656743557858484156139353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8875658077144645541519137 6656743557858484156139353)
      ·
        refine ⟨4992557668393863117104515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6656743557858484156139353 4992557668393863117104515)
        ·
          refine ⟨7488836502590794675656773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4992557668393863117104515 7488836502590794675656773)
          ·
            refine ⟨1404156844235774001685645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7488836502590794675656773 1404156844235774001685645)
            ·
              refine ⟨526558816588415250632117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1404156844235774001685645 526558816588415250632117)
              ·
                refine ⟨49364889055163929746761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 526558816588415250632117 49364889055163929746761)
                ·
                  rfl

theorem cell20_324465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 3, 5].length) (baseStart_324465 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_324465 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_324465 prefixEnd_324465 := by exact prefixLift 324465
  have htrace : WordTrace (prefixWord ++ tailWord_324465) baseStart_324465 baseEnd_324465 := by
    simpa [prefixWord, tailWord_324465, baseEnd_324465] using wordTrace_append hprefix tailTrace_324465
  have hstable : (prefixWord ++ tailWord_324465).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_324465).length < 2 ^ (prefixWord ++ tailWord_324465).sum := by decide
  have hdescent : baseEnd_324465 < baseStart_324465 := by decide
  rcases family_descends (prefixWord ++ tailWord_324465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_324478 : List Nat := [4, 2, 3, 1, 2, 1, 3, 4]
def baseStart_324478 : Nat := 118140960795 + 324478 * 2 ^ 59
def prefixEnd_324478 : Nat := 4983230072969 + 3 ^ 40 * 324478 * 2
def baseEnd_324478 : Nat := 49366866906573840602299

theorem tailTrace_324478 : CollatzResearch.WordTrace tailWord_324478 prefixEnd_324478 49366866906573840602299 := by
  unfold tailWord_324478
  simp only [CollatzResearch.WordTrace]
  refine ⟨1479335614809887159447761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 7889789945652731517054725 1479335614809887159447761)
  ·
    refine ⟨1109501711107415369585821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1479335614809887159447761 1109501711107415369585821)
    ·
      refine ⟨416063141665280763594683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1109501711107415369585821 416063141665280763594683)
      ·
        refine ⟨624094712497921145392025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 416063141665280763594683 624094712497921145392025)
        ·
          refine ⟨468071034373440859044019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 624094712497921145392025 468071034373440859044019)
          ·
            refine ⟨702106551560161288566029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 468071034373440859044019 702106551560161288566029)
            ·
              refine ⟨263289956835060483212261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 702106551560161288566029 263289956835060483212261)
              ·
                refine ⟨49366866906573840602299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 263289956835060483212261 49366866906573840602299)
                ·
                  rfl

theorem cell20_324478_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 2, 1, 3, 4].length) (baseStart_324478 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_324478 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_324478 prefixEnd_324478 := by exact prefixLift 324478
  have htrace : WordTrace (prefixWord ++ tailWord_324478) baseStart_324478 baseEnd_324478 := by
    simpa [prefixWord, tailWord_324478, baseEnd_324478] using wordTrace_append hprefix tailTrace_324478
  have hstable : (prefixWord ++ tailWord_324478).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_324478).length < 2 ^ (prefixWord ++ tailWord_324478).sum := by decide
  have hdescent : baseEnd_324478 < baseStart_324478 := by decide
  rcases family_descends (prefixWord ++ tailWord_324478) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_324479 : List Nat := [1, 1, 2, 2, 1, 1, 5, 1, 6]
def baseStart_324479 : Nat := 118140960795 + 324479 * 2 ^ 59
def prefixEnd_324479 : Nat := 4983230072969 + 3 ^ 40 * 324479 * 2
def baseEnd_324479 : Nat := 148101057146969962773559

theorem tailTrace_324479 : CollatzResearch.WordTrace tailWord_324479 prefixEnd_324479 148101057146969962773559 := by
  unfold tailWord_324479
  simp only [CollatzResearch.WordTrace]
  refine ⟨11834721391475474446368491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7889814260983649630912327 11834721391475474446368491)
  ·
    refine ⟨17752082087213211669552737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11834721391475474446368491 17752082087213211669552737)
    ·
      refine ⟨13314061565409908752164553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17752082087213211669552737 13314061565409908752164553)
      ·
        refine ⟨9985546174057431564123415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13314061565409908752164553 9985546174057431564123415)
        ·
          refine ⟨14978319261086147346185123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9985546174057431564123415 14978319261086147346185123)
          ·
            refine ⟨22467478891629221019277685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14978319261086147346185123 22467478891629221019277685)
            ·
              refine ⟨2106326146090239470557283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 22467478891629221019277685 2106326146090239470557283)
              ·
                refine ⟨3159489219135359205835925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2106326146090239470557283 3159489219135359205835925)
                ·
                  refine ⟨148101057146969962773559, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3159489219135359205835925 148101057146969962773559)
                  ·
                    rfl

theorem cell20_324479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 5, 1, 6].length) (baseStart_324479 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_324479 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_324479 prefixEnd_324479 := by exact prefixLift 324479
  have htrace : WordTrace (prefixWord ++ tailWord_324479) baseStart_324479 baseEnd_324479 := by
    simpa [prefixWord, tailWord_324479, baseEnd_324479] using wordTrace_append hprefix tailTrace_324479
  have hstable : (prefixWord ++ tailWord_324479).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_324479).length < 2 ^ (prefixWord ++ tailWord_324479).sum := by decide
  have hdescent : baseEnd_324479 < baseStart_324479 := by decide
  rcases family_descends (prefixWord ++ tailWord_324479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_324502 : List Nat := [5, 3, 1, 1, 1, 1, 3, 2, 3]
def baseStart_324502 : Nat := 118140960795 + 324502 * 2 ^ 59
def prefixEnd_324502 : Nat := 4983230072969 + 3 ^ 40 * 324502 * 2
def baseEnd_324502 : Nat := 148111554973684105006799

theorem tailTrace_324502 : CollatzResearch.WordTrace tailWord_324502 prefixEnd_324502 148111554973684105006799 := by
  unfold tailWord_324502
  simp only [CollatzResearch.WordTrace]
  refine ⟨739722516899509335903485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 7890373513594766249637173 739722516899509335903485)
  ·
    refine ⟨277395943837316000963807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 739722516899509335903485 277395943837316000963807)
    ·
      refine ⟨416093915755974001445711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 277395943837316000963807 416093915755974001445711)
      ·
        refine ⟨624140873633961002168567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 416093915755974001445711 624140873633961002168567)
        ·
          refine ⟨936211310450941503252851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 624140873633961002168567 936211310450941503252851)
          ·
            refine ⟨1404316965676412254879277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 936211310450941503252851 1404316965676412254879277)
            ·
              refine ⟨526618862128654595579729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1404316965676412254879277 526618862128654595579729)
              ·
                refine ⟨394964146596490946684797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 526618862128654595579729 394964146596490946684797)
                ·
                  refine ⟨148111554973684105006799, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 394964146596490946684797 148111554973684105006799)
                  ·
                    rfl

theorem cell20_324502_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 3, 2, 3].length) (baseStart_324502 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_324502 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_324502 prefixEnd_324502 := by exact prefixLift 324502
  have htrace : WordTrace (prefixWord ++ tailWord_324502) baseStart_324502 baseEnd_324502 := by
    simpa [prefixWord, tailWord_324502, baseEnd_324502] using wordTrace_append hprefix tailTrace_324502
  have hstable : (prefixWord ++ tailWord_324502).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_324502).length < 2 ^ (prefixWord ++ tailWord_324502).sum := by decide
  have hdescent : baseEnd_324502 < baseStart_324502 := by decide
  rcases family_descends (prefixWord ++ tailWord_324502) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_324513 : List Nat := [1, 2, 3, 4, 1, 2, 2, 1, 4]
def baseStart_324513 : Nat := 118140960795 + 324513 * 2 ^ 59
def prefixEnd_324513 : Nat := 4983230072969 + 3 ^ 40 * 324513 * 2
def baseEnd_324513 : Nat := 148116575673416955640087

theorem tailTrace_324513 : CollatzResearch.WordTrace tailWord_324513 prefixEnd_324513 148116575673416955640087 := by
  unfold tailWord_324513
  simp only [CollatzResearch.WordTrace]
  refine ⟨11835961473352298253106193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7890640982234865502070795 11835961473352298253106193)
  ·
    refine ⟨8876971105014223689829645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11835961473352298253106193 8876971105014223689829645)
    ·
      refine ⟨3328864164380333883686117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8876971105014223689829645 3328864164380333883686117)
      ·
        refine ⟨624162030821312603191147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3328864164380333883686117 624162030821312603191147)
        ·
          refine ⟨936243046231968904786721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 624162030821312603191147 936243046231968904786721)
          ·
            refine ⟨702182284673976678590041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 936243046231968904786721 702182284673976678590041)
            ·
              refine ⟨526636713505482508942531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 702182284673976678590041 526636713505482508942531)
              ·
                refine ⟨789955070258223763413797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 526636713505482508942531 789955070258223763413797)
                ·
                  refine ⟨148116575673416955640087, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 789955070258223763413797 148116575673416955640087)
                  ·
                    rfl

theorem cell20_324513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 2, 2, 1, 4].length) (baseStart_324513 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_324513 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_324513 prefixEnd_324513 := by exact prefixLift 324513
  have htrace : WordTrace (prefixWord ++ tailWord_324513) baseStart_324513 baseEnd_324513 := by
    simpa [prefixWord, tailWord_324513, baseEnd_324513] using wordTrace_append hprefix tailTrace_324513
  have hstable : (prefixWord ++ tailWord_324513).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_324513).length < 2 ^ (prefixWord ++ tailWord_324513).sum := by decide
  have hdescent : baseEnd_324513 < baseStart_324513 := by decide
  rcases family_descends (prefixWord ++ tailWord_324513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_324550 : List Nat := [6, 1, 3, 1, 2, 1, 6]
def baseStart_324550 : Nat := 118140960795 + 324550 * 2 ^ 59
def prefixEnd_324550 : Nat := 4983230072969 + 3 ^ 40 * 324550 * 2
def baseEnd_324550 : Nat := 16459273720178807934067

theorem tailTrace_324550 : CollatzResearch.WordTrace tailWord_324550 prefixEnd_324550 16459273720178807934067 := by
  unfold tailWord_324550
  simp only [CollatzResearch.WordTrace]
  refine ⟨369915967944320424131347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 7891540649478835714802069 369915967944320424131347)
  ·
    refine ⟨554873951916480636197021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 369915967944320424131347 554873951916480636197021)
    ·
      refine ⟨208077731968680238573883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 554873951916480636197021 208077731968680238573883)
      ·
        refine ⟨312116597953020357860825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 208077731968680238573883 312116597953020357860825)
        ·
          refine ⟨234087448464765268395619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 312116597953020357860825 234087448464765268395619)
          ·
            refine ⟨351131172697147902593429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 234087448464765268395619 351131172697147902593429)
            ·
              refine ⟨16459273720178807934067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 351131172697147902593429 16459273720178807934067)
              ·
                rfl

theorem cell20_324550_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 2, 1, 6].length) (baseStart_324550 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_324550 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_324550 prefixEnd_324550 := by exact prefixLift 324550
  have htrace : WordTrace (prefixWord ++ tailWord_324550) baseStart_324550 baseEnd_324550 := by
    simpa [prefixWord, tailWord_324550, baseEnd_324550] using wordTrace_append hprefix tailTrace_324550
  have hstable : (prefixWord ++ tailWord_324550).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_324550).length < 2 ^ (prefixWord ++ tailWord_324550).sum := by decide
  have hdescent : baseEnd_324550 < baseStart_324550 := by decide
  rcases family_descends (prefixWord ++ tailWord_324550) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_324551 : List Nat := [1, 1, 4, 1, 1, 2, 5, 3, 2]
def baseStart_324551 : Nat := 118140960795 + 324551 * 2 ^ 59
def prefixEnd_324551 : Nat := 4983230072969 + 3 ^ 40 * 324551 * 2
def baseEnd_324551 : Nat := 148133919908857712373265

theorem tailTrace_324551 : CollatzResearch.WordTrace tailWord_324551 prefixEnd_324551 148133919908857712373265 := by
  unfold tailWord_324551
  simp only [CollatzResearch.WordTrace]
  refine ⟨11837347447214630742989507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7891564964809753828659671 11837347447214630742989507)
  ·
    refine ⟨17756021170821946114484261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11837347447214630742989507 17756021170821946114484261)
    ·
      refine ⟨3329253969529114896465799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 17756021170821946114484261 3329253969529114896465799)
      ·
        refine ⟨4993880954293672344698699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3329253969529114896465799 4993880954293672344698699)
        ·
          refine ⟨7490821431440508517048049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4993880954293672344698699 7490821431440508517048049)
          ·
            refine ⟨5618116073580381387786037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7490821431440508517048049 5618116073580381387786037)
            ·
              refine ⟨526698381898160755104941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 5618116073580381387786037 526698381898160755104941)
              ·
                refine ⟨197511893211810283164353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 526698381898160755104941 197511893211810283164353)
                ·
                  refine ⟨148133919908857712373265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 197511893211810283164353 148133919908857712373265)
                  ·
                    rfl

theorem cell20_324551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 5, 3, 2].length) (baseStart_324551 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_324551 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_324551 prefixEnd_324551 := by exact prefixLift 324551
  have htrace : WordTrace (prefixWord ++ tailWord_324551) baseStart_324551 baseEnd_324551 := by
    simpa [prefixWord, tailWord_324551, baseEnd_324551] using wordTrace_append hprefix tailTrace_324551
  have hstable : (prefixWord ++ tailWord_324551).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_324551).length < 2 ^ (prefixWord ++ tailWord_324551).sum := by decide
  have hdescent : baseEnd_324551 < baseStart_324551 := by decide
  rcases family_descends (prefixWord ++ tailWord_324551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_324568 : List Nat := [2, 1, 2, 2, 2, 4, 3, 2, 2]
def baseStart_324568 : Nat := 118140960795 + 324568 * 2 ^ 59
def prefixEnd_324568 : Nat := 4983230072969 + 3 ^ 40 * 324568 * 2
def baseEnd_324568 : Nat := 148141679172081208806529

theorem tailTrace_324568 : CollatzResearch.WordTrace tailWord_324568 prefixEnd_324568 148141679172081208806529 := by
  unfold tailWord_324568
  simp only [CollatzResearch.WordTrace]
  refine ⟨5918983744076521323179179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7891978325435361764238905 5918983744076521323179179)
  ·
    refine ⟨8878475616114781984768769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5918983744076521323179179 8878475616114781984768769)
    ·
      refine ⟨6658856712086086488576577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8878475616114781984768769 6658856712086086488576577)
      ·
        refine ⟨4994142534064564866432433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6658856712086086488576577 4994142534064564866432433)
        ·
          refine ⟨3745606900548423649824325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4994142534064564866432433 3745606900548423649824325)
          ·
            refine ⟨702301293852829434342061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3745606900548423649824325 702301293852829434342061)
            ·
              refine ⟨263362985194811037878273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 702301293852829434342061 263362985194811037878273)
              ·
                refine ⟨197522238896108278408705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 263362985194811037878273 197522238896108278408705)
                ·
                  refine ⟨148141679172081208806529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 197522238896108278408705 148141679172081208806529)
                  ·
                    rfl

theorem cell20_324568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 4, 3, 2, 2].length) (baseStart_324568 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_324568 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_324568 prefixEnd_324568 := by exact prefixLift 324568
  have htrace : WordTrace (prefixWord ++ tailWord_324568) baseStart_324568 baseEnd_324568 := by
    simpa [prefixWord, tailWord_324568, baseEnd_324568] using wordTrace_append hprefix tailTrace_324568
  have hstable : (prefixWord ++ tailWord_324568).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_324568).length < 2 ^ (prefixWord ++ tailWord_324568).sum := by decide
  have hdescent : baseEnd_324568 < baseStart_324568 := by decide
  rcases family_descends (prefixWord ++ tailWord_324568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_324578 : List Nat := [3, 3, 3, 1, 1, 3, 2, 1, 3]
def baseStart_324578 : Nat := 118140960795 + 324578 * 2 ^ 59
def prefixEnd_324578 : Nat := 4983230072969 + 3 ^ 40 * 324578 * 2
def baseEnd_324578 : Nat := 148146243444565618473155

theorem tailTrace_324578 : CollatzResearch.WordTrace tailWord_324578 prefixEnd_324578 148146243444565618473155 := by
  unfold tailWord_324578
  simp only [CollatzResearch.WordTrace]
  refine ⟨2959583054529203588555597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7892221478744542902814925 2959583054529203588555597)
  ·
    refine ⟨1109843645448451345708349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2959583054529203588555597 1109843645448451345708349)
    ·
      refine ⟨416191367043169254640631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1109843645448451345708349 416191367043169254640631)
      ·
        refine ⟨624287050564753881960947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 416191367043169254640631 624287050564753881960947)
        ·
          refine ⟨936430575847130822941421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 624287050564753881960947 936430575847130822941421)
          ·
            refine ⟨351161465942674058603033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 936430575847130822941421 351161465942674058603033)
            ·
              refine ⟨263371099457005543952275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 351161465942674058603033 263371099457005543952275)
              ·
                refine ⟨395056649185508315928413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 263371099457005543952275 395056649185508315928413)
                ·
                  refine ⟨148146243444565618473155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 395056649185508315928413 148146243444565618473155)
                  ·
                    rfl

theorem cell20_324578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 3, 2, 1, 3].length) (baseStart_324578 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_324578 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_324578 prefixEnd_324578 := by exact prefixLift 324578
  have htrace : WordTrace (prefixWord ++ tailWord_324578) baseStart_324578 baseEnd_324578 := by
    simpa [prefixWord, tailWord_324578, baseEnd_324578] using wordTrace_append hprefix tailTrace_324578
  have hstable : (prefixWord ++ tailWord_324578).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_324578).length < 2 ^ (prefixWord ++ tailWord_324578).sum := by decide
  have hdescent : baseEnd_324578 < baseStart_324578 := by decide
  rcases family_descends (prefixWord ++ tailWord_324578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_324579 : List Nat := [1, 1, 1, 6, 1, 1, 4, 5]
def baseStart_324579 : Nat := 118140960795 + 324579 * 2 ^ 59
def prefixEnd_324579 : Nat := 4983230072969 + 3 ^ 40 * 324579 * 2
def baseEnd_324579 : Nat := 49382233290604686479939

theorem tailTrace_324579 : CollatzResearch.WordTrace tailWord_324579 prefixEnd_324579 49382233290604686479939 := by
  unfold tailWord_324579
  simp only [CollatzResearch.WordTrace]
  refine ⟨11838368691113191525008791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7892245794075461016672527 11838368691113191525008791)
  ·
    refine ⟨17757553036669787287513187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11838368691113191525008791 17757553036669787287513187)
    ·
      refine ⟨26636329555004680931269781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17757553036669787287513187 26636329555004680931269781)
      ·
        refine ⟨1248577947890844418653271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 26636329555004680931269781 1248577947890844418653271)
        ·
          refine ⟨1872866921836266627979907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1248577947890844418653271 1872866921836266627979907)
          ·
            refine ⟨2809300382754399941969861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1872866921836266627979907 2809300382754399941969861)
            ·
              refine ⟨526743821766449989119349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2809300382754399941969861 526743821766449989119349)
              ·
                refine ⟨49382233290604686479939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 526743821766449989119349 49382233290604686479939)
                ·
                  rfl

theorem cell20_324579_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 4, 5].length) (baseStart_324579 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_324579 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_324579 prefixEnd_324579 := by exact prefixLift 324579
  have htrace : WordTrace (prefixWord ++ tailWord_324579) baseStart_324579 baseEnd_324579 := by
    simpa [prefixWord, tailWord_324579, baseEnd_324579] using wordTrace_append hprefix tailTrace_324579
  have hstable : (prefixWord ++ tailWord_324579).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_324579).length < 2 ^ (prefixWord ++ tailWord_324579).sum := by decide
  have hdescent : baseEnd_324579 < baseStart_324579 := by decide
  rcases family_descends (prefixWord ++ tailWord_324579) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_324641 : List Nat := [1, 2, 3, 2, 3, 1, 2, 3, 3]
def baseStart_324641 : Nat := 118140960795 + 324641 * 2 ^ 59
def prefixEnd_324641 : Nat := 4983230072969 + 3 ^ 40 * 324641 * 2
def baseEnd_324641 : Nat := 148174998361217399372897

theorem tailTrace_324641 : CollatzResearch.WordTrace tailWord_324641 prefixEnd_324641 148174998361217399372897 := by
  unfold tailWord_324641
  simp only [CollatzResearch.WordTrace]
  refine ⟨11840630016888576113765777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7893753344592384075843851 11840630016888576113765777)
  ·
    refine ⟨8880472512666432085324333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11840630016888576113765777 8880472512666432085324333)
    ·
      refine ⟨3330177192249912031996625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8880472512666432085324333 3330177192249912031996625)
      ·
        refine ⟨2497632894187434023997469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3330177192249912031996625 2497632894187434023997469)
        ·
          refine ⟨936612335320287758999051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2497632894187434023997469 936612335320287758999051)
          ·
            refine ⟨1404918502980431638498577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 936612335320287758999051 1404918502980431638498577)
            ·
              refine ⟨1053688877235323728873933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1404918502980431638498577 1053688877235323728873933)
              ·
                refine ⟨395133328963246398327725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1053688877235323728873933 395133328963246398327725)
                ·
                  refine ⟨148174998361217399372897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 395133328963246398327725 148174998361217399372897)
                  ·
                    rfl

theorem cell20_324641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 2, 3, 3].length) (baseStart_324641 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_324641 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_324641 prefixEnd_324641 := by exact prefixLift 324641
  have htrace : WordTrace (prefixWord ++ tailWord_324641) baseStart_324641 baseEnd_324641 := by
    simpa [prefixWord, tailWord_324641, baseEnd_324641] using wordTrace_append hprefix tailTrace_324641
  have hstable : (prefixWord ++ tailWord_324641).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_324641).length < 2 ^ (prefixWord ++ tailWord_324641).sum := by decide
  have hdescent : baseEnd_324641 < baseStart_324641 := by decide
  rcases family_descends (prefixWord ++ tailWord_324641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_324665 : List Nat := [1, 2, 1, 5, 2, 1, 1, 5, 2]
def baseStart_324665 : Nat := 118140960795 + 324665 * 2 ^ 59
def prefixEnd_324665 : Nat := 4983230072969 + 3 ^ 40 * 324665 * 2
def baseEnd_324665 : Nat := 148185952615179982572799

theorem tailTrace_324665 : CollatzResearch.WordTrace tailWord_324665 prefixEnd_324665 148185952615179982572799 := by
  unfold tailWord_324665
  simp only [CollatzResearch.WordTrace]
  refine ⟨11841505368801628212639449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7894336912534418808426299 11841505368801628212639449)
  ·
    refine ⟨8881129026601221159479587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11841505368801628212639449 8881129026601221159479587)
    ·
      refine ⟨13321693539901831739219381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8881129026601221159479587 13321693539901831739219381)
      ·
        refine ⟨1248908769365796725551817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 13321693539901831739219381 1248908769365796725551817)
        ·
          refine ⟨936681577024347544163863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1248908769365796725551817 936681577024347544163863)
          ·
            refine ⟨1405022365536521316245795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 936681577024347544163863 1405022365536521316245795)
            ·
              refine ⟨2107533548304781974368693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1405022365536521316245795 2107533548304781974368693)
              ·
                refine ⟨197581270153573310097065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2107533548304781974368693 197581270153573310097065)
                ·
                  refine ⟨148185952615179982572799, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 197581270153573310097065 148185952615179982572799)
                  ·
                    rfl

theorem cell20_324665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 1, 5, 2].length) (baseStart_324665 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_324665 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_324665 prefixEnd_324665 := by exact prefixLift 324665
  have htrace : WordTrace (prefixWord ++ tailWord_324665) baseStart_324665 baseEnd_324665 := by
    simpa [prefixWord, tailWord_324665, baseEnd_324665] using wordTrace_append hprefix tailTrace_324665
  have hstable : (prefixWord ++ tailWord_324665).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_324665).length < 2 ^ (prefixWord ++ tailWord_324665).sum := by decide
  have hdescent : baseEnd_324665 < baseStart_324665 := by decide
  rcases family_descends (prefixWord ++ tailWord_324665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_324679 : List Nat := [1, 1, 4, 1, 3, 2, 3, 2, 3]
def baseStart_324679 : Nat := 118140960795 + 324679 * 2 ^ 59
def prefixEnd_324679 : Nat := 4983230072969 + 3 ^ 40 * 324679 * 2
def baseEnd_324679 : Nat := 148192342596658156106075

theorem tailTrace_324679 : CollatzResearch.WordTrace tailWord_324679 prefixEnd_324679 148192342596658156106075 := by
  unfold tailWord_324679
  simp only [CollatzResearch.WordTrace]
  refine ⟨11842015990750908603649091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7894677327167272402432727 11842015990750908603649091)
  ·
    refine ⟨17763023986126362905473637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11842015990750908603649091 17763023986126362905473637)
    ·
      refine ⟨3330566997398693044776307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 17763023986126362905473637 3330566997398693044776307)
      ·
        refine ⟨4995850496098039567164461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3330566997398693044776307 4995850496098039567164461)
        ·
          refine ⟨1873443936036764837686673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4995850496098039567164461 1873443936036764837686673)
          ·
            refine ⟨1405082952027573628265005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1873443936036764837686673 1405082952027573628265005)
            ·
              refine ⟨526906107010340110599377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1405082952027573628265005 526906107010340110599377)
              ·
                refine ⟨395179580257755082949533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 526906107010340110599377 395179580257755082949533)
                ·
                  refine ⟨148192342596658156106075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 395179580257755082949533 148192342596658156106075)
                  ·
                    rfl

theorem cell20_324679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 3, 2, 3].length) (baseStart_324679 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_324679 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_324679 prefixEnd_324679 := by exact prefixLift 324679
  have htrace : WordTrace (prefixWord ++ tailWord_324679) baseStart_324679 baseEnd_324679 := by
    simpa [prefixWord, tailWord_324679, baseEnd_324679] using wordTrace_append hprefix tailTrace_324679
  have hstable : (prefixWord ++ tailWord_324679).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_324679).length < 2 ^ (prefixWord ++ tailWord_324679).sum := by decide
  have hdescent : baseEnd_324679 < baseStart_324679 := by decide
  rcases family_descends (prefixWord ++ tailWord_324679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_324686 : List Nat := [4, 1, 1, 1, 1, 3, 4, 1, 4]
def baseStart_324686 : Nat := 118140960795 + 324686 * 2 ^ 59
def prefixEnd_324686 : Nat := 4983230072969 + 3 ^ 40 * 324686 * 2
def baseEnd_324686 : Nat := 148195537587397242872713

theorem tailTrace_324686 : CollatzResearch.WordTrace tailWord_324686 prefixEnd_324686 148195537587397242872713 := by
  unfold tailWord_324686
  simp only [CollatzResearch.WordTrace]
  refine ⟨1480283912715693599894239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 7894847534483699199435941 1480283912715693599894239)
  ·
    refine ⟨2220425869073540399841359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1480283912715693599894239 2220425869073540399841359)
    ·
      refine ⟨3330638803610310599762039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2220425869073540399841359 3330638803610310599762039)
      ·
        refine ⟨4995958205415465899643059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3330638803610310599762039 4995958205415465899643059)
        ·
          refine ⟨7493937308123198849464589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4995958205415465899643059 7493937308123198849464589)
          ·
            refine ⟨2810226490546199568549221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7493937308123198849464589 2810226490546199568549221)
            ·
              refine ⟨526917466977412419102979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2810226490546199568549221 526917466977412419102979)
              ·
                refine ⟨790376200466118628654469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 526917466977412419102979 790376200466118628654469)
                ·
                  refine ⟨148195537587397242872713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 790376200466118628654469 148195537587397242872713)
                  ·
                    rfl

theorem cell20_324686_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 4, 1, 4].length) (baseStart_324686 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_324686 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_324686 prefixEnd_324686 := by exact prefixLift 324686
  have htrace : WordTrace (prefixWord ++ tailWord_324686) baseStart_324686 baseEnd_324686 := by
    simpa [prefixWord, tailWord_324686, baseEnd_324686] using wordTrace_append hprefix tailTrace_324686
  have hstable : (prefixWord ++ tailWord_324686).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_324686).length < 2 ^ (prefixWord ++ tailWord_324686).sum := by decide
  have hdescent : baseEnd_324686 < baseStart_324686 := by decide
  rcases family_descends (prefixWord ++ tailWord_324686) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_324741 : List Nat := [1, 3, 1, 1, 6, 2, 1, 1, 4]
def baseStart_324741 : Nat := 118140960795 + 324741 * 2 ^ 59
def prefixEnd_324741 : Nat := 4983230072969 + 3 ^ 40 * 324741 * 2
def baseEnd_324741 : Nat := 148220641086061496039155

theorem tailTrace_324741 : CollatzResearch.WordTrace tailWord_324741 prefixEnd_324741 148220641086061496039155 := by
  unfold tailWord_324741
  simp only [CollatzResearch.WordTrace]
  refine ⟨11844277316526293192406077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7896184877684195461604051 11844277316526293192406077)
  ·
    refine ⟨4441603993697359947152279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11844277316526293192406077 4441603993697359947152279)
    ·
      refine ⟨6662405990546039920728419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4441603993697359947152279 6662405990546039920728419)
      ·
        refine ⟨9993608985819059881092629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6662405990546039920728419 9993608985819059881092629)
        ·
          refine ⟨468450421210268431926217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 9993608985819059881092629 468450421210268431926217)
          ·
            refine ⟨351337815907701323944663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 468450421210268431926217 351337815907701323944663)
            ·
              refine ⟨527006723861551985916995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 351337815907701323944663 527006723861551985916995)
              ·
                refine ⟨790510085792327978875493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 527006723861551985916995 790510085792327978875493)
                ·
                  refine ⟨148220641086061496039155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 790510085792327978875493 148220641086061496039155)
                  ·
                    rfl

theorem cell20_324741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 6, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 6, 2, 1, 1, 4].length) (baseStart_324741 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_324741 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_324741 prefixEnd_324741 := by exact prefixLift 324741
  have htrace : WordTrace (prefixWord ++ tailWord_324741) baseStart_324741 baseEnd_324741 := by
    simpa [prefixWord, tailWord_324741, baseEnd_324741] using wordTrace_append hprefix tailTrace_324741
  have hstable : (prefixWord ++ tailWord_324741).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_324741).length < 2 ^ (prefixWord ++ tailWord_324741).sum := by decide
  have hdescent : baseEnd_324741 < baseStart_324741 := by decide
  rcases family_descends (prefixWord ++ tailWord_324741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_324755 : List Nat := [1, 1, 1, 2, 1, 2, 8, 1, 3]
def baseStart_324755 : Nat := 118140960795 + 324755 * 2 ^ 59
def prefixEnd_324755 : Nat := 4983230072969 + 3 ^ 40 * 324755 * 2
def baseEnd_324755 : Nat := 148227031067539669572431

theorem tailTrace_324755 : CollatzResearch.WordTrace tailWord_324755 prefixEnd_324755 148227031067539669572431 := by
  unfold tailWord_324755
  simp only [CollatzResearch.WordTrace]
  refine ⟨11844787938475573583415719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7896525292317049055610479 11844787938475573583415719)
  ·
    refine ⟨17767181907713360375123579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11844787938475573583415719 17767181907713360375123579)
    ·
      refine ⟨26650772861570040562685369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17767181907713360375123579 26650772861570040562685369)
      ·
        refine ⟨19988079646177530422014027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26650772861570040562685369 19988079646177530422014027)
        ·
          refine ⟨29982119469266295633021041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19988079646177530422014027 29982119469266295633021041)
          ·
            refine ⟨22486589601949721724765781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29982119469266295633021041 22486589601949721724765781)
            ·
              refine ⟨263514721897848301462099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 22486589601949721724765781 263514721897848301462099)
              ·
                refine ⟨395272082846772452193149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 263514721897848301462099 395272082846772452193149)
                ·
                  refine ⟨148227031067539669572431, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 395272082846772452193149 148227031067539669572431)
                  ·
                    rfl

theorem cell20_324755_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 8, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 8, 1, 3].length) (baseStart_324755 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_324755 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_324755 prefixEnd_324755 := by exact prefixLift 324755
  have htrace : WordTrace (prefixWord ++ tailWord_324755) baseStart_324755 baseEnd_324755 := by
    simpa [prefixWord, tailWord_324755, baseEnd_324755] using wordTrace_append hprefix tailTrace_324755
  have hstable : (prefixWord ++ tailWord_324755).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_324755).length < 2 ^ (prefixWord ++ tailWord_324755).sum := by decide
  have hdescent : baseEnd_324755 < baseStart_324755 := by decide
  rcases family_descends (prefixWord ++ tailWord_324755) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_324793 : List Nat := [1, 2, 1, 4, 1, 4, 2, 2, 3]
def baseStart_324793 : Nat := 118140960795 + 324793 * 2 ^ 59
def prefixEnd_324793 : Nat := 4983230072969 + 3 ^ 40 * 324793 * 2
def baseEnd_324793 : Nat := 148244375302980426305609

theorem tailTrace_324793 : CollatzResearch.WordTrace tailWord_324793 prefixEnd_324793 148244375302980426305609 := by
  unfold tailWord_324793
  simp only [CollatzResearch.WordTrace]
  refine ⟨11846173912337906073299033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7897449274891937382199355 11846173912337906073299033)
  ·
    refine ⟨8884630434253429554974275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11846173912337906073299033 8884630434253429554974275)
    ·
      refine ⟨13326945651380144332461413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8884630434253429554974275 13326945651380144332461413)
      ·
        refine ⟨2498802309633777062336515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 13326945651380144332461413 2498802309633777062336515)
        ·
          refine ⟨3748203464450665593504773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2498802309633777062336515 3748203464450665593504773)
          ·
            refine ⟨702788149584499798782145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3748203464450665593504773 702788149584499798782145)
            ·
              refine ⟨527091112188374849086609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 702788149584499798782145 527091112188374849086609)
              ·
                refine ⟨395318334141281136814957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 527091112188374849086609 395318334141281136814957)
                ·
                  refine ⟨148244375302980426305609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 395318334141281136814957 148244375302980426305609)
                  ·
                    rfl

theorem cell20_324793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 4, 2, 2, 3].length) (baseStart_324793 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_324793 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_324793 prefixEnd_324793 := by exact prefixLift 324793
  have htrace : WordTrace (prefixWord ++ tailWord_324793) baseStart_324793 baseEnd_324793 := by
    simpa [prefixWord, tailWord_324793, baseEnd_324793] using wordTrace_append hprefix tailTrace_324793
  have hstable : (prefixWord ++ tailWord_324793).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_324793).length < 2 ^ (prefixWord ++ tailWord_324793).sum := by decide
  have hdescent : baseEnd_324793 < baseStart_324793 := by decide
  rcases family_descends (prefixWord ++ tailWord_324793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_324796 : List Nat := [2, 2, 2, 3, 2, 1, 4, 2, 2]
def baseStart_324796 : Nat := 118140960795 + 324796 * 2 ^ 59
def prefixEnd_324796 : Nat := 4983230072969 + 3 ^ 40 * 324796 * 2
def baseEnd_324796 : Nat := 148245744584725749205597

theorem tailTrace_324796 : CollatzResearch.WordTrace tailWord_324796 prefixEnd_324796 148245744584725749205597 := by
  unfold tailWord_324796
  simp only [CollatzResearch.WordTrace]
  refine ⟨5923141665663518792829121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7897522220884691723772161 5923141665663518792829121)
  ·
    refine ⟨4442356249247639094621841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5923141665663518792829121 4442356249247639094621841)
    ·
      refine ⟨3331767186935729320966381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4442356249247639094621841 3331767186935729320966381)
      ·
        refine ⟨1249412695100898495362393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3331767186935729320966381 1249412695100898495362393)
        ·
          refine ⟨937059521325673871521795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1249412695100898495362393 937059521325673871521795)
          ·
            refine ⟨1405589281988510807282693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 937059521325673871521795 1405589281988510807282693)
            ·
              refine ⟨263547990372845776365505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1405589281988510807282693 263547990372845776365505)
              ·
                refine ⟨197660992779634332274129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 263547990372845776365505 197660992779634332274129)
                ·
                  refine ⟨148245744584725749205597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 197660992779634332274129 148245744584725749205597)
                  ·
                    rfl

theorem cell20_324796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 4, 2, 2].length) (baseStart_324796 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_324796 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_324796 prefixEnd_324796 := by exact prefixLift 324796
  have htrace : WordTrace (prefixWord ++ tailWord_324796) baseStart_324796 baseEnd_324796 := by
    simpa [prefixWord, tailWord_324796, baseEnd_324796] using wordTrace_append hprefix tailTrace_324796
  have hstable : (prefixWord ++ tailWord_324796).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_324796).length < 2 ^ (prefixWord ++ tailWord_324796).sum := by decide
  have hdescent : baseEnd_324796 < baseStart_324796 := by decide
  rcases family_descends (prefixWord ++ tailWord_324796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_324824 : List Nat := [2, 1, 2, 2, 5, 1, 3, 4]
def baseStart_324824 : Nat := 118140960795 + 324824 * 2 ^ 59
def prefixEnd_324824 : Nat := 4983230072969 + 3 ^ 40 * 324824 * 2
def baseEnd_324824 : Nat := 49419508182560698757383

theorem tailTrace_324824 : CollatzResearch.WordTrace tailWord_324824 prefixEnd_324824 49419508182560698757383 := by
  unfold tailWord_324824
  simp only [CollatzResearch.WordTrace]
  refine ⟨5923652287612799183838763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7898203050150398911785017 5923652287612799183838763)
  ·
    refine ⟨8885478431419198775758145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5923652287612799183838763 8885478431419198775758145)
    ·
      refine ⟨6664108823564399081818609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8885478431419198775758145 6664108823564399081818609)
      ·
        refine ⟨4998081617673299311363957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6664108823564399081818609 4998081617673299311363957)
        ·
          refine ⟨468570151656871810440371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 4998081617673299311363957 468570151656871810440371)
          ·
            refine ⟨702855227485307715660557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 468570151656871810440371 702855227485307715660557)
            ·
              refine ⟨263570710306990393372709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 702855227485307715660557 263570710306990393372709)
              ·
                refine ⟨49419508182560698757383, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 263570710306990393372709 49419508182560698757383)
                ·
                  rfl

theorem cell20_324824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 5, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 5, 1, 3, 4].length) (baseStart_324824 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_324824 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_324824 prefixEnd_324824 := by exact prefixLift 324824
  have htrace : WordTrace (prefixWord ++ tailWord_324824) baseStart_324824 baseEnd_324824 := by
    simpa [prefixWord, tailWord_324824, baseEnd_324824] using wordTrace_append hprefix tailTrace_324824
  have hstable : (prefixWord ++ tailWord_324824).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_324824).length < 2 ^ (prefixWord ++ tailWord_324824).sum := by decide
  have hdescent : baseEnd_324824 < baseStart_324824 := by decide
  rcases family_descends (prefixWord ++ tailWord_324824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_324845 : List Nat := [1, 5, 1, 2, 2, 2, 7]
def baseStart_324845 : Nat := 118140960795 + 324845 * 2 ^ 59
def prefixEnd_324845 : Nat := 4983230072969 + 3 ^ 40 * 324845 * 2
def baseEnd_324845 : Nat := 16474234391099928508007

theorem tailTrace_324845 : CollatzResearch.WordTrace tailWord_324845 prefixEnd_324845 16474234391099928508007 := by
  unfold tailWord_324845
  simp only [CollatzResearch.WordTrace]
  refine ⟨11848070508149518954191989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7898713672099679302794659 11848070508149518954191989)
  ·
    refine ⟨1110756610139017401955499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 11848070508149518954191989 1110756610139017401955499)
    ·
      refine ⟨1666134915208526102933249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1110756610139017401955499 1666134915208526102933249)
      ·
        refine ⟨1249601186406394577199937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1666134915208526102933249 1249601186406394577199937)
        ·
          refine ⟨937200889804795932899953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1249601186406394577199937 937200889804795932899953)
          ·
            refine ⟨702900667353596949674965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 937200889804795932899953 702900667353596949674965)
            ·
              refine ⟨16474234391099928508007, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 702900667353596949674965 16474234391099928508007)
              ·
                rfl

theorem cell20_324845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 2, 7].length) (baseStart_324845 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_324845 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_324845 prefixEnd_324845 := by exact prefixLift 324845
  have htrace : WordTrace (prefixWord ++ tailWord_324845) baseStart_324845 baseEnd_324845 := by
    simpa [prefixWord, tailWord_324845, baseEnd_324845] using wordTrace_append hprefix tailTrace_324845
  have hstable : (prefixWord ++ tailWord_324845).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_324845).length < 2 ^ (prefixWord ++ tailWord_324845).sum := by decide
  have hdescent : baseEnd_324845 < baseStart_324845 := by decide
  rcases family_descends (prefixWord ++ tailWord_324845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_324869 : List Nat := [1, 3, 1, 1, 2, 1, 7, 1, 3]
def baseStart_324869 : Nat := 118140960795 + 324869 * 2 ^ 59
def prefixEnd_324869 : Nat := 4983230072969 + 3 ^ 40 * 324869 * 2
def baseEnd_324869 : Nat := 148279063773861939771965

theorem tailTrace_324869 : CollatzResearch.WordTrace tailWord_324869 prefixEnd_324869 148279063773861939771965 := by
  unfold tailWord_324869
  simp only [CollatzResearch.WordTrace]
  refine ⟨11848945860062571053065661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7899297240041714035377107 11848945860062571053065661)
  ·
    refine ⟨4443354697523464144899623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11848945860062571053065661 4443354697523464144899623)
    ·
      refine ⟨6665032046285196217349435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4443354697523464144899623 6665032046285196217349435)
      ·
        refine ⟨9997548069427794326024153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6665032046285196217349435 9997548069427794326024153)
        ·
          refine ⟨7498161052070845744518115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9997548069427794326024153 7498161052070845744518115)
          ·
            refine ⟨11247241578106268616777173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7498161052070845744518115 11247241578106268616777173)
            ·
              refine ⟨263607224486865670705715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 11247241578106268616777173 263607224486865670705715)
              ·
                refine ⟨395410836730298506058573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 263607224486865670705715 395410836730298506058573)
                ·
                  refine ⟨148279063773861939771965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 395410836730298506058573 148279063773861939771965)
                  ·
                    rfl

theorem cell20_324869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 7, 1, 3].length) (baseStart_324869 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_324869 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_324869 prefixEnd_324869 := by exact prefixLift 324869
  have htrace : WordTrace (prefixWord ++ tailWord_324869) baseStart_324869 baseEnd_324869 := by
    simpa [prefixWord, tailWord_324869, baseEnd_324869] using wordTrace_append hprefix tailTrace_324869
  have hstable : (prefixWord ++ tailWord_324869).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_324869).length < 2 ^ (prefixWord ++ tailWord_324869).sum := by decide
  have hdescent : baseEnd_324869 < baseStart_324869 := by decide
  rcases family_descends (prefixWord ++ tailWord_324869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_324890 : List Nat := [3, 1, 1, 3, 3, 1, 1, 2, 5]
def baseStart_324890 : Nat := 118140960795 + 324890 * 2 ^ 59
def prefixEnd_324890 : Nat := 4983230072969 + 3 ^ 40 * 324890 * 2
def baseEnd_324890 : Nat := 148288648746079200071879

theorem tailTrace_324890 : CollatzResearch.WordTrace tailWord_324890 prefixEnd_324890 148288648746079200071879 := by
  unfold tailWord_324890
  simp only [CollatzResearch.WordTrace]
  refine ⟨2962427948246622909895031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7899807861990994426386749 2962427948246622909895031)
  ·
    refine ⟨4443641922369934364842547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2962427948246622909895031 4443641922369934364842547)
    ·
      refine ⟨6665462883554901547263821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4443641922369934364842547 6665462883554901547263821)
      ·
        refine ⟨2499548581333088080223933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6665462883554901547263821 2499548581333088080223933)
        ·
          refine ⟨937330717999908030083975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2499548581333088080223933 937330717999908030083975)
          ·
            refine ⟨1405996076999862045125963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 937330717999908030083975 1405996076999862045125963)
            ·
              refine ⟨2108994115499793067688945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1405996076999862045125963 2108994115499793067688945)
              ·
                refine ⟨1581745586624844800766709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2108994115499793067688945 1581745586624844800766709)
                ·
                  refine ⟨148288648746079200071879, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1581745586624844800766709 148288648746079200071879)
                  ·
                    rfl

theorem cell20_324890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 1, 2, 5].length) (baseStart_324890 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_324890 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_324890 prefixEnd_324890 := by exact prefixLift 324890
  have htrace : WordTrace (prefixWord ++ tailWord_324890) baseStart_324890 baseEnd_324890 := by
    simpa [prefixWord, tailWord_324890, baseEnd_324890] using wordTrace_append hprefix tailTrace_324890
  have hstable : (prefixWord ++ tailWord_324890).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_324890).length < 2 ^ (prefixWord ++ tailWord_324890).sum := by decide
  have hdescent : baseEnd_324890 < baseStart_324890 := by decide
  rcases family_descends (prefixWord ++ tailWord_324890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_324914 : List Nat := [3, 2, 1, 1, 4, 1, 3, 1, 4]
def baseStart_324914 : Nat := 118140960795 + 324914 * 2 ^ 59
def prefixEnd_324914 : Nat := 4983230072969 + 3 ^ 40 * 324914 * 2
def baseEnd_324914 : Nat := 148299603000041783271781

theorem tailTrace_324914 : CollatzResearch.WordTrace tailWord_324914 prefixEnd_324914 148299603000041783271781 := by
  unfold tailWord_324914
  simp only [CollatzResearch.WordTrace]
  refine ⟨2962646786224885934613449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7900391429933029158969197 2962646786224885934613449)
  ·
    refine ⟨2221985089668664450960087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2962646786224885934613449 2221985089668664450960087)
    ·
      refine ⟨3332977634502996676440131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2221985089668664450960087 3332977634502996676440131)
      ·
        refine ⟨4999466451754495014660197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3332977634502996676440131 4999466451754495014660197)
        ·
          refine ⟨937399959703967815248787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4999466451754495014660197 937399959703967815248787)
          ·
            refine ⟨1406099939555951722873181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 937399959703967815248787 1406099939555951722873181)
            ·
              refine ⟨527287477333481896077443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1406099939555951722873181 527287477333481896077443)
              ·
                refine ⟨790931216000222844116165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 527287477333481896077443 790931216000222844116165)
                ·
                  refine ⟨148299603000041783271781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 790931216000222844116165 148299603000041783271781)
                  ·
                    rfl

theorem cell20_324914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 3, 1, 4].length) (baseStart_324914 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_324914 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_324914 prefixEnd_324914 := by exact prefixLift 324914
  have htrace : WordTrace (prefixWord ++ tailWord_324914) baseStart_324914 baseEnd_324914 := by
    simpa [prefixWord, tailWord_324914, baseEnd_324914] using wordTrace_append hprefix tailTrace_324914
  have hstable : (prefixWord ++ tailWord_324914).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_324914).length < 2 ^ (prefixWord ++ tailWord_324914).sum := by decide
  have hdescent : baseEnd_324914 < baseStart_324914 := by decide
  rcases family_descends (prefixWord ++ tailWord_324914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_324924 : List Nat := [2, 2, 2, 2, 1, 5, 2, 1, 3]
def baseStart_324924 : Nat := 118140960795 + 324924 * 2 ^ 59
def prefixEnd_324924 : Nat := 4983230072969 + 3 ^ 40 * 324924 * 2
def baseEnd_324924 : Nat := 148304167272526192938407

theorem tailTrace_324924 : CollatzResearch.WordTrace tailWord_324924 prefixEnd_324924 148304167272526192938407 := by
  unfold tailWord_324924
  simp only [CollatzResearch.WordTrace]
  refine ⟨5925475937431657723158913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7900634583242210297545217 5925475937431657723158913)
  ·
    refine ⟨4444106953073743292369185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5925475937431657723158913 4444106953073743292369185)
    ·
      refine ⟨3333080214805307469276889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4444106953073743292369185 3333080214805307469276889)
      ·
        refine ⟨2499810161103980601957667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3333080214805307469276889 2499810161103980601957667)
        ·
          refine ⟨3749715241655970902936501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2499810161103980601957667 3749715241655970902936501)
          ·
            refine ⟨351535803905247272150297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 3749715241655970902936501 351535803905247272150297)
            ·
              refine ⟨263651852928935454112723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 351535803905247272150297 263651852928935454112723)
              ·
                refine ⟨395477779393403181169085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 263651852928935454112723 395477779393403181169085)
                ·
                  refine ⟨148304167272526192938407, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 395477779393403181169085 148304167272526192938407)
                  ·
                    rfl

theorem cell20_324924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 5, 2, 1, 3].length) (baseStart_324924 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_324924 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_324924 prefixEnd_324924 := by exact prefixLift 324924
  have htrace : WordTrace (prefixWord ++ tailWord_324924) baseStart_324924 baseEnd_324924 := by
    simpa [prefixWord, tailWord_324924, baseEnd_324924] using wordTrace_append hprefix tailTrace_324924
  have hstable : (prefixWord ++ tailWord_324924).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_324924).length < 2 ^ (prefixWord ++ tailWord_324924).sum := by decide
  have hdescent : baseEnd_324924 < baseStart_324924 := by decide
  rcases family_descends (prefixWord ++ tailWord_324924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_324928 : List Nat := [2, 1, 1, 2, 2, 1, 5, 3, 3]
def baseStart_324928 : Nat := 118140960795 + 324928 * 2 ^ 59
def prefixEnd_324928 : Nat := 4983230072969 + 3 ^ 40 * 324928 * 2
def baseEnd_324928 : Nat := 148305992981519956805057

theorem tailTrace_324928 : CollatzResearch.WordTrace tailWord_324928 prefixEnd_324928 148305992981519956805057 := by
  unfold tailWord_324928
  simp only [CollatzResearch.WordTrace]
  refine ⟨5925548883424412064731719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7900731844565882752975625 5925548883424412064731719)
  ·
    refine ⟨8888323325136618097097579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5925548883424412064731719 8888323325136618097097579)
    ·
      refine ⟨13332484987704927145646369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8888323325136618097097579 13332484987704927145646369)
      ·
        refine ⟨9999363740778695359234777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13332484987704927145646369 9999363740778695359234777)
        ·
          refine ⟨7499522805584021519426083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9999363740778695359234777 7499522805584021519426083)
          ·
            refine ⟨11249284208376032279139125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7499522805584021519426083 11249284208376032279139125)
            ·
              refine ⟨1054620394535253026169293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 11249284208376032279139125 1054620394535253026169293)
              ·
                refine ⟨395482647950719884813485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1054620394535253026169293 395482647950719884813485)
                ·
                  refine ⟨148305992981519956805057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 395482647950719884813485 148305992981519956805057)
                  ·
                    rfl

theorem cell20_324928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 5, 3, 3].length) (baseStart_324928 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_324928 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_324928 prefixEnd_324928 := by exact prefixLift 324928
  have htrace : WordTrace (prefixWord ++ tailWord_324928) baseStart_324928 baseEnd_324928 := by
    simpa [prefixWord, tailWord_324928, baseEnd_324928] using wordTrace_append hprefix tailTrace_324928
  have hstable : (prefixWord ++ tailWord_324928).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_324928).length < 2 ^ (prefixWord ++ tailWord_324928).sum := by decide
  have hdescent : baseEnd_324928 < baseStart_324928 := by decide
  rcases family_descends (prefixWord ++ tailWord_324928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_324942 : List Nat := [4, 1, 1, 1, 1, 1, 3, 8]
def baseStart_324942 : Nat := 118140960795 + 324942 * 2 ^ 59
def prefixEnd_324942 : Nat := 4983230072969 + 3 ^ 40 * 324942 * 2
def baseEnd_324942 : Nat := 49437460987666043446111

theorem tailTrace_324942 : CollatzResearch.WordTrace tailWord_324942 prefixEnd_324942 49437460987666043446111 := by
  unfold tailWord_324942
  simp only [CollatzResearch.WordTrace]
  refine ⟨1481451048599763065059135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 7901072259198736346982053 1481451048599763065059135)
  ·
    refine ⟨2222176572899644597588703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1481451048599763065059135 2222176572899644597588703)
    ·
      refine ⟨3333264859349466896383055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2222176572899644597588703 3333264859349466896383055)
      ·
        refine ⟨4999897289024200344574583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3333264859349466896383055 4999897289024200344574583)
        ·
          refine ⟨7499845933536300516861875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4999897289024200344574583 7499845933536300516861875)
          ·
            refine ⟨11249768900304450775292813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7499845933536300516861875 11249768900304450775292813)
            ·
              refine ⟨4218663337614169040734805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11249768900304450775292813 4218663337614169040734805)
              ·
                refine ⟨49437460987666043446111, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 4218663337614169040734805 49437460987666043446111)
                ·
                  rfl

theorem cell20_324942_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 3, 8].length) (baseStart_324942 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_324942 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_324942 prefixEnd_324942 := by exact prefixLift 324942
  have htrace : WordTrace (prefixWord ++ tailWord_324942) baseStart_324942 baseEnd_324942 := by
    simpa [prefixWord, tailWord_324942, baseEnd_324942] using wordTrace_append hprefix tailTrace_324942
  have hstable : (prefixWord ++ tailWord_324942).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_324942).length < 2 ^ (prefixWord ++ tailWord_324942).sum := by decide
  have hdescent : baseEnd_324942 < baseStart_324942 := by decide
  rcases family_descends (prefixWord ++ tailWord_324942) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_324952 : List Nat := [2, 1, 2, 2, 1, 1, 4, 5, 2]
def baseStart_324952 : Nat := 118140960795 + 324952 * 2 ^ 59
def prefixEnd_324952 : Nat := 4983230072969 + 3 ^ 40 * 324952 * 2
def baseEnd_324952 : Nat := 148316947235482540004959

theorem tailTrace_324952 : CollatzResearch.WordTrace tailWord_324952 prefixEnd_324952 148316947235482540004959 := by
  unfold tailWord_324952
  simp only [CollatzResearch.WordTrace]
  refine ⟨5925986559380938114168555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7901315412507917485558073 5925986559380938114168555)
  ·
    refine ⟨8888979839071407171252833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5925986559380938114168555 8888979839071407171252833)
    ·
      refine ⟨6666734879303555378439625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8888979839071407171252833 6666734879303555378439625)
      ·
        refine ⟨5000051159477666533829719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6666734879303555378439625 5000051159477666533829719)
        ·
          refine ⟨7500076739216499800744579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5000051159477666533829719 7500076739216499800744579)
          ·
            refine ⟨11250115108824749701116869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7500076739216499800744579 11250115108824749701116869)
            ·
              refine ⟨2109396582904640568959413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11250115108824749701116869 2109396582904640568959413)
              ·
                refine ⟨197755929647310053339945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2109396582904640568959413 197755929647310053339945)
                ·
                  refine ⟨148316947235482540004959, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 197755929647310053339945 148316947235482540004959)
                  ·
                    rfl

theorem cell20_324952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 4, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 4, 5, 2].length) (baseStart_324952 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_324952 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_324952 prefixEnd_324952 := by exact prefixLift 324952
  have htrace : WordTrace (prefixWord ++ tailWord_324952) baseStart_324952 baseEnd_324952 := by
    simpa [prefixWord, tailWord_324952, baseEnd_324952] using wordTrace_append hprefix tailTrace_324952
  have hstable : (prefixWord ++ tailWord_324952).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_324952).length < 2 ^ (prefixWord ++ tailWord_324952).sum := by decide
  have hdescent : baseEnd_324952 < baseStart_324952 := by decide
  rcases family_descends (prefixWord ++ tailWord_324952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_325018 : List Nat := [3, 1, 1, 4, 1, 1, 9]
def baseStart_325018 : Nat := 118140960795 + 325018 * 2 ^ 59
def prefixEnd_325018 : Nat := 4983230072969 + 3 ^ 40 * 325018 * 2
def baseEnd_325018 : Nat := 16483007937097738200521

theorem tailTrace_325018 : CollatzResearch.WordTrace tailWord_325018 prefixEnd_325018 16483007937097738200521 := by
  unfold tailWord_325018
  simp only [CollatzResearch.WordTrace]
  refine ⟨2963595084130692375059927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7902920224348513000159805 2963595084130692375059927)
  ·
    refine ⟨4445392626196038562589891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2963595084130692375059927 4445392626196038562589891)
    ·
      refine ⟨6668088939294057843884837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4445392626196038562589891 6668088939294057843884837)
      ·
        refine ⟨1250266676117635845728407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6668088939294057843884837 1250266676117635845728407)
        ·
          refine ⟨1875400014176453768592611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1250266676117635845728407 1875400014176453768592611)
          ·
            refine ⟨2813100021264680652888917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1875400014176453768592611 2813100021264680652888917)
            ·
              refine ⟨16483007937097738200521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 2813100021264680652888917 16483007937097738200521)
              ·
                rfl

theorem cell20_325018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 9].length) (baseStart_325018 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_325018 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_325018 prefixEnd_325018 := by exact prefixLift 325018
  have htrace : WordTrace (prefixWord ++ tailWord_325018) baseStart_325018 baseEnd_325018 := by
    simpa [prefixWord, tailWord_325018, baseEnd_325018] using wordTrace_append hprefix tailTrace_325018
  have hstable : (prefixWord ++ tailWord_325018).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_325018).length < 2 ^ (prefixWord ++ tailWord_325018).sum := by decide
  have hdescent : baseEnd_325018 < baseStart_325018 := by decide
  rcases family_descends (prefixWord ++ tailWord_325018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_325021 : List Nat := [1, 4, 2, 1, 3, 1, 3, 2, 3]
def baseStart_325021 : Nat := 118140960795 + 325021 * 2 ^ 59
def prefixEnd_325021 : Nat := 4983230072969 + 3 ^ 40 * 325021 * 2
def baseEnd_325021 : Nat := 148348440715624966704677

theorem tailTrace_325021 : CollatzResearch.WordTrace tailWord_325021 prefixEnd_325021 148348440715624966704677 := by
  unfold tailWord_325021
  simp only [CollatzResearch.WordTrace]
  refine ⟨11854489755511901012598917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7902993170341267341732611 11854489755511901012598917)
  ·
    refine ⟨2222716829158481439862297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 11854489755511901012598917 2222716829158481439862297)
    ·
      refine ⟨1667037621868861079896723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2222716829158481439862297 1667037621868861079896723)
      ·
        refine ⟨2500556432803291619845085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1667037621868861079896723 2500556432803291619845085)
        ·
          refine ⟨937708662301234357441907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2500556432803291619845085 937708662301234357441907)
          ·
            refine ⟨1406562993451851536162861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 937708662301234357441907 1406562993451851536162861)
            ·
              refine ⟨527461122544444326061073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1406562993451851536162861 527461122544444326061073)
              ·
                refine ⟨395595841908333244545805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 527461122544444326061073 395595841908333244545805)
                ·
                  refine ⟨148348440715624966704677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 395595841908333244545805 148348440715624966704677)
                  ·
                    rfl

theorem cell20_325021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 3, 2, 3].length) (baseStart_325021 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_325021 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_325021 prefixEnd_325021 := by exact prefixLift 325021
  have htrace : WordTrace (prefixWord ++ tailWord_325021) baseStart_325021 baseEnd_325021 := by
    simpa [prefixWord, tailWord_325021, baseEnd_325021] using wordTrace_append hprefix tailTrace_325021
  have hstable : (prefixWord ++ tailWord_325021).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_325021).length < 2 ^ (prefixWord ++ tailWord_325021).sum := by decide
  have hdescent : baseEnd_325021 < baseStart_325021 := by decide
  rcases family_descends (prefixWord ++ tailWord_325021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_325063 : List Nat := [1, 1, 4, 1, 1, 3, 1, 1, 7]
def baseStart_325063 : Nat := 118140960795 + 325063 * 2 ^ 59
def prefixEnd_325063 : Nat := 4983230072969 + 3 ^ 40 * 325063 * 2
def baseEnd_325063 : Nat := 148367610660059487304505

theorem tailTrace_325063 : CollatzResearch.WordTrace tailWord_325063 prefixEnd_325063 148367610660059487304505 := by
  unfold tailWord_325063
  simp only [CollatzResearch.WordTrace]
  refine ⟨11856021621359742185627843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7904014414239828123751895 11856021621359742185627843)
  ·
    refine ⟨17784032432039613278441765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11856021621359742185627843 17784032432039613278441765)
    ·
      refine ⟨3334506081007427489707831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 17784032432039613278441765 3334506081007427489707831)
      ·
        refine ⟨5001759121511141234561747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3334506081007427489707831 5001759121511141234561747)
        ·
          refine ⟨7502638682266711851842621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5001759121511141234561747 7502638682266711851842621)
          ·
            refine ⟨2813489505850016944440983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7502638682266711851842621 2813489505850016944440983)
            ·
              refine ⟨4220234258775025416661475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2813489505850016944440983 4220234258775025416661475)
              ·
                refine ⟨6330351388162538124992213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4220234258775025416661475 6330351388162538124992213)
                ·
                  refine ⟨148367610660059487304505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6330351388162538124992213 148367610660059487304505)
                  ·
                    rfl

theorem cell20_325063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 1, 1, 7].length) (baseStart_325063 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_325063 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_325063 prefixEnd_325063 := by exact prefixLift 325063
  have htrace : WordTrace (prefixWord ++ tailWord_325063) baseStart_325063 baseEnd_325063 := by
    simpa [prefixWord, tailWord_325063, baseEnd_325063] using wordTrace_append hprefix tailTrace_325063
  have hstable : (prefixWord ++ tailWord_325063).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_325063).length < 2 ^ (prefixWord ++ tailWord_325063).sum := by decide
  have hdescent : baseEnd_325063 < baseStart_325063 := by decide
  rcases family_descends (prefixWord ++ tailWord_325063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_325132 : List Nat := [2, 2, 1, 2, 5, 8]
def baseStart_325132 : Nat := 118140960795 + 325132 * 2 ^ 59
def prefixEnd_325132 : Nat := 4983230072969 + 3 ^ 40 * 325132 * 2
def baseEnd_325132 : Nat := 5496263116303774592749

theorem tailTrace_325132 : CollatzResearch.WordTrace tailWord_325132 prefixEnd_325132 5496263116303774592749 := by
  unfold tailWord_325132
  simp only [CollatzResearch.WordTrace]
  refine ⟨5929269129054883484944825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7905692172073177979926433 5929269129054883484944825)
  ·
    refine ⟨4446951846791162613708619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5929269129054883484944825 4446951846791162613708619)
    ·
      refine ⟨6670427770186743920562929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4446951846791162613708619 6670427770186743920562929)
      ·
        refine ⟨5002820827640057940422197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6670427770186743920562929 5002820827640057940422197)
        ·
          refine ⟨469014452591255431914581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 5002820827640057940422197 469014452591255431914581)
          ·
            refine ⟨5496263116303774592749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 469014452591255431914581 5496263116303774592749)
            ·
              rfl

theorem cell20_325132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 5, 8].length) (baseStart_325132 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_325132 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_325132 prefixEnd_325132 := by exact prefixLift 325132
  have htrace : WordTrace (prefixWord ++ tailWord_325132) baseStart_325132 baseEnd_325132 := by
    simpa [prefixWord, tailWord_325132, baseEnd_325132] using wordTrace_append hprefix tailTrace_325132
  have hstable : (prefixWord ++ tailWord_325132).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_325132).length < 2 ^ (prefixWord ++ tailWord_325132).sum := by decide
  have hdescent : baseEnd_325132 < baseStart_325132 := by decide
  rcases family_descends (prefixWord ++ tailWord_325132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_325166 : List Nat := [4, 1, 3, 1, 2, 2, 3, 4]
def baseStart_325166 : Nat := 118140960795 + 325166 * 2 ^ 59
def prefixEnd_325166 : Nat := 4983230072969 + 3 ^ 40 * 325166 * 2
def baseEnd_325166 : Nat := 49471540888882968956917

theorem tailTrace_325166 : CollatzResearch.WordTrace tailWord_325166 prefixEnd_325166 49471540888882968956917 := by
  unfold tailWord_325166
  simp only [CollatzResearch.WordTrace]
  refine ⟨1482472292498323847078419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 7906518893324393851084901 1482472292498323847078419)
  ·
    refine ⟨2223708438747485770617629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1482472292498323847078419 2223708438747485770617629)
    ·
      refine ⟨833890664530307163981611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2223708438747485770617629 833890664530307163981611)
      ·
        refine ⟨1250835996795460745972417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 833890664530307163981611 1250835996795460745972417)
        ·
          refine ⟨938126997596595559479313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1250835996795460745972417 938126997596595559479313)
          ·
            refine ⟨703595248197446669609485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 938126997596595559479313 703595248197446669609485)
            ·
              refine ⟨263848218074042501103557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 703595248197446669609485 263848218074042501103557)
              ·
                refine ⟨49471540888882968956917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 263848218074042501103557 49471540888882968956917)
                ·
                  rfl

theorem cell20_325166_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 2, 3, 4].length) (baseStart_325166 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_325166 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_325166 prefixEnd_325166 := by exact prefixLift 325166
  have htrace : WordTrace (prefixWord ++ tailWord_325166) baseStart_325166 baseEnd_325166 := by
    simpa [prefixWord, tailWord_325166, baseEnd_325166] using wordTrace_append hprefix tailTrace_325166
  have hstable : (prefixWord ++ tailWord_325166).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_325166).length < 2 ^ (prefixWord ++ tailWord_325166).sum := by decide
  have hdescent : baseEnd_325166 < baseStart_325166 := by decide
  rcases family_descends (prefixWord ++ tailWord_325166) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_325184 : List Nat := [2, 1, 1, 2, 2, 2, 1, 1, 8]
def baseStart_325184 : Nat := 118140960795 + 325184 * 2 ^ 59
def prefixEnd_325184 : Nat := 4983230072969 + 3 ^ 40 * 325184 * 2
def baseEnd_325184 : Nat := 148422838357120844270677

theorem tailTrace_325184 : CollatzResearch.WordTrace tailWord_325184 prefixEnd_325184 148422838357120844270677 := by
  unfold tailWord_325184
  simp only [CollatzResearch.WordTrace]
  refine ⟨5930217426960689925391303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7906956569280919900521737 5930217426960689925391303)
  ·
    refine ⟨8895326140441034888086955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5930217426960689925391303 8895326140441034888086955)
    ·
      refine ⟨13342989210661552332130433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8895326140441034888086955 13342989210661552332130433)
      ·
        refine ⟨10007241907996164249097825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13342989210661552332130433 10007241907996164249097825)
        ·
          refine ⟨7505431430997123186823369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10007241907996164249097825 7505431430997123186823369)
          ·
            refine ⟨5629073573247842390117527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7505431430997123186823369 5629073573247842390117527)
            ·
              refine ⟨8443610359871763585176291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5629073573247842390117527 8443610359871763585176291)
              ·
                refine ⟨12665415539807645377764437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8443610359871763585176291 12665415539807645377764437)
                ·
                  refine ⟨148422838357120844270677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 12665415539807645377764437 148422838357120844270677)
                  ·
                    rfl

theorem cell20_325184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 1, 1, 8].length) (baseStart_325184 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_325184 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_325184 prefixEnd_325184 := by exact prefixLift 325184
  have htrace : WordTrace (prefixWord ++ tailWord_325184) baseStart_325184 baseEnd_325184 := by
    simpa [prefixWord, tailWord_325184, baseEnd_325184] using wordTrace_append hprefix tailTrace_325184
  have hstable : (prefixWord ++ tailWord_325184).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_325184).length < 2 ^ (prefixWord ++ tailWord_325184).sum := by decide
  have hdescent : baseEnd_325184 < baseStart_325184 := by decide
  rcases family_descends (prefixWord ++ tailWord_325184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_325190 : List Nat := [6, 1, 1, 1, 3, 1, 1, 1, 5]
def baseStart_325190 : Nat := 118140960795 + 325190 * 2 ^ 59
def prefixEnd_325190 : Nat := 4983230072969 + 3 ^ 40 * 325190 * 2
def baseEnd_325190 : Nat := 148425576920611490070653

theorem tailTrace_325190 : CollatzResearch.WordTrace tailWord_325190 prefixEnd_325190 148425576920611490070653 := by
  unfold tailWord_325190
  simp only [CollatzResearch.WordTrace]
  refine ⟨370645427871863839859407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 7907102461266428583667349 370645427871863839859407)
  ·
    refine ⟨555968141807795759789111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 370645427871863839859407 555968141807795759789111)
    ·
      refine ⟨833952212711693639683667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 555968141807795759789111 833952212711693639683667)
      ·
        refine ⟨1250928319067540459525501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 833952212711693639683667 1250928319067540459525501)
        ·
          refine ⟨469098119650327672322063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1250928319067540459525501 469098119650327672322063)
          ·
            refine ⟨703647179475491508483095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 469098119650327672322063 703647179475491508483095)
            ·
              refine ⟨1055470769213237262724643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 703647179475491508483095 1055470769213237262724643)
              ·
                refine ⟨1583206153819855894086965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1055470769213237262724643 1583206153819855894086965)
                ·
                  refine ⟨148425576920611490070653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1583206153819855894086965 148425576920611490070653)
                  ·
                    rfl

theorem cell20_325190_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 3, 1, 1, 1, 5].length) (baseStart_325190 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_325190 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_325190 prefixEnd_325190 := by exact prefixLift 325190
  have htrace : WordTrace (prefixWord ++ tailWord_325190) baseStart_325190 baseEnd_325190 := by
    simpa [prefixWord, tailWord_325190, baseEnd_325190] using wordTrace_append hprefix tailTrace_325190
  have hstable : (prefixWord ++ tailWord_325190).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_325190).length < 2 ^ (prefixWord ++ tailWord_325190).sum := by decide
  have hdescent : baseEnd_325190 < baseStart_325190 := by decide
  rcases family_descends (prefixWord ++ tailWord_325190) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_325197 : List Nat := [1, 6, 1, 1, 3, 1, 2, 1, 4]
def baseStart_325197 : Nat := 118140960795 + 325197 * 2 ^ 59
def prefixEnd_325197 : Nat := 4983230072969 + 3 ^ 40 * 325197 * 2
def baseEnd_325197 : Nat := 148428771911350576837291

theorem tailTrace_325197 : CollatzResearch.WordTrace tailWord_325197 prefixEnd_325197 148428771911350576837291 := by
  unfold tailWord_325197
  simp only [CollatzResearch.WordTrace]
  refine ⟨11860909002874283071005845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7907272668582855380670563 11860909002874283071005845)
  ·
    refine ⟨555980109509732018953399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 11860909002874283071005845 555980109509732018953399)
    ·
      refine ⟨833970164264598028430099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 555980109509732018953399 833970164264598028430099)
      ·
        refine ⟨1250955246396897042645149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 833970164264598028430099 1250955246396897042645149)
        ·
          refine ⟨469108217398836390991931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1250955246396897042645149 469108217398836390991931)
          ·
            refine ⟨703662326098254586487897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 469108217398836390991931 703662326098254586487897)
            ·
              refine ⟨527746744573690939865923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 703662326098254586487897 527746744573690939865923)
              ·
                refine ⟨791620116860536409798885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 527746744573690939865923 791620116860536409798885)
                ·
                  refine ⟨148428771911350576837291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 791620116860536409798885 148428771911350576837291)
                  ·
                    rfl

theorem cell20_325197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 3, 1, 2, 1, 4].length) (baseStart_325197 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_325197 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_325197 prefixEnd_325197 := by exact prefixLift 325197
  have htrace : WordTrace (prefixWord ++ tailWord_325197) baseStart_325197 baseEnd_325197 := by
    simpa [prefixWord, tailWord_325197, baseEnd_325197] using wordTrace_append hprefix tailTrace_325197
  have hstable : (prefixWord ++ tailWord_325197).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_325197).length < 2 ^ (prefixWord ++ tailWord_325197).sum := by decide
  have hdescent : baseEnd_325197 < baseStart_325197 := by decide
  rcases family_descends (prefixWord ++ tailWord_325197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_325201 : List Nat := [1, 2, 2, 1, 3, 2, 4, 1, 4]
def baseStart_325201 : Nat := 118140960795 + 325201 * 2 ^ 59
def prefixEnd_325201 : Nat := 4983230072969 + 3 ^ 40 * 325201 * 2
def baseEnd_325201 : Nat := 148430597620344340703941

theorem tailTrace_325201 : CollatzResearch.WordTrace tailWord_325201 prefixEnd_325201 148430597620344340703941 := by
  unfold tailWord_325201
  simp only [CollatzResearch.WordTrace]
  refine ⟨11861054894859791754151457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7907369929906527836100971 11861054894859791754151457)
  ·
    refine ⟨8895791171144843815613593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11861054894859791754151457 8895791171144843815613593)
    ·
      refine ⟨6671843378358632861710195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8895791171144843815613593 6671843378358632861710195)
      ·
        refine ⟨10007765067537949292565293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6671843378358632861710195 10007765067537949292565293)
        ·
          refine ⟨3752911900326730984711985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10007765067537949292565293 3752911900326730984711985)
          ·
            refine ⟨2814683925245048238533989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3752911900326730984711985 2814683925245048238533989)
            ·
              refine ⟨527753235983446544725123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2814683925245048238533989 527753235983446544725123)
              ·
                refine ⟨791629853975169817087685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 527753235983446544725123 791629853975169817087685)
                ·
                  refine ⟨148430597620344340703941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 791629853975169817087685 148430597620344340703941)
                  ·
                    rfl

theorem cell20_325201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 4, 1, 4].length) (baseStart_325201 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_325201 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_325201 prefixEnd_325201 := by exact prefixLift 325201
  have htrace : WordTrace (prefixWord ++ tailWord_325201) baseStart_325201 baseEnd_325201 := by
    simpa [prefixWord, tailWord_325201, baseEnd_325201] using wordTrace_append hprefix tailTrace_325201
  have hstable : (prefixWord ++ tailWord_325201).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_325201).length < 2 ^ (prefixWord ++ tailWord_325201).sum := by decide
  have hdescent : baseEnd_325201 < baseStart_325201 := by decide
  rcases family_descends (prefixWord ++ tailWord_325201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_325252 : List Nat := [2, 3, 2, 1, 4, 1, 3, 2, 2]
def baseStart_325252 : Nat := 118140960795 + 325252 * 2 ^ 59
def prefixEnd_325252 : Nat := 4983230072969 + 3 ^ 40 * 325252 * 2
def baseEnd_325252 : Nat := 148453875410014830003733

theorem tailTrace_325252 : CollatzResearch.WordTrace tailWord_325252 prefixEnd_325252 148453875410014830003733 := by
  unfold tailWord_325252
  simp only [CollatzResearch.WordTrace]
  refine ⟨5931457508837513732129005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7908610011783351642838673 5931457508837513732129005)
  ·
    refine ⟨2224296565814067649548377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5931457508837513732129005 2224296565814067649548377)
    ·
      refine ⟨1668222424360550737161283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2224296565814067649548377 1668222424360550737161283)
      ·
        refine ⟨2502333636540826105741925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1668222424360550737161283 2502333636540826105741925)
        ·
          refine ⟨469187556851404894826611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2502333636540826105741925 469187556851404894826611)
          ·
            refine ⟨703781335277107342239917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 469187556851404894826611 703781335277107342239917)
            ·
              refine ⟨263918000728915253339969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 703781335277107342239917 263918000728915253339969)
              ·
                refine ⟨197938500546686440004977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 263918000728915253339969 197938500546686440004977)
                ·
                  refine ⟨148453875410014830003733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 197938500546686440004977 148453875410014830003733)
                  ·
                    rfl

theorem cell20_325252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 4, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 4, 1, 3, 2, 2].length) (baseStart_325252 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_325252 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_325252 prefixEnd_325252 := by exact prefixLift 325252
  have htrace : WordTrace (prefixWord ++ tailWord_325252) baseStart_325252 baseEnd_325252 := by
    simpa [prefixWord, tailWord_325252, baseEnd_325252] using wordTrace_append hprefix tailTrace_325252
  have hstable : (prefixWord ++ tailWord_325252).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_325252).length < 2 ^ (prefixWord ++ tailWord_325252).sum := by decide
  have hdescent : baseEnd_325252 < baseStart_325252 := by decide
  rcases family_descends (prefixWord ++ tailWord_325252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_325253 : List Nat := [1, 3, 1, 1, 4, 1, 1, 3, 5]
def baseStart_325253 : Nat := 118140960795 + 325253 * 2 ^ 59
def prefixEnd_325253 : Nat := 4983230072969 + 3 ^ 40 * 325253 * 2
def baseEnd_325253 : Nat := 148454331837263270970395

theorem tailTrace_325253 : CollatzResearch.WordTrace tailWord_325253 prefixEnd_325253 148454331837263270970395 := by
  unfold tailWord_325253
  simp only [CollatzResearch.WordTrace]
  refine ⟨11862951490671404635044413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7908634327114269756696275 11862951490671404635044413)
  ·
    refine ⟨4448606809001776738141655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11862951490671404635044413 4448606809001776738141655)
    ·
      refine ⟨6672910213502665107212483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4448606809001776738141655 6672910213502665107212483)
      ·
        refine ⟨10009365320253997660818725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6672910213502665107212483 10009365320253997660818725)
        ·
          refine ⟨1876755997547624561403511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10009365320253997660818725 1876755997547624561403511)
          ·
            refine ⟨2815133996321436842105267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1876755997547624561403511 2815133996321436842105267)
            ·
              refine ⟨4222700994482155263157901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2815133996321436842105267 4222700994482155263157901)
              ·
                refine ⟨1583512872930808223684213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4222700994482155263157901 1583512872930808223684213)
                ·
                  refine ⟨148454331837263270970395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1583512872930808223684213 148454331837263270970395)
                  ·
                    rfl

theorem cell20_325253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 1, 3, 5].length) (baseStart_325253 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_325253 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_325253 prefixEnd_325253 := by exact prefixLift 325253
  have htrace : WordTrace (prefixWord ++ tailWord_325253) baseStart_325253 baseEnd_325253 := by
    simpa [prefixWord, tailWord_325253, baseEnd_325253] using wordTrace_append hprefix tailTrace_325253
  have hstable : (prefixWord ++ tailWord_325253).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_325253).length < 2 ^ (prefixWord ++ tailWord_325253).sum := by decide
  have hdescent : baseEnd_325253 < baseStart_325253 := by decide
  rcases family_descends (prefixWord ++ tailWord_325253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_325284 : List Nat := [2, 3, 1, 2, 2, 2, 2, 6]
def baseStart_325284 : Nat := 118140960795 + 325284 * 2 ^ 59
def prefixEnd_325284 : Nat := 4983230072969 + 3 ^ 40 * 325284 * 2
def baseEnd_325284 : Nat := 49489493693988313645645

theorem tailTrace_325284 : CollatzResearch.WordTrace tailWord_325284 prefixEnd_325284 49489493693988313645645 := by
  unfold tailWord_325284
  simp only [CollatzResearch.WordTrace]
  refine ⟨5932041076779548464711453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7909388102372731286281937 5932041076779548464711453)
  ·
    refine ⟨2224515403792330674266795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5932041076779548464711453 2224515403792330674266795)
    ·
      refine ⟨3336773105688496011400193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2224515403792330674266795 3336773105688496011400193)
      ·
        refine ⟨2502579829266372008550145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3336773105688496011400193 2502579829266372008550145)
        ·
          refine ⟨1876934871949779006412609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2502579829266372008550145 1876934871949779006412609)
          ·
            refine ⟨1407701153962334254809457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1876934871949779006412609 1407701153962334254809457)
            ·
              refine ⟨1055775865471750691107093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1407701153962334254809457 1055775865471750691107093)
              ·
                refine ⟨49489493693988313645645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1055775865471750691107093 49489493693988313645645)
                ·
                  rfl

theorem cell20_325284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 2, 6].length) (baseStart_325284 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_325284 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_325284 prefixEnd_325284 := by exact prefixLift 325284
  have htrace : WordTrace (prefixWord ++ tailWord_325284) baseStart_325284 baseEnd_325284 := by
    simpa [prefixWord, tailWord_325284, baseEnd_325284] using wordTrace_append hprefix tailTrace_325284
  have hstable : (prefixWord ++ tailWord_325284).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_325284).length < 2 ^ (prefixWord ++ tailWord_325284).sum := by decide
  have hdescent : baseEnd_325284 < baseStart_325284 := by decide
  rcases family_descends (prefixWord ++ tailWord_325284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_325301 : List Nat := [1, 3, 3, 3, 3, 7]
def baseStart_325301 : Nat := 118140960795 + 325301 * 2 ^ 59
def prefixEnd_325301 : Nat := 4983230072969 + 3 ^ 40 * 325301 * 2
def baseEnd_325301 : Nat := 5499120012784756939637

theorem tailTrace_325301 : CollatzResearch.WordTrace tailWord_325301 prefixEnd_325301 5499120012784756939637 := by
  unfold tailWord_325301
  simp only [CollatzResearch.WordTrace]
  refine ⟨11864702194497508832791757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7909801462998339221861171 11864702194497508832791757)
  ·
    refine ⟨4449263322936565812296909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11864702194497508832791757 4449263322936565812296909)
    ·
      refine ⟨1668473746101212179611341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4449263322936565812296909 1668473746101212179611341)
      ·
        refine ⟨625677654787954567354253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1668473746101212179611341 625677654787954567354253)
        ·
          refine ⟨234629120545482962757845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 625677654787954567354253 234629120545482962757845)
          ·
            refine ⟨5499120012784756939637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 234629120545482962757845 5499120012784756939637)
            ·
              rfl

theorem cell20_325301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 3, 7].length) (baseStart_325301 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_325301 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_325301 prefixEnd_325301 := by exact prefixLift 325301
  have htrace : WordTrace (prefixWord ++ tailWord_325301) baseStart_325301 baseEnd_325301 := by
    simpa [prefixWord, tailWord_325301, baseEnd_325301] using wordTrace_append hprefix tailTrace_325301
  have hstable : (prefixWord ++ tailWord_325301).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_325301).length < 2 ^ (prefixWord ++ tailWord_325301).sum := by decide
  have hdescent : baseEnd_325301 < baseStart_325301 := by decide
  rcases family_descends (prefixWord ++ tailWord_325301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_325308 : List Nat := [2, 2, 2, 3, 1, 2, 1, 4, 3]
def baseStart_325308 : Nat := 118140960795 + 325308 * 2 ^ 59
def prefixEnd_325308 : Nat := 4983230072969 + 3 ^ 40 * 325308 * 2
def baseEnd_325308 : Nat := 148479435335927524136837

theorem tailTrace_325308 : CollatzResearch.WordTrace tailWord_325308 prefixEnd_325308 148479435335927524136837 := by
  unfold tailWord_325308
  simp only [CollatzResearch.WordTrace]
  refine ⟨5932478752736074514148289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7909971670314766018864385 5932478752736074514148289)
  ·
    refine ⟨4449359064552055885611217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5932478752736074514148289 4449359064552055885611217)
    ·
      refine ⟨3337019298414041914208413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4449359064552055885611217 3337019298414041914208413)
      ·
        refine ⟨1251382236905265717828155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3337019298414041914208413 1251382236905265717828155)
        ·
          refine ⟨1877073355357898576742233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1251382236905265717828155 1877073355357898576742233)
          ·
            refine ⟨1407805016518423932556675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1877073355357898576742233 1407805016518423932556675)
            ·
              refine ⟨2111707524777635898835013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1407805016518423932556675 2111707524777635898835013)
              ·
                refine ⟨395945160895806731031565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2111707524777635898835013 395945160895806731031565)
                ·
                  refine ⟨148479435335927524136837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 395945160895806731031565 148479435335927524136837)
                  ·
                    rfl

theorem cell20_325308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 1, 4, 3].length) (baseStart_325308 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_325308 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_325308 prefixEnd_325308 := by exact prefixLift 325308
  have htrace : WordTrace (prefixWord ++ tailWord_325308) baseStart_325308 baseEnd_325308 := by
    simpa [prefixWord, tailWord_325308, baseEnd_325308] using wordTrace_append hprefix tailTrace_325308
  have hstable : (prefixWord ++ tailWord_325308).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_325308).length < 2 ^ (prefixWord ++ tailWord_325308).sum := by decide
  have hdescent : baseEnd_325308 < baseStart_325308 := by decide
  rcases family_descends (prefixWord ++ tailWord_325308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_325314 : List Nat := [3, 5, 1, 2, 1, 2, 1, 5]
def baseStart_325314 : Nat := 118140960795 + 325314 * 2 ^ 59
def prefixEnd_325314 : Nat := 4983230072969 + 3 ^ 40 * 325314 * 2
def baseEnd_325314 : Nat := 49494057966472723312271

theorem tailTrace_325314 : CollatzResearch.WordTrace tailWord_325314 prefixEnd_325314 49494057966472723312271 := by
  unfold tailWord_325314
  simp only [CollatzResearch.WordTrace]
  refine ⟨2966294085862603013253749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7910117562300274702009997 2966294085862603013253749)
  ·
    refine ⟨278090070549619032492539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 2966294085862603013253749 278090070549619032492539)
    ·
      refine ⟨417135105824428548738809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 278090070549619032492539 417135105824428548738809)
      ·
        refine ⟨312851329368321411554107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 417135105824428548738809 312851329368321411554107)
        ·
          refine ⟨469276994052482117331161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 312851329368321411554107 469276994052482117331161)
          ·
            refine ⟨351957745539361587998371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 469276994052482117331161 351957745539361587998371)
            ·
              refine ⟨527936618309042381997557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 351957745539361587998371 527936618309042381997557)
              ·
                refine ⟨49494057966472723312271, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 527936618309042381997557 49494057966472723312271)
                ·
                  rfl

theorem cell20_325314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 1, 2, 1, 5].length) (baseStart_325314 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_325314 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_325314 prefixEnd_325314 := by exact prefixLift 325314
  have htrace : WordTrace (prefixWord ++ tailWord_325314) baseStart_325314 baseEnd_325314 := by
    simpa [prefixWord, tailWord_325314, baseEnd_325314] using wordTrace_append hprefix tailTrace_325314
  have hstable : (prefixWord ++ tailWord_325314).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_325314).length < 2 ^ (prefixWord ++ tailWord_325314).sum := by decide
  have hdescent : baseEnd_325314 < baseStart_325314 := by decide
  rcases family_descends (prefixWord ++ tailWord_325314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_325332 : List Nat := [2, 4, 1, 3, 1, 2, 1, 2, 4]
def baseStart_325332 : Nat := 118140960795 + 325332 * 2 ^ 59
def prefixEnd_325332 : Nat := 4983230072969 + 3 ^ 40 * 325332 * 2
def baseEnd_325332 : Nat := 148490389589890107336739

theorem tailTrace_325332 : CollatzResearch.WordTrace tailWord_325332 prefixEnd_325332 148490389589890107336739 := by
  unfold tailWord_325332
  simp only [CollatzResearch.WordTrace]
  refine ⟨5932916428692600563585125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7910555238256800751446833 5932916428692600563585125)
  ·
    refine ⟨1112421830379862605672211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5932916428692600563585125 1112421830379862605672211)
    ·
      refine ⟨1668632745569793908508317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1112421830379862605672211 1668632745569793908508317)
      ·
        refine ⟨625737279588672715690619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1668632745569793908508317 625737279588672715690619)
        ·
          refine ⟨938605919383009073535929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 625737279588672715690619 938605919383009073535929)
          ·
            refine ⟨703954439537256805151947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 938605919383009073535929 703954439537256805151947)
            ·
              refine ⟨1055931659305885207727921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 703954439537256805151947 1055931659305885207727921)
              ·
                refine ⟨791948744479413905795941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1055931659305885207727921 791948744479413905795941)
                ·
                  refine ⟨148490389589890107336739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 791948744479413905795941 148490389589890107336739)
                  ·
                    rfl

theorem cell20_325332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 2, 1, 2, 4].length) (baseStart_325332 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_325332 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_325332 prefixEnd_325332 := by exact prefixLift 325332
  have htrace : WordTrace (prefixWord ++ tailWord_325332) baseStart_325332 baseEnd_325332 := by
    simpa [prefixWord, tailWord_325332, baseEnd_325332] using wordTrace_append hprefix tailTrace_325332
  have hstable : (prefixWord ++ tailWord_325332).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_325332).length < 2 ^ (prefixWord ++ tailWord_325332).sum := by decide
  have hdescent : baseEnd_325332 < baseStart_325332 := by decide
  rcases family_descends (prefixWord ++ tailWord_325332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_325394 : List Nat := [3, 2, 4, 1, 1, 1, 4, 4]
def baseStart_325394 : Nat := 118140960795 + 325394 * 2 ^ 59
def prefixEnd_325394 : Nat := 4983230072969 + 3 ^ 40 * 325394 * 2
def baseEnd_325394 : Nat := 49506229359764482423273

theorem tailTrace_325394 : CollatzResearch.WordTrace tailWord_325394 prefixEnd_325394 49506229359764482423273 := by
  unfold tailWord_325394
  simp only [CollatzResearch.WordTrace]
  refine ⟨2967023545790146428981809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7912062788773723810618157 2967023545790146428981809)
  ·
    refine ⟨2225267659342609821736357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2967023545790146428981809 2225267659342609821736357)
    ·
      refine ⟨417237686126739341575567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2225267659342609821736357 417237686126739341575567)
      ·
        refine ⟨625856529190109012363351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 417237686126739341575567 625856529190109012363351)
        ·
          refine ⟨938784793785163518545027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 625856529190109012363351 938784793785163518545027)
          ·
            refine ⟨1408177190677745277817541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 938784793785163518545027 1408177190677745277817541)
            ·
              refine ⟨264033223252077239590789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1408177190677745277817541 264033223252077239590789)
              ·
                refine ⟨49506229359764482423273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 264033223252077239590789 49506229359764482423273)
                ·
                  rfl

theorem cell20_325394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 4, 4].length) (baseStart_325394 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_325394 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_325394 prefixEnd_325394 := by exact prefixLift 325394
  have htrace : WordTrace (prefixWord ++ tailWord_325394) baseStart_325394 baseEnd_325394 := by
    simpa [prefixWord, tailWord_325394, baseEnd_325394] using wordTrace_append hprefix tailTrace_325394
  have hstable : (prefixWord ++ tailWord_325394).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_325394).length < 2 ^ (prefixWord ++ tailWord_325394).sum := by decide
  have hdescent : baseEnd_325394 < baseStart_325394 := by decide
  rcases family_descends (prefixWord ++ tailWord_325394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_325425 : List Nat := [1, 2, 2, 3, 2, 3, 3, 2, 2]
def baseStart_325425 : Nat := 118140960795 + 325425 * 2 ^ 59
def prefixEnd_325425 : Nat := 4983230072969 + 3 ^ 40 * 325425 * 2
def baseEnd_325425 : Nat := 148532837323995117236359

theorem tailTrace_325425 : CollatzResearch.WordTrace tailWord_325425 prefixEnd_325425 148532837323995117236359 := by
  unfold tailWord_325425
  simp only [CollatzResearch.WordTrace]
  refine ⟨11869224846048278010305729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7912816564032185340203819 11869224846048278010305729)
  ·
    refine ⟨8901918634536208507729297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11869224846048278010305729 8901918634536208507729297)
    ·
      refine ⟨6676438975902156380796973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8901918634536208507729297 6676438975902156380796973)
      ·
        refine ⟨2503664615963308642798865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6676438975902156380796973 2503664615963308642798865)
        ·
          refine ⟨1877748461972481482099149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2503664615963308642798865 1877748461972481482099149)
          ·
            refine ⟨704155673239680555787181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1877748461972481482099149 704155673239680555787181)
            ·
              refine ⟨264058377464880208420193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 704155673239680555787181 264058377464880208420193)
              ·
                refine ⟨198043783098660156315145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 264058377464880208420193 198043783098660156315145)
                ·
                  refine ⟨148532837323995117236359, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 198043783098660156315145 148532837323995117236359)
                  ·
                    rfl

theorem cell20_325425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 3, 3, 2, 2].length) (baseStart_325425 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_325425 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_325425 prefixEnd_325425 := by exact prefixLift 325425
  have htrace : WordTrace (prefixWord ++ tailWord_325425) baseStart_325425 baseEnd_325425 := by
    simpa [prefixWord, tailWord_325425, baseEnd_325425] using wordTrace_append hprefix tailTrace_325425
  have hstable : (prefixWord ++ tailWord_325425).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_325425).length < 2 ^ (prefixWord ++ tailWord_325425).sum := by decide
  have hdescent : baseEnd_325425 < baseStart_325425 := by decide
  rcases family_descends (prefixWord ++ tailWord_325425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_325450 : List Nat := [3, 1, 2, 1, 1, 1, 4, 1, 6]
def baseStart_325450 : Nat := 118140960795 + 325450 * 2 ^ 59
def prefixEnd_325450 : Nat := 4983230072969 + 3 ^ 40 * 325450 * 2
def baseEnd_325450 : Nat := 148544248005206141402923

theorem tailTrace_325450 : CollatzResearch.WordTrace tailWord_325450 prefixEnd_325450 148544248005206141402923 := by
  unfold tailWord_325450
  simp only [CollatzResearch.WordTrace]
  refine ⟨2967534167739426819991451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7913424447305138186643869 2967534167739426819991451)
  ·
    refine ⟨4451301251609140229987177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2967534167739426819991451 4451301251609140229987177)
    ·
      refine ⟨3338475938706855172490383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4451301251609140229987177 3338475938706855172490383)
      ·
        refine ⟨5007713908060282758735575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3338475938706855172490383 5007713908060282758735575)
        ·
          refine ⟨7511570862090424138103363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5007713908060282758735575 7511570862090424138103363)
          ·
            refine ⟨11267356293135636207155045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7511570862090424138103363 11267356293135636207155045)
            ·
              refine ⟨2112629304962931788841571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11267356293135636207155045 2112629304962931788841571)
              ·
                refine ⟨3168943957444397683262357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2112629304962931788841571 3168943957444397683262357)
                ·
                  refine ⟨148544248005206141402923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3168943957444397683262357 148544248005206141402923)
                  ·
                    rfl

theorem cell20_325450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 4, 1, 6].length) (baseStart_325450 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_325450 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_325450 prefixEnd_325450 := by exact prefixLift 325450
  have htrace : WordTrace (prefixWord ++ tailWord_325450) baseStart_325450 baseEnd_325450 := by
    simpa [prefixWord, tailWord_325450, baseEnd_325450] using wordTrace_append hprefix tailTrace_325450
  have hstable : (prefixWord ++ tailWord_325450).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_325450).length < 2 ^ (prefixWord ++ tailWord_325450).sum := by decide
  have hdescent : baseEnd_325450 < baseStart_325450 := by decide
  rcases family_descends (prefixWord ++ tailWord_325450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_325453 : List Nat := [1, 6, 1, 2, 1, 1, 2, 6]
def baseStart_325453 : Nat := 118140960795 + 325453 * 2 ^ 59
def prefixEnd_325453 : Nat := 4983230072969 + 3 ^ 40 * 325453 * 2
def baseEnd_325453 : Nat := 49515205762317154767637

theorem tailTrace_325453 : CollatzResearch.WordTrace tailWord_325453 prefixEnd_325453 49515205762317154767637 := by
  unfold tailWord_325453
  simp only [CollatzResearch.WordTrace]
  refine ⟨11870246089946838792325013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7913497393297892528216675 11870246089946838792325013)
  ·
    refine ⟨556417785466258068390235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 11870246089946838792325013 556417785466258068390235)
    ·
      refine ⟨834626678199387102585353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 556417785466258068390235 834626678199387102585353)
      ·
        refine ⟨625970008649540326939015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 834626678199387102585353 625970008649540326939015)
        ·
          refine ⟨938955012974310490408523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 625970008649540326939015 938955012974310490408523)
          ·
            refine ⟨1408432519461465735612785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 938955012974310490408523 1408432519461465735612785)
            ·
              refine ⟨1056324389596099301709589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1408432519461465735612785 1056324389596099301709589)
              ·
                refine ⟨49515205762317154767637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1056324389596099301709589 49515205762317154767637)
                ·
                  rfl

theorem cell20_325453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 2, 6].length) (baseStart_325453 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_325453 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_325453 prefixEnd_325453 := by exact prefixLift 325453
  have htrace : WordTrace (prefixWord ++ tailWord_325453) baseStart_325453 baseEnd_325453 := by
    simpa [prefixWord, tailWord_325453, baseEnd_325453] using wordTrace_append hprefix tailTrace_325453
  have hstable : (prefixWord ++ tailWord_325453).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_325453).length < 2 ^ (prefixWord ++ tailWord_325453).sum := by decide
  have hdescent : baseEnd_325453 < baseStart_325453 := by decide
  rcases family_descends (prefixWord ++ tailWord_325453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_325474 : List Nat := [3, 3, 2, 1, 2, 9]
def baseStart_325474 : Nat := 118140960795 + 325474 * 2 ^ 59
def prefixEnd_325474 : Nat := 4983230072969 + 3 ^ 40 * 325474 * 2
def baseEnd_325474 : Nat := 5502044528117360170475

theorem tailTrace_325474 : CollatzResearch.WordTrace tailWord_325474 prefixEnd_325474 5502044528117360170475 := by
  unfold tailWord_325474
  simp only [CollatzResearch.WordTrace]
  refine ⟨2967753005717689844709869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7914008015247172919226317 2967753005717689844709869)
  ·
    refine ⟨1112907377144133691766201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2967753005717689844709869 1112907377144133691766201)
    ·
      refine ⟨834680532858100268824651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1112907377144133691766201 834680532858100268824651)
      ·
        refine ⟨1252020799287150403236977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 834680532858100268824651 1252020799287150403236977)
        ·
          refine ⟨939015599465362802427733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1252020799287150403236977 939015599465362802427733)
          ·
            refine ⟨5502044528117360170475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 939015599465362802427733 5502044528117360170475)
            ·
              rfl

theorem cell20_325474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 9].length) (baseStart_325474 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_325474 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_325474 prefixEnd_325474 := by exact prefixLift 325474
  have htrace : WordTrace (prefixWord ++ tailWord_325474) baseStart_325474 baseEnd_325474 := by
    simpa [prefixWord, tailWord_325474, baseEnd_325474] using wordTrace_append hprefix tailTrace_325474
  have hstable : (prefixWord ++ tailWord_325474).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_325474).length < 2 ^ (prefixWord ++ tailWord_325474).sum := by decide
  have hdescent : baseEnd_325474 < baseStart_325474 := by decide
  rcases family_descends (prefixWord ++ tailWord_325474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_325484 : List Nat := [2, 2, 1, 1, 4, 3, 1, 4, 2]
def baseStart_325484 : Nat := 118140960795 + 325484 * 2 ^ 59
def prefixEnd_325484 : Nat := 4983230072969 + 3 ^ 40 * 325484 * 2
def baseEnd_325484 : Nat := 148559766531653134269451

theorem tailTrace_325484 : CollatzResearch.WordTrace tailWord_325484 prefixEnd_325484 148559766531653134269451 := by
  unfold tailWord_325484
  simp only [CollatzResearch.WordTrace]
  refine ⟨5935688376417265543351753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7914251168556354057802337 5935688376417265543351753)
  ·
    refine ⟨4451766282312949157513815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5935688376417265543351753 4451766282312949157513815)
    ·
      refine ⟨6677649423469423736270723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4451766282312949157513815 6677649423469423736270723)
      ·
        refine ⟨10016474135204135604406085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6677649423469423736270723 10016474135204135604406085)
        ·
          refine ⟨1878088900350775425826141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10016474135204135604406085 1878088900350775425826141)
          ·
            refine ⟨704283337631540784684803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1878088900350775425826141 704283337631540784684803)
            ·
              refine ⟨1056425006447311177027205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 704283337631540784684803 1056425006447311177027205)
              ·
                refine ⟨198079688708870845692601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1056425006447311177027205 198079688708870845692601)
                ·
                  refine ⟨148559766531653134269451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 198079688708870845692601 148559766531653134269451)
                  ·
                    rfl

theorem cell20_325484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 3, 1, 4, 2].length) (baseStart_325484 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_325484 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_325484 prefixEnd_325484 := by exact prefixLift 325484
  have htrace : WordTrace (prefixWord ++ tailWord_325484) baseStart_325484 baseEnd_325484 := by
    simpa [prefixWord, tailWord_325484, baseEnd_325484] using wordTrace_append hprefix tailTrace_325484
  have hstable : (prefixWord ++ tailWord_325484).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_325484).length < 2 ^ (prefixWord ++ tailWord_325484).sum := by decide
  have hdescent : baseEnd_325484 < baseStart_325484 := by decide
  rcases family_descends (prefixWord ++ tailWord_325484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_325488 : List Nat := [2, 1, 1, 1, 4, 1, 1, 5, 4]
def baseStart_325488 : Nat := 118140960795 + 325488 * 2 ^ 59
def prefixEnd_325488 : Nat := 4983230072969 + 3 ^ 40 * 325488 * 2
def baseEnd_325488 : Nat := 148561592240646898136101

theorem tailTrace_325488 : CollatzResearch.WordTrace tailWord_325488 prefixEnd_325488 148561592240646898136101 := by
  unfold tailWord_325488
  simp only [CollatzResearch.WordTrace]
  refine ⟨5935761322410019884924559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7914348429880026513232745 5935761322410019884924559)
  ·
    refine ⟨8903641983615029827386839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5935761322410019884924559 8903641983615029827386839)
    ·
      refine ⟨13355462975422544741080259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8903641983615029827386839 13355462975422544741080259)
      ·
        refine ⟨20033194463133817111620389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13355462975422544741080259 20033194463133817111620389)
        ·
          refine ⟨3756223961837590708428823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 20033194463133817111620389 3756223961837590708428823)
          ·
            refine ⟨5634335942756386062643235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3756223961837590708428823 5634335942756386062643235)
            ·
              refine ⟨8451503914134579093964853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5634335942756386062643235 8451503914134579093964853)
              ·
                refine ⟨792328491950116790059205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 8451503914134579093964853 792328491950116790059205)
                ·
                  refine ⟨148561592240646898136101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 792328491950116790059205 148561592240646898136101)
                  ·
                    rfl

theorem cell20_325488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 1, 5, 4].length) (baseStart_325488 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_325488 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_325488 prefixEnd_325488 := by exact prefixLift 325488
  have htrace : WordTrace (prefixWord ++ tailWord_325488) baseStart_325488 baseEnd_325488 := by
    simpa [prefixWord, tailWord_325488, baseEnd_325488] using wordTrace_append hprefix tailTrace_325488
  have hstable : (prefixWord ++ tailWord_325488).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_325488).length < 2 ^ (prefixWord ++ tailWord_325488).sum := by decide
  have hdescent : baseEnd_325488 < baseStart_325488 := by decide
  rcases family_descends (prefixWord ++ tailWord_325488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_325518 : List Nat := [4, 1, 1, 5, 1, 1, 2, 3, 2]
def baseStart_325518 : Nat := 118140960795 + 325518 * 2 ^ 59
def prefixEnd_325518 : Nat := 4983230072969 + 3 ^ 40 * 325518 * 2
def baseEnd_325518 : Nat := 148575285058100127135979

theorem tailTrace_325518 : CollatzResearch.WordTrace tailWord_325518 prefixEnd_325518 148575285058100127135979 := by
  unfold tailWord_325518
  simp only [CollatzResearch.WordTrace]
  refine ⟨1484077104338919361680151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 7915077889807569928960805 1484077104338919361680151)
  ·
    refine ⟨2226115656508379042520227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1484077104338919361680151 2226115656508379042520227)
    ·
      refine ⟨3339173484762568563780341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2226115656508379042520227 3339173484762568563780341)
      ·
        refine ⟨313047514196490802854407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 3339173484762568563780341 313047514196490802854407)
        ·
          refine ⟨469571271294736204281611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 313047514196490802854407 469571271294736204281611)
          ·
            refine ⟨704356906942104306422417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 469571271294736204281611 704356906942104306422417)
            ·
              refine ⟨528267680206578229816813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 704356906942104306422417 528267680206578229816813)
              ·
                refine ⟨198100380077466836181305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 528267680206578229816813 198100380077466836181305)
                ·
                  refine ⟨148575285058100127135979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 198100380077466836181305 148575285058100127135979)
                  ·
                    rfl

theorem cell20_325518_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 1, 1, 2, 3, 2].length) (baseStart_325518 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_325518 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_325518 prefixEnd_325518 := by exact prefixLift 325518
  have htrace : WordTrace (prefixWord ++ tailWord_325518) baseStart_325518 baseEnd_325518 := by
    simpa [prefixWord, tailWord_325518, baseEnd_325518] using wordTrace_append hprefix tailTrace_325518
  have hstable : (prefixWord ++ tailWord_325518).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_325518).length < 2 ^ (prefixWord ++ tailWord_325518).sum := by decide
  have hdescent : baseEnd_325518 < baseStart_325518 := by decide
  rcases family_descends (prefixWord ++ tailWord_325518) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_325543 : List Nat := [1, 1, 6, 1, 2, 1, 1, 3, 4]
def baseStart_325543 : Nat := 118140960795 + 325543 * 2 ^ 59
def prefixEnd_325543 : Nat := 4983230072969 + 3 ^ 40 * 325543 * 2
def baseEnd_325543 : Nat := 148586695739311151302543

theorem tailTrace_325543 : CollatzResearch.WordTrace tailWord_325543 prefixEnd_325543 148586695739311151302543 := by
  unfold tailWord_325543
  simp only [CollatzResearch.WordTrace]
  refine ⟨11873528659620784163101283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7915685773080522775400855 11873528659620784163101283)
  ·
    refine ⟨17810292989431176244651925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11873528659620784163101283 17810292989431176244651925)
    ·
      refine ⟨834857483879586386468059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 17810292989431176244651925 834857483879586386468059)
      ·
        refine ⟨1252286225819379579702089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 834857483879586386468059 1252286225819379579702089)
        ·
          refine ⟨939214669364534684776567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1252286225819379579702089 939214669364534684776567)
          ·
            refine ⟨1408822004046802027164851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 939214669364534684776567 1408822004046802027164851)
            ·
              refine ⟨2113233006070203040747277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1408822004046802027164851 2113233006070203040747277)
              ·
                refine ⟨792462377276326140280229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2113233006070203040747277 792462377276326140280229)
                ·
                  refine ⟨148586695739311151302543, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 792462377276326140280229 148586695739311151302543)
                  ·
                    rfl

theorem cell20_325543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 1, 3, 4].length) (baseStart_325543 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_325543 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_325543 prefixEnd_325543 := by exact prefixLift 325543
  have htrace : WordTrace (prefixWord ++ tailWord_325543) baseStart_325543 baseEnd_325543 := by
    simpa [prefixWord, tailWord_325543, baseEnd_325543] using wordTrace_append hprefix tailTrace_325543
  have hstable : (prefixWord ++ tailWord_325543).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_325543).length < 2 ^ (prefixWord ++ tailWord_325543).sum := by decide
  have hdescent : baseEnd_325543 < baseStart_325543 := by decide
  rcases family_descends (prefixWord ++ tailWord_325543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_325553 : List Nat := [1, 2, 2, 4, 2, 2, 3, 1, 3]
def baseStart_325553 : Nat := 118140960795 + 325553 * 2 ^ 59
def prefixEnd_325553 : Nat := 4983230072969 + 3 ^ 40 * 325553 * 2
def baseEnd_325553 : Nat := 148591260011795560969169

theorem tailTrace_325553 : CollatzResearch.WordTrace tailWord_325553 prefixEnd_325553 148591260011795560969169 := by
  unfold tailWord_325553
  simp only [CollatzResearch.WordTrace]
  refine ⟨11873893389584555870965313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7915928926389703913976875 11873893389584555870965313)
  ·
    refine ⟨8905420042188416903223985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11873893389584555870965313 8905420042188416903223985)
    ·
      refine ⟨6679065031641312677417989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8905420042188416903223985 6679065031641312677417989)
      ·
        refine ⟨1252324693432746127015873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6679065031641312677417989 1252324693432746127015873)
        ·
          refine ⟨939243520074559595261905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1252324693432746127015873 939243520074559595261905)
          ·
            refine ⟨704432640055919696446429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 939243520074559595261905 704432640055919696446429)
            ·
              refine ⟨264162240020969886167411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 704432640055919696446429 264162240020969886167411)
              ·
                refine ⟨396243360031454829251117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 264162240020969886167411 396243360031454829251117)
                ·
                  refine ⟨148591260011795560969169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 396243360031454829251117 148591260011795560969169)
                  ·
                    rfl

theorem cell20_325553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 2, 3, 1, 3].length) (baseStart_325553 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_325553 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_325553 prefixEnd_325553 := by exact prefixLift 325553
  have htrace : WordTrace (prefixWord ++ tailWord_325553) baseStart_325553 baseEnd_325553 := by
    simpa [prefixWord, tailWord_325553, baseEnd_325553] using wordTrace_append hprefix tailTrace_325553
  have hstable : (prefixWord ++ tailWord_325553).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_325553).length < 2 ^ (prefixWord ++ tailWord_325553).sum := by decide
  have hdescent : baseEnd_325553 < baseStart_325553 := by decide
  rcases family_descends (prefixWord ++ tailWord_325553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_325645 : List Nat := [1, 7, 1, 2, 2, 1, 2, 2, 2]
def baseStart_325645 : Nat := 118140960795 + 325645 * 2 ^ 59
def prefixEnd_325645 : Nat := 4983230072969 + 3 ^ 40 * 325645 * 2
def baseEnd_325645 : Nat := 148633251318652129902127

theorem tailTrace_325645 : CollatzResearch.WordTrace tailWord_325645 prefixEnd_325645 148633251318652129902127 := by
  unfold tailWord_325645
  simp only [CollatzResearch.WordTrace]
  refine ⟨11877248905251255583314389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7918165936834170388876259 11877248905251255583314389)
  ·
    refine ⟨278373021216826302733931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 11877248905251255583314389 278373021216826302733931)
    ·
      refine ⟨417559531825239454100897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 278373021216826302733931 417559531825239454100897)
      ·
        refine ⟨313169648868929590575673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 417559531825239454100897 313169648868929590575673)
        ·
          refine ⟨234877236651697192931755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 313169648868929590575673 234877236651697192931755)
          ·
            refine ⟨352315854977545789397633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 234877236651697192931755 352315854977545789397633)
            ·
              refine ⟨264236891233159342048225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 352315854977545789397633 264236891233159342048225)
              ·
                refine ⟨198177668424869506536169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 264236891233159342048225 198177668424869506536169)
                ·
                  refine ⟨148633251318652129902127, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 198177668424869506536169 148633251318652129902127)
                  ·
                    rfl

theorem cell20_325645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 2, 1, 2, 2, 2].length) (baseStart_325645 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_325645 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_325645 prefixEnd_325645 := by exact prefixLift 325645
  have htrace : WordTrace (prefixWord ++ tailWord_325645) baseStart_325645 baseEnd_325645 := by
    simpa [prefixWord, tailWord_325645, baseEnd_325645] using wordTrace_append hprefix tailTrace_325645
  have hstable : (prefixWord ++ tailWord_325645).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_325645).length < 2 ^ (prefixWord ++ tailWord_325645).sum := by decide
  have hdescent : baseEnd_325645 < baseStart_325645 := by decide
  rcases family_descends (prefixWord ++ tailWord_325645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_325685 : List Nat := [1, 3, 3, 1, 1, 1, 2, 8]
def baseStart_325685 : Nat := 118140960795 + 325685 * 2 ^ 59
def prefixEnd_325685 : Nat := 4983230072969 + 3 ^ 40 * 325685 * 2
def baseEnd_325685 : Nat := 49550502802863256189543

theorem tailTrace_325685 : CollatzResearch.WordTrace tailWord_325685 prefixEnd_325685 49550502802863256189543 := by
  unfold tailWord_325685
  simp only [CollatzResearch.WordTrace]
  refine ⟨11878707825106342414770509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7919138550070894943180339 11878707825106342414770509)
  ·
    refine ⟨4454515434414878405538941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11878707825106342414770509 4454515434414878405538941)
    ·
      refine ⟨1670443287905579402077103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4454515434414878405538941 1670443287905579402077103)
      ·
        refine ⟨2505664931858369103115655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1670443287905579402077103 2505664931858369103115655)
        ·
          refine ⟨3758497397787553654673483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2505664931858369103115655 3758497397787553654673483)
          ·
            refine ⟨5637746096681330482010225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3758497397787553654673483 5637746096681330482010225)
            ·
              refine ⟨4228309572510997861507669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5637746096681330482010225 4228309572510997861507669)
              ·
                refine ⟨49550502802863256189543, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 4228309572510997861507669 49550502802863256189543)
                ·
                  rfl

theorem cell20_325685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 2, 8].length) (baseStart_325685 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_325685 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_325685 prefixEnd_325685 := by exact prefixLift 325685
  have htrace : WordTrace (prefixWord ++ tailWord_325685) baseStart_325685 baseEnd_325685 := by
    simpa [prefixWord, tailWord_325685, baseEnd_325685] using wordTrace_append hprefix tailTrace_325685
  have hstable : (prefixWord ++ tailWord_325685).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_325685).length < 2 ^ (prefixWord ++ tailWord_325685).sum := by decide
  have hdescent : baseEnd_325685 < baseStart_325685 := by decide
  rcases family_descends (prefixWord ++ tailWord_325685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_325695 : List Nat := [1, 1, 2, 2, 3, 1, 3, 5, 2]
def baseStart_325695 : Nat := 118140960795 + 325695 * 2 ^ 59
def prefixEnd_325695 : Nat := 4983230072969 + 3 ^ 40 * 325695 * 2
def baseEnd_325695 : Nat := 148656072681074178235255

theorem tailTrace_325695 : CollatzResearch.WordTrace tailWord_325695 prefixEnd_325695 148656072681074178235255 := by
  unfold tailWord_325695
  simp only [CollatzResearch.WordTrace]
  refine ⟨11879072555070114122634539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7919381703380076081756359 11879072555070114122634539)
  ·
    refine ⟨17818608832605171183951809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11879072555070114122634539 17818608832605171183951809)
    ·
      refine ⟨13363956624453878387963857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17818608832605171183951809 13363956624453878387963857)
      ·
        refine ⟨10022967468340408790972893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13363956624453878387963857 10022967468340408790972893)
        ·
          refine ⟨3758612800627653296614835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10022967468340408790972893 3758612800627653296614835)
          ·
            refine ⟨5637919200941479944922253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3758612800627653296614835 5637919200941479944922253)
            ·
              refine ⟨2114219700353054979345845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5637919200941479944922253 2114219700353054979345845)
              ·
                refine ⟨198208096908098904313673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2114219700353054979345845 198208096908098904313673)
                ·
                  refine ⟨148656072681074178235255, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 198208096908098904313673 148656072681074178235255)
                  ·
                    rfl

theorem cell20_325695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 3, 5, 2].length) (baseStart_325695 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_325695 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_325695 prefixEnd_325695 := by exact prefixLift 325695
  have htrace : WordTrace (prefixWord ++ tailWord_325695) baseStart_325695 baseEnd_325695 := by
    simpa [prefixWord, tailWord_325695, baseEnd_325695] using wordTrace_append hprefix tailTrace_325695
  have hstable : (prefixWord ++ tailWord_325695).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_325695).length < 2 ^ (prefixWord ++ tailWord_325695).sum := by decide
  have hdescent : baseEnd_325695 < baseStart_325695 := by decide
  rcases family_descends (prefixWord ++ tailWord_325695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_325740 : List Nat := [2, 2, 1, 1, 3, 3, 4, 4]
def baseStart_325740 : Nat := 118140960795 + 325740 * 2 ^ 59
def prefixEnd_325740 : Nat := 4983230072969 + 3 ^ 40 * 325740 * 2
def baseEnd_325740 : Nat := 49558870635751340578357

theorem tailTrace_325740 : CollatzResearch.WordTrace tailWord_325740 prefixEnd_325740 49558870635751340578357 := by
  unfold tailWord_325740
  simp only [CollatzResearch.WordTrace]
  refine ⟨5940356919953543404011337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7920475893271391205348449 5940356919953543404011337)
  ·
    refine ⟨4455267689965157553008503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5940356919953543404011337 4455267689965157553008503)
    ·
      refine ⟨6682901534947736329512755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4455267689965157553008503 6682901534947736329512755)
      ·
        refine ⟨10024352302421604494269133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6682901534947736329512755 10024352302421604494269133)
        ·
          refine ⟨3759132113408101685350925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10024352302421604494269133 3759132113408101685350925)
          ·
            refine ⟨1409674542528038132006597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3759132113408101685350925 1409674542528038132006597)
            ·
              refine ⟨264313976724007149751237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1409674542528038132006597 264313976724007149751237)
              ·
                refine ⟨49558870635751340578357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 264313976724007149751237 49558870635751340578357)
                ·
                  rfl

theorem cell20_325740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 4, 4].length) (baseStart_325740 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_325740 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_325740 prefixEnd_325740 := by exact prefixLift 325740
  have htrace : WordTrace (prefixWord ++ tailWord_325740) baseStart_325740 baseEnd_325740 := by
    simpa [prefixWord, tailWord_325740, baseEnd_325740] using wordTrace_append hprefix tailTrace_325740
  have hstable : (prefixWord ++ tailWord_325740).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_325740).length < 2 ^ (prefixWord ++ tailWord_325740).sum := by decide
  have hdescent : baseEnd_325740 < baseStart_325740 := by decide
  rcases family_descends (prefixWord ++ tailWord_325740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_325778 : List Nat := [3, 2, 3, 1, 1, 1, 4, 5]
def baseStart_325778 : Nat := 118140960795 + 325778 * 2 ^ 59
def prefixEnd_325778 : Nat := 4983230072969 + 3 ^ 40 * 325778 * 2
def baseEnd_325778 : Nat := 49564652047564926156083

theorem tailTrace_325778 : CollatzResearch.WordTrace tailWord_325778 prefixEnd_325778 49564652047564926156083 := by
  unfold tailWord_325778
  simp only [CollatzResearch.WordTrace]
  refine ⟨2970524953442354824476497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7921399875846279531937325 2970524953442354824476497)
  ·
    refine ⟨2227893715081766118357373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2970524953442354824476497 2227893715081766118357373)
    ·
      refine ⟨835460143155662294384015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2227893715081766118357373 835460143155662294384015)
      ·
        refine ⟨1253190214733493441576023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 835460143155662294384015 1253190214733493441576023)
        ·
          refine ⟨1879785322100240162364035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1253190214733493441576023 1879785322100240162364035)
          ·
            refine ⟨2819677983150360243546053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1879785322100240162364035 2819677983150360243546053)
            ·
              refine ⟨528689621840692545664885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2819677983150360243546053 528689621840692545664885)
              ·
                refine ⟨49564652047564926156083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 528689621840692545664885 49564652047564926156083)
                ·
                  rfl

theorem cell20_325778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 4, 5].length) (baseStart_325778 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_325778 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_325778 prefixEnd_325778 := by exact prefixLift 325778
  have htrace : WordTrace (prefixWord ++ tailWord_325778) baseStart_325778 baseEnd_325778 := by
    simpa [prefixWord, tailWord_325778, baseEnd_325778] using wordTrace_append hprefix tailTrace_325778
  have hstable : (prefixWord ++ tailWord_325778).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_325778).length < 2 ^ (prefixWord ++ tailWord_325778).sum := by decide
  have hdescent : baseEnd_325778 < baseStart_325778 := by decide
  rcases family_descends (prefixWord ++ tailWord_325778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_325812 : List Nat := [2, 5, 3, 1, 1, 8]
def baseStart_325812 : Nat := 118140960795 + 325812 * 2 ^ 59
def prefixEnd_325812 : Nat := 4983230072969 + 3 ^ 40 * 325812 * 2
def baseEnd_325812 : Nat := 5507758321079324864251

theorem tailTrace_325812 : CollatzResearch.WordTrace tailWord_325812 prefixEnd_325812 5507758321079324864251 := by
  unfold tailWord_325812
  simp only [CollatzResearch.WordTrace]
  refine ⟨5941669947823121552321845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7922226597097495403095793 5941669947823121552321845)
  ·
    refine ⟨557031557608417645530173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 5941669947823121552321845 557031557608417645530173)
    ·
      refine ⟨208886834103156617073815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 557031557608417645530173 208886834103156617073815)
      ·
        refine ⟨313330251154734925610723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 208886834103156617073815 313330251154734925610723)
        ·
          refine ⟨469995376732102388416085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 313330251154734925610723 469995376732102388416085)
          ·
            refine ⟨5507758321079324864251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 469995376732102388416085 5507758321079324864251)
            ·
              rfl

theorem cell20_325812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 1, 8].length) (baseStart_325812 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_325812 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_325812 prefixEnd_325812 := by exact prefixLift 325812
  have htrace : WordTrace (prefixWord ++ tailWord_325812) baseStart_325812 baseEnd_325812 := by
    simpa [prefixWord, tailWord_325812, baseEnd_325812] using wordTrace_append hprefix tailTrace_325812
  have hstable : (prefixWord ++ tailWord_325812).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_325812).length < 2 ^ (prefixWord ++ tailWord_325812).sum := by decide
  have hdescent : baseEnd_325812 < baseStart_325812 := by decide
  rcases family_descends (prefixWord ++ tailWord_325812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_325822 : List Nat := [4, 2, 1, 1, 4, 2, 2, 2, 2]
def baseStart_325822 : Nat := 118140960795 + 325822 * 2 ^ 59
def prefixEnd_325822 : Nat := 4983230072969 + 3 ^ 40 * 325822 * 2
def baseEnd_325822 : Nat := 148714038941626181001403

theorem tailTrace_325822 : CollatzResearch.WordTrace tailWord_325822 prefixEnd_325822 148714038941626181001403 := by
  unfold tailWord_325822
  simp only [CollatzResearch.WordTrace]
  refine ⟨1485463078201251851563465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 7922469750406676541671813 1485463078201251851563465)
  ·
    refine ⟨1114097308650938888672599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1485463078201251851563465 1114097308650938888672599)
    ·
      refine ⟨1671145962976408333008899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1114097308650938888672599 1671145962976408333008899)
      ·
        refine ⟨2506718944464612499513349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1671145962976408333008899 2506718944464612499513349)
        ·
          refine ⟨470009802087114843658753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2506718944464612499513349 470009802087114843658753)
          ·
            refine ⟨352507351565336132744065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 470009802087114843658753 352507351565336132744065)
            ·
              refine ⟨264380513674002099558049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 352507351565336132744065 264380513674002099558049)
              ·
                refine ⟨198285385255501574668537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 264380513674002099558049 198285385255501574668537)
                ·
                  refine ⟨148714038941626181001403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 198285385255501574668537 148714038941626181001403)
                  ·
                    rfl

theorem cell20_325822_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 4, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 4, 2, 2, 2, 2].length) (baseStart_325822 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_325822 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_325822 prefixEnd_325822 := by exact prefixLift 325822
  have htrace : WordTrace (prefixWord ++ tailWord_325822) baseStart_325822 baseEnd_325822 := by
    simpa [prefixWord, tailWord_325822, baseEnd_325822] using wordTrace_append hprefix tailTrace_325822
  have hstable : (prefixWord ++ tailWord_325822).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_325822).length < 2 ^ (prefixWord ++ tailWord_325822).sum := by decide
  have hdescent : baseEnd_325822 < baseStart_325822 := by decide
  rcases family_descends (prefixWord ++ tailWord_325822) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_325851 : List Nat := [1, 1, 1, 1, 1, 1, 1, 7, 6]
def baseStart_325851 : Nat := 118140960795 + 325851 * 2 ^ 59
def prefixEnd_325851 : Nat := 4983230072969 + 3 ^ 40 * 325851 * 2
def baseEnd_325851 : Nat := 148727275331830969034617

theorem tailTrace_325851 : CollatzResearch.WordTrace tailWord_325851 prefixEnd_325851 148727275331830969034617 := by
  unfold tailWord_325851
  simp only [CollatzResearch.WordTrace]
  refine ⟨11884762342504952765313407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7923174895003301843542271 11884762342504952765313407)
  ·
    refine ⟨17827143513757429147970111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11884762342504952765313407 17827143513757429147970111)
    ·
      refine ⟨26740715270636143721955167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17827143513757429147970111 26740715270636143721955167)
      ·
        refine ⟨40111072905954215582932751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26740715270636143721955167 40111072905954215582932751)
        ·
          refine ⟨60166609358931323374399127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40111072905954215582932751 60166609358931323374399127)
          ·
            refine ⟨90249914038396985061598691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60166609358931323374399127 90249914038396985061598691)
            ·
              refine ⟨135374871057595477592398037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 90249914038396985061598691 135374871057595477592398037)
              ·
                refine ⟨3172848540412394006071829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 135374871057595477592398037 3172848540412394006071829)
                ·
                  refine ⟨148727275331830969034617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3172848540412394006071829 148727275331830969034617)
                  ·
                    rfl

theorem cell20_325851_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 7, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 7, 6].length) (baseStart_325851 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_325851 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_325851 prefixEnd_325851 := by exact prefixLift 325851
  have htrace : WordTrace (prefixWord ++ tailWord_325851) baseStart_325851 baseEnd_325851 := by
    simpa [prefixWord, tailWord_325851, baseEnd_325851] using wordTrace_append hprefix tailTrace_325851
  have hstable : (prefixWord ++ tailWord_325851).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_325851).length < 2 ^ (prefixWord ++ tailWord_325851).sum := by decide
  have hdescent : baseEnd_325851 < baseStart_325851 := by decide
  rcases family_descends (prefixWord ++ tailWord_325851) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_325864 : List Nat := [2, 1, 4, 1, 2, 3, 2, 3, 2]
def baseStart_325864 : Nat := 118140960795 + 325864 * 2 ^ 59
def prefixEnd_325864 : Nat := 4983230072969 + 3 ^ 40 * 325864 * 2
def baseEnd_325864 : Nat := 148733208886060701601231

theorem tailTrace_325864 : CollatzResearch.WordTrace tailWord_325864 prefixEnd_325864 148733208886060701601231 := by
  unfold tailWord_325864
  simp only [CollatzResearch.WordTrace]
  refine ⟨5942618245728927992768323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7923490994305237323691097 5942618245728927992768323)
  ·
    refine ⟨8913927368593391989152485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5942618245728927992768323 8913927368593391989152485)
    ·
      refine ⟨1671361381611260997966091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8913927368593391989152485 1671361381611260997966091)
      ·
        refine ⟨2507042072416891496949137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1671361381611260997966091 2507042072416891496949137)
        ·
          refine ⟨1880281554312668622711853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2507042072416891496949137 1880281554312668622711853)
          ·
            refine ⟨705105582867250733516945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1880281554312668622711853 705105582867250733516945)
            ·
              refine ⟨528829187150438050137709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 705105582867250733516945 528829187150438050137709)
              ·
                refine ⟨198310945181414268801641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 528829187150438050137709 198310945181414268801641)
                ·
                  refine ⟨148733208886060701601231, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 198310945181414268801641 148733208886060701601231)
                  ·
                    rfl

theorem cell20_325864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 3, 2, 3, 2].length) (baseStart_325864 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_325864 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_325864 prefixEnd_325864 := by exact prefixLift 325864
  have htrace : WordTrace (prefixWord ++ tailWord_325864) baseStart_325864 baseEnd_325864 := by
    simpa [prefixWord, tailWord_325864, baseEnd_325864] using wordTrace_append hprefix tailTrace_325864
  have hstable : (prefixWord ++ tailWord_325864).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_325864).length < 2 ^ (prefixWord ++ tailWord_325864).sum := by decide
  have hdescent : baseEnd_325864 < baseStart_325864 := by decide
  rcases family_descends (prefixWord ++ tailWord_325864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_325878 : List Nat := [5, 1, 1, 1, 1, 1, 5, 2, 3]
def baseStart_325878 : Nat := 118140960795 + 325878 * 2 ^ 59
def prefixEnd_325878 : Nat := 4983230072969 + 3 ^ 40 * 325878 * 2
def baseEnd_325878 : Nat := 148739598867538875134507

theorem tailTrace_325878 : CollatzResearch.WordTrace tailWord_325878 prefixEnd_325878 148739598867538875134507 := by
  unfold tailWord_325878
  simp only [CollatzResearch.WordTrace]
  refine ⟨742859194587946023534143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 7923831408938090917697525 742859194587946023534143)
  ·
    refine ⟨1114288791881919035301215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 742859194587946023534143 1114288791881919035301215)
    ·
      refine ⟨1671433187822878552951823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1114288791881919035301215 1671433187822878552951823)
      ·
        refine ⟨2507149781734317829427735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1671433187822878552951823 2507149781734317829427735)
        ·
          refine ⟨3760724672601476744141603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2507149781734317829427735 3760724672601476744141603)
          ·
            refine ⟨5641087008902215116212405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3760724672601476744141603 5641087008902215116212405)
            ·
              refine ⟨528851907084582667144913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 5641087008902215116212405 528851907084582667144913)
              ·
                refine ⟨396638930313437000358685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 528851907084582667144913 396638930313437000358685)
                ·
                  refine ⟨148739598867538875134507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 396638930313437000358685 148739598867538875134507)
                  ·
                    rfl

theorem cell20_325878_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 5, 2, 3].length) (baseStart_325878 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_325878 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_325878 prefixEnd_325878 := by exact prefixLift 325878
  have htrace : WordTrace (prefixWord ++ tailWord_325878) baseStart_325878 baseEnd_325878 := by
    simpa [prefixWord, tailWord_325878, baseEnd_325878] using wordTrace_append hprefix tailTrace_325878
  have hstable : (prefixWord ++ tailWord_325878).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_325878).length < 2 ^ (prefixWord ++ tailWord_325878).sum := by decide
  have hdescent : baseEnd_325878 < baseStart_325878 := by decide
  rcases family_descends (prefixWord ++ tailWord_325878) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_325940 : List Nat := [2, 5, 1, 1, 1, 4, 1, 1, 4]
def baseStart_325940 : Nat := 118140960795 + 325940 * 2 ^ 59
def prefixEnd_325940 : Nat := 4983230072969 + 3 ^ 40 * 325940 * 2
def baseEnd_325940 : Nat := 148767897356942215067587

theorem tailTrace_325940 : CollatzResearch.WordTrace tailWord_325940 prefixEnd_325940 148767897356942215067587 := by
  unfold tailWord_325940
  simp only [CollatzResearch.WordTrace]
  refine ⟨5944004219591260482651637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7925338959455013976868849 5944004219591260482651637)
  ·
    refine ⟨557250395586680670248591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 5944004219591260482651637 557250395586680670248591)
    ·
      refine ⟨835875593380021005372887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 557250395586680670248591 835875593380021005372887)
      ·
        refine ⟨1253813390070031508059331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 835875593380021005372887 1253813390070031508059331)
        ·
          refine ⟨1880720085105047262088997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1253813390070031508059331 1880720085105047262088997)
          ·
            refine ⟨352635015957196361641687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1880720085105047262088997 352635015957196361641687)
            ·
              refine ⟨528952523935794542462531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 352635015957196361641687 528952523935794542462531)
              ·
                refine ⟨793428785903691813693797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 528952523935794542462531 793428785903691813693797)
                ·
                  refine ⟨148767897356942215067587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 793428785903691813693797 148767897356942215067587)
                  ·
                    rfl

theorem cell20_325940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 4, 1, 1, 4].length) (baseStart_325940 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_325940 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_325940 prefixEnd_325940 := by exact prefixLift 325940
  have htrace : WordTrace (prefixWord ++ tailWord_325940) baseStart_325940 baseEnd_325940 := by
    simpa [prefixWord, tailWord_325940, baseEnd_325940] using wordTrace_append hprefix tailTrace_325940
  have hstable : (prefixWord ++ tailWord_325940).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_325940).length < 2 ^ (prefixWord ++ tailWord_325940).sum := by decide
  have hdescent : baseEnd_325940 < baseStart_325940 := by decide
  rcases family_descends (prefixWord ++ tailWord_325940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_325944 : List Nat := [2, 1, 2, 1, 3, 1, 5, 1, 4]
def baseStart_325944 : Nat := 118140960795 + 325944 * 2 ^ 59
def prefixEnd_325944 : Nat := 4983230072969 + 3 ^ 40 * 325944 * 2
def baseEnd_325944 : Nat := 148769723065935978934237

theorem tailTrace_325944 : CollatzResearch.WordTrace tailWord_325944 prefixEnd_325944 148769723065935978934237 := by
  unfold tailWord_325944
  simp only [CollatzResearch.WordTrace]
  refine ⟨5944077165584014824224443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7925436220778686432299257 5944077165584014824224443)
  ·
    refine ⟨8916115748376022236336665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5944077165584014824224443 8916115748376022236336665)
    ·
      refine ⟨6687086811282016677252499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8916115748376022236336665 6687086811282016677252499)
      ·
        refine ⟨10030630216923025015878749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6687086811282016677252499 10030630216923025015878749)
        ·
          refine ⟨3761486331346134380954531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10030630216923025015878749 3761486331346134380954531)
          ·
            refine ⟨5642229497019201571431797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3761486331346134380954531 5642229497019201571431797)
            ·
              refine ⟨528959015345550147321731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 5642229497019201571431797 528959015345550147321731)
              ·
                refine ⟨793438523018325220982597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 528959015345550147321731 793438523018325220982597)
                ·
                  refine ⟨148769723065935978934237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 793438523018325220982597 148769723065935978934237)
                  ·
                    rfl

theorem cell20_325944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 5, 1, 4].length) (baseStart_325944 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_325944 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_325944 prefixEnd_325944 := by exact prefixLift 325944
  have htrace : WordTrace (prefixWord ++ tailWord_325944) baseStart_325944 baseEnd_325944 := by
    simpa [prefixWord, tailWord_325944, baseEnd_325944] using wordTrace_append hprefix tailTrace_325944
  have hstable : (prefixWord ++ tailWord_325944).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_325944).length < 2 ^ (prefixWord ++ tailWord_325944).sum := by decide
  have hdescent : baseEnd_325944 < baseStart_325944 := by decide
  rcases family_descends (prefixWord ++ tailWord_325944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_325951 : List Nat := [1, 1, 2, 2, 4, 1, 4, 5]
def baseStart_325951 : Nat := 118140960795 + 325951 * 2 ^ 59
def prefixEnd_325951 : Nat := 4983230072969 + 3 ^ 40 * 325951 * 2
def baseEnd_325951 : Nat := 49590972685558355233625

theorem tailTrace_325951 : CollatzResearch.WordTrace tailWord_325951 prefixEnd_325951 49590972685558355233625 := by
  unfold tailWord_325951
  simp only [CollatzResearch.WordTrace]
  refine ⟨11888409642142669843953707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7925606428095113229302471 11888409642142669843953707)
  ·
    refine ⟨17832614463214004765930561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11888409642142669843953707 17832614463214004765930561)
    ·
      refine ⟨13374460847410503574447921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17832614463214004765930561 13374460847410503574447921)
      ·
        refine ⟨10030845635557877680835941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13374460847410503574447921 10030845635557877680835941)
        ·
          refine ⟨1880783556667102065156739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10030845635557877680835941 1880783556667102065156739)
          ·
            refine ⟨2821175335000653097735109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1880783556667102065156739 2821175335000653097735109)
            ·
              refine ⟨528970375312622455825333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2821175335000653097735109 528970375312622455825333)
              ·
                refine ⟨49590972685558355233625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 528970375312622455825333 49590972685558355233625)
                ·
                  rfl

theorem cell20_325951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 4, 5].length) (baseStart_325951 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_325951 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_325951 prefixEnd_325951 := by exact prefixLift 325951
  have htrace : WordTrace (prefixWord ++ tailWord_325951) baseStart_325951 baseEnd_325951 := by
    simpa [prefixWord, tailWord_325951, baseEnd_325951] using wordTrace_append hprefix tailTrace_325951
  have hstable : (prefixWord ++ tailWord_325951).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_325951).length < 2 ^ (prefixWord ++ tailWord_325951).sum := by decide
  have hdescent : baseEnd_325951 < baseStart_325951 := by decide
  rcases family_descends (prefixWord ++ tailWord_325951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_325992 : List Nat := [2, 1, 4, 2, 2, 2, 2, 2, 3]
def baseStart_325992 : Nat := 118140960795 + 325992 * 2 ^ 59
def prefixEnd_325992 : Nat := 4983230072969 + 3 ^ 40 * 325992 * 2
def baseEnd_325992 : Nat := 148791631573861145334041

theorem tailTrace_325992 : CollatzResearch.WordTrace tailWord_325992 prefixEnd_325992 148791631573861145334041 := by
  unfold tailWord_325992
  simp only [CollatzResearch.WordTrace]
  refine ⟨5944952517497066923098115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7926603356662755897464153 5944952517497066923098115)
  ·
    refine ⟨8917428776245600384647173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5944952517497066923098115 8917428776245600384647173)
    ·
      refine ⟨1672017895546050072121345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8917428776245600384647173 1672017895546050072121345)
      ·
        refine ⟨1254013421659537554091009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1672017895546050072121345 1254013421659537554091009)
        ·
          refine ⟨940510066244653165568257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1254013421659537554091009 940510066244653165568257)
          ·
            refine ⟨705382549683489874176193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 940510066244653165568257 705382549683489874176193)
            ·
              refine ⟨529036912262617405632145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 705382549683489874176193 529036912262617405632145)
              ·
                refine ⟨396777684196963054224109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 529036912262617405632145 396777684196963054224109)
                ·
                  refine ⟨148791631573861145334041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 396777684196963054224109 148791631573861145334041)
                  ·
                    rfl

theorem cell20_325992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 2, 2, 2, 3].length) (baseStart_325992 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_325992 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_325992 prefixEnd_325992 := by exact prefixLift 325992
  have htrace : WordTrace (prefixWord ++ tailWord_325992) baseStart_325992 baseEnd_325992 := by
    simpa [prefixWord, tailWord_325992, baseEnd_325992] using wordTrace_append hprefix tailTrace_325992
  have hstable : (prefixWord ++ tailWord_325992).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_325992).length < 2 ^ (prefixWord ++ tailWord_325992).sum := by decide
  have hdescent : baseEnd_325992 < baseStart_325992 := by decide
  rcases family_descends (prefixWord ++ tailWord_325992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_326013 : List Nat := [1, 4, 1, 1, 2, 3, 2, 3, 3]
def baseStart_326013 : Nat := 118140960795 + 326013 * 2 ^ 59
def prefixEnd_326013 : Nat := 4983230072969 + 3 ^ 40 * 326013 * 2
def baseEnd_326013 : Nat := 148801216546078405633955

theorem tailTrace_326013 : CollatzResearch.WordTrace tailWord_326013 prefixEnd_326013 148801216546078405633955 := by
  unfold tailWord_326013
  simp only [CollatzResearch.WordTrace]
  refine ⟨11890670967918054432710693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7927113978612036288473795 11890670967918054432710693)
  ·
    refine ⟨2229500806484635206133255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 11890670967918054432710693 2229500806484635206133255)
    ·
      refine ⟨3344251209726952809199883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2229500806484635206133255 3344251209726952809199883)
      ·
        refine ⟨5016376814590429213799825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3344251209726952809199883 5016376814590429213799825)
        ·
          refine ⟨3762282610942821910349869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5016376814590429213799825 3762282610942821910349869)
          ·
            refine ⟨1410855979103558216381201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3762282610942821910349869 1410855979103558216381201)
            ·
              refine ⟨1058141984327668662285901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1410855979103558216381201 1058141984327668662285901)
              ·
                refine ⟨396803244122875748357213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1058141984327668662285901 396803244122875748357213)
                ·
                  refine ⟨148801216546078405633955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 396803244122875748357213 148801216546078405633955)
                  ·
                    rfl

theorem cell20_326013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 2, 3, 3].length) (baseStart_326013 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_326013 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_326013 prefixEnd_326013 := by exact prefixLift 326013
  have htrace : WordTrace (prefixWord ++ tailWord_326013) baseStart_326013 baseEnd_326013 := by
    simpa [prefixWord, tailWord_326013, baseEnd_326013] using wordTrace_append hprefix tailTrace_326013
  have hstable : (prefixWord ++ tailWord_326013).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_326013).length < 2 ^ (prefixWord ++ tailWord_326013).sum := by decide
  have hdescent : baseEnd_326013 < baseStart_326013 := by decide
  rcases family_descends (prefixWord ++ tailWord_326013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_326020 : List Nat := [2, 3, 2, 1, 1, 2, 3, 2, 4]
def baseStart_326020 : Nat := 118140960795 + 326020 * 2 ^ 59
def prefixEnd_326020 : Nat := 4983230072969 + 3 ^ 40 * 326020 * 2
def baseEnd_326020 : Nat := 148804411536817492400593

theorem tailTrace_326020 : CollatzResearch.WordTrace tailWord_326020 prefixEnd_326020 148804411536817492400593 := by
  unfold tailWord_326020
  simp only [CollatzResearch.WordTrace]
  refine ⟨5945463139446347314107757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7927284185928463085477009 5945463139446347314107757)
  ·
    refine ⟨2229548677292380242790409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5945463139446347314107757 2229548677292380242790409)
    ·
      refine ⟨1672161507969285182092807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2229548677292380242790409 1672161507969285182092807)
      ·
        refine ⟨2508242261953927773139211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1672161507969285182092807 2508242261953927773139211)
        ·
          refine ⟨3762363392930891659708817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2508242261953927773139211 3762363392930891659708817)
          ·
            refine ⟨2821772544698168744781613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3762363392930891659708817 2821772544698168744781613)
            ·
              refine ⟨1058164704261813279293105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2821772544698168744781613 1058164704261813279293105)
              ·
                refine ⟨793623528196359959469829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1058164704261813279293105 793623528196359959469829)
                ·
                  refine ⟨148804411536817492400593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 793623528196359959469829 148804411536817492400593)
                  ·
                    rfl

theorem cell20_326020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 3, 2, 4].length) (baseStart_326020 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_326020 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_326020 prefixEnd_326020 := by exact prefixLift 326020
  have htrace : WordTrace (prefixWord ++ tailWord_326020) baseStart_326020 baseEnd_326020 := by
    simpa [prefixWord, tailWord_326020, baseEnd_326020] using wordTrace_append hprefix tailTrace_326020
  have hstable : (prefixWord ++ tailWord_326020).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_326020).length < 2 ^ (prefixWord ++ tailWord_326020).sum := by decide
  have hdescent : baseEnd_326020 < baseStart_326020 := by decide
  rcases family_descends (prefixWord ++ tailWord_326020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_326041 : List Nat := [1, 2, 1, 2, 1, 4, 1, 2, 6]
def baseStart_326041 : Nat := 118140960795 + 326041 * 2 ^ 59
def prefixEnd_326041 : Nat := 4983230072969 + 3 ^ 40 * 326041 * 2
def baseEnd_326041 : Nat := 148813996509034752700507

theorem tailTrace_326041 : CollatzResearch.WordTrace tailWord_326041 prefixEnd_326041 148813996509034752700507 := by
  unfold tailWord_326041
  simp only [CollatzResearch.WordTrace]
  refine ⟨11891692211816615214729977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7927794807877743476486651 11891692211816615214729977)
  ·
    refine ⟨8918769158862461411047483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11891692211816615214729977 8918769158862461411047483)
    ·
      refine ⟨13378153738293692116571225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8918769158862461411047483 13378153738293692116571225)
      ·
        refine ⟨10033615303720269087428419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13378153738293692116571225 10033615303720269087428419)
        ·
          refine ⟨15050422955580403631142629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10033615303720269087428419 15050422955580403631142629)
          ·
            refine ⟨2821954304171325680839243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 15050422955580403631142629 2821954304171325680839243)
            ·
              refine ⟨4232931456256988521258865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2821954304171325680839243 4232931456256988521258865)
              ·
                refine ⟨3174698592192741390944149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4232931456256988521258865 3174698592192741390944149)
                ·
                  refine ⟨148813996509034752700507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3174698592192741390944149 148813996509034752700507)
                  ·
                    rfl

theorem cell20_326041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 1, 2, 6].length) (baseStart_326041 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_326041 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_326041 prefixEnd_326041 := by exact prefixLift 326041
  have htrace : WordTrace (prefixWord ++ tailWord_326041) baseStart_326041 baseEnd_326041 := by
    simpa [prefixWord, tailWord_326041, baseEnd_326041] using wordTrace_append hprefix tailTrace_326041
  have hstable : (prefixWord ++ tailWord_326041).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_326041).length < 2 ^ (prefixWord ++ tailWord_326041).sum := by decide
  have hdescent : baseEnd_326041 < baseStart_326041 := by decide
  rcases family_descends (prefixWord ++ tailWord_326041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_326051 : List Nat := [1, 1, 1, 4, 1, 4, 3, 2, 3]
def baseStart_326051 : Nat := 118140960795 + 326051 * 2 ^ 59
def prefixEnd_326051 : Nat := 4983230072969 + 3 ^ 40 * 326051 * 2
def baseEnd_326051 : Nat := 148818560781519162367133

theorem tailTrace_326051 : CollatzResearch.WordTrace tailWord_326051 prefixEnd_326051 148818560781519162367133 := by
  unfold tailWord_326051
  simp only [CollatzResearch.WordTrace]
  refine ⟨11892056941780386922594007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7928037961186924615062671 11892056941780386922594007)
  ·
    refine ⟨17838085412670580383891011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11892056941780386922594007 17838085412670580383891011)
    ·
      refine ⟨26757128119005870575836517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17838085412670580383891011 26757128119005870575836517)
      ·
        refine ⟨5016961522313600732969347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 26757128119005870575836517 5016961522313600732969347)
        ·
          refine ⟨7525442283470401099454021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5016961522313600732969347 7525442283470401099454021)
          ·
            refine ⟨1411020428150700206147629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7525442283470401099454021 1411020428150700206147629)
            ·
              refine ⟨529132660556512577305361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1411020428150700206147629 529132660556512577305361)
              ·
                refine ⟨396849495417384432979021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 529132660556512577305361 396849495417384432979021)
                ·
                  refine ⟨148818560781519162367133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 396849495417384432979021 148818560781519162367133)
                  ·
                    rfl

theorem cell20_326051_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 3, 2, 3].length) (baseStart_326051 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_326051 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_326051 prefixEnd_326051 := by exact prefixLift 326051
  have htrace : WordTrace (prefixWord ++ tailWord_326051) baseStart_326051 baseEnd_326051 := by
    simpa [prefixWord, tailWord_326051, baseEnd_326051] using wordTrace_append hprefix tailTrace_326051
  have hstable : (prefixWord ++ tailWord_326051).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_326051).length < 2 ^ (prefixWord ++ tailWord_326051).sum := by decide
  have hdescent : baseEnd_326051 < baseStart_326051 := by decide
  rcases family_descends (prefixWord ++ tailWord_326051) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_326134 : List Nat := [5, 1, 1, 1, 2, 1, 2, 1, 6]
def baseStart_326134 : Nat := 118140960795 + 326134 * 2 ^ 59
def prefixEnd_326134 : Nat := 4983230072969 + 3 ^ 40 * 326134 * 2
def baseEnd_326134 : Nat := 148856444243139762600127

theorem tailTrace_326134 : CollatzResearch.WordTrace tailWord_326134 prefixEnd_326134 148856444243139762600127 := by
  unfold tailWord_326134
  simp only [CollatzResearch.WordTrace]
  refine ⟨743442762529980756116591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 7930056133653128065243637 743442762529980756116591)
  ·
    refine ⟨1115164143794971134174887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 743442762529980756116591 1115164143794971134174887)
    ·
      refine ⟨1672746215692456701262331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1115164143794971134174887 1672746215692456701262331)
      ·
        refine ⟨2509119323538685051893497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1672746215692456701262331 2509119323538685051893497)
        ·
          refine ⟨1881839492654013788920123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2509119323538685051893497 1881839492654013788920123)
          ·
            refine ⟨2822759238981020683380185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1881839492654013788920123 2822759238981020683380185)
            ·
              refine ⟨2117069429235765512535139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2822759238981020683380185 2117069429235765512535139)
              ·
                refine ⟨3175604143853648268802709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2117069429235765512535139 3175604143853648268802709)
                ·
                  refine ⟨148856444243139762600127, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3175604143853648268802709 148856444243139762600127)
                  ·
                    rfl

theorem cell20_326134_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 2, 1, 6].length) (baseStart_326134 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_326134 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_326134 prefixEnd_326134 := by exact prefixLift 326134
  have htrace : WordTrace (prefixWord ++ tailWord_326134) baseStart_326134 baseEnd_326134 := by
    simpa [prefixWord, tailWord_326134, baseEnd_326134] using wordTrace_append hprefix tailTrace_326134
  have hstable : (prefixWord ++ tailWord_326134).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_326134).length < 2 ^ (prefixWord ++ tailWord_326134).sum := by decide
  have hdescent : baseEnd_326134 < baseStart_326134 := by decide
  rcases family_descends (prefixWord ++ tailWord_326134) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_326162 : List Nat := [3, 2, 15]
def baseStart_326162 : Nat := 118140960795 + 326162 * 2 ^ 59
def prefixEnd_326162 : Nat := 4983230072969 + 3 ^ 40 * 326162 * 2
def baseEnd_326162 : Nat := 204210184096153785551

theorem tailTrace_326162 : CollatzResearch.WordTrace tailWord_326162 prefixEnd_326162 204210184096153785551 := by
  unfold tailWord_326162
  simp only [CollatzResearch.WordTrace]
  refine ⟨2974026361094563219971185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7930736962918835253256493 2974026361094563219971185)
  ·
    refine ⟨2230519770820922414978389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2974026361094563219971185 2230519770820922414978389)
    ·
      refine ⟨204210184096153785551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 15 2230519770820922414978389 204210184096153785551)
      ·
        rfl

theorem cell20_326162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 15].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 15].length) (baseStart_326162 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_326162 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_326162 prefixEnd_326162 := by exact prefixLift 326162
  have htrace : WordTrace (prefixWord ++ tailWord_326162) baseStart_326162 baseEnd_326162 := by
    simpa [prefixWord, tailWord_326162, baseEnd_326162] using wordTrace_append hprefix tailTrace_326162
  have hstable : (prefixWord ++ tailWord_326162).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_326162).length < 2 ^ (prefixWord ++ tailWord_326162).sum := by decide
  have hdescent : baseEnd_326162 < baseStart_326162 := by decide
  rcases family_descends (prefixWord ++ tailWord_326162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_326164 : List Nat := [2, 4, 3, 1, 1, 3, 2, 2, 2]
def baseStart_326164 : Nat := 118140960795 + 326164 * 2 ^ 59
def prefixEnd_326164 : Nat := 4983230072969 + 3 ^ 40 * 326164 * 2
def baseEnd_326164 : Nat := 148870137060592991600005

theorem tailTrace_326164 : CollatzResearch.WordTrace tailWord_326164 prefixEnd_326164 148870137060592991600005 := by
  unfold tailWord_326164
  simp only [CollatzResearch.WordTrace]
  refine ⟨5948089195185503610728773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7930785593580671480971697 5948089195185503610728773)
  ·
    refine ⟨1115266724097281927011645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5948089195185503610728773 1115266724097281927011645)
    ·
      refine ⟨418225021536480722629367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1115266724097281927011645 418225021536480722629367)
      ·
        refine ⟨627337532304721083944051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 418225021536480722629367 627337532304721083944051)
        ·
          refine ⟨941006298457081625916077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 627337532304721083944051 941006298457081625916077)
          ·
            refine ⟨352877361921405609718529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 941006298457081625916077 352877361921405609718529)
            ·
              refine ⟨264658021441054207288897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 352877361921405609718529 264658021441054207288897)
              ·
                refine ⟨198493516080790655466673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 264658021441054207288897 198493516080790655466673)
                ·
                  refine ⟨148870137060592991600005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 198493516080790655466673 148870137060592991600005)
                  ·
                    rfl

theorem cell20_326164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 3, 2, 2, 2].length) (baseStart_326164 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_326164 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_326164 prefixEnd_326164 := by exact prefixLift 326164
  have htrace : WordTrace (prefixWord ++ tailWord_326164) baseStart_326164 baseEnd_326164 := by
    simpa [prefixWord, tailWord_326164, baseEnd_326164] using wordTrace_append hprefix tailTrace_326164
  have hstable : (prefixWord ++ tailWord_326164).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_326164).length < 2 ^ (prefixWord ++ tailWord_326164).sum := by decide
  have hdescent : baseEnd_326164 < baseStart_326164 := by decide
  rcases family_descends (prefixWord ++ tailWord_326164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_326165 : List Nat := [1, 3, 2, 1, 3, 1, 4, 2, 3]
def baseStart_326165 : Nat := 118140960795 + 326165 * 2 ^ 59
def prefixEnd_326165 : Nat := 4983230072969 + 3 ^ 40 * 326165 * 2
def baseEnd_326165 : Nat := 148870593487841432566667

theorem tailTrace_326165 : CollatzResearch.WordTrace tailWord_326165 prefixEnd_326165 148870593487841432566667 := by
  unfold tailWord_326165
  simp only [CollatzResearch.WordTrace]
  refine ⟨11896214863367384392243949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7930809908911589594829299 11896214863367384392243949)
  ·
    refine ⟨4461080573762769147091481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11896214863367384392243949 4461080573762769147091481)
    ·
      refine ⟨3345810430322076860318611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4461080573762769147091481 3345810430322076860318611)
      ·
        refine ⟨5018715645483115290477917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3345810430322076860318611 5018715645483115290477917)
        ·
          refine ⟨1882018367056168233929219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5018715645483115290477917 1882018367056168233929219)
          ·
            refine ⟨2823027550584252350893829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1882018367056168233929219 2823027550584252350893829)
            ·
              refine ⟨529317665734547315792593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2823027550584252350893829 529317665734547315792593)
              ·
                refine ⟨396988249300910486844445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 529317665734547315792593 396988249300910486844445)
                ·
                  refine ⟨148870593487841432566667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 396988249300910486844445 148870593487841432566667)
                  ·
                    rfl

theorem cell20_326165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 4, 2, 3].length) (baseStart_326165 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_326165 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_326165 prefixEnd_326165 := by exact prefixLift 326165
  have htrace : WordTrace (prefixWord ++ tailWord_326165) baseStart_326165 baseEnd_326165 := by
    simpa [prefixWord, tailWord_326165, baseEnd_326165] using wordTrace_append hprefix tailTrace_326165
  have hstable : (prefixWord ++ tailWord_326165).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_326165).length < 2 ^ (prefixWord ++ tailWord_326165).sum := by decide
  have hdescent : baseEnd_326165 < baseStart_326165 := by decide
  rcases family_descends (prefixWord ++ tailWord_326165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_326168 : List Nat := [2, 1, 2, 3, 3, 1, 4, 2, 2]
def baseStart_326168 : Nat := 118140960795 + 326168 * 2 ^ 59
def prefixEnd_326168 : Nat := 4983230072969 + 3 ^ 40 * 326168 * 2
def baseEnd_326168 : Nat := 148871962769586755466655

theorem tailTrace_326168 : CollatzResearch.WordTrace tailWord_326168 prefixEnd_326168 148871962769586755466655 := by
  unfold tailWord_326168
  simp only [CollatzResearch.WordTrace]
  refine ⟨5948162141178257952301579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7930882854904343936402105 5948162141178257952301579)
  ·
    refine ⟨8922243211767386928452369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5948162141178257952301579 8922243211767386928452369)
    ·
      refine ⟨6691682408825540196339277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8922243211767386928452369 6691682408825540196339277)
      ·
        refine ⟨2509380903309577573627229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6691682408825540196339277 2509380903309577573627229)
        ·
          refine ⟨941017838741091590110211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2509380903309577573627229 941017838741091590110211)
          ·
            refine ⟨1411526758111637385165317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 941017838741091590110211 1411526758111637385165317)
            ·
              refine ⟨264661267145932009718497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1411526758111637385165317 264661267145932009718497)
              ·
                refine ⟨198495950359449007288873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 264661267145932009718497 198495950359449007288873)
                ·
                  refine ⟨148871962769586755466655, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 198495950359449007288873 148871962769586755466655)
                  ·
                    rfl

theorem cell20_326168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 4, 2, 2].length) (baseStart_326168 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_326168 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_326168 prefixEnd_326168 := by exact prefixLift 326168
  have htrace : WordTrace (prefixWord ++ tailWord_326168) baseStart_326168 baseEnd_326168 := by
    simpa [prefixWord, tailWord_326168, baseEnd_326168] using wordTrace_append hprefix tailTrace_326168
  have hstable : (prefixWord ++ tailWord_326168).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_326168).length < 2 ^ (prefixWord ++ tailWord_326168).sum := by decide
  have hdescent : baseEnd_326168 < baseStart_326168 := by decide
  rcases family_descends (prefixWord ++ tailWord_326168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_326179 : List Nat := [1, 1, 1, 4, 4, 1, 3, 5]
def baseStart_326179 : Nat := 118140960795 + 326179 * 2 ^ 59
def prefixEnd_326179 : Nat := 4983230072969 + 3 ^ 40 * 326179 * 2
def baseEnd_326179 : Nat := 49625661156439868699981

theorem tailTrace_326179 : CollatzResearch.WordTrace tailWord_326179 prefixEnd_326179 49625661156439868699981 := by
  unfold tailWord_326179
  simp only [CollatzResearch.WordTrace]
  refine ⟨11896725485316664783253591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7931150323544443188835727 11896725485316664783253591)
  ·
    refine ⟨17845088227974997174880387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11896725485316664783253591 17845088227974997174880387)
    ·
      refine ⟨26767632341962495762320581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17845088227974997174880387 26767632341962495762320581)
      ·
        refine ⟨5018931064117967955435109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 26767632341962495762320581 5018931064117967955435109)
        ·
          refine ⟨941049574522118991644083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5018931064117967955435109 941049574522118991644083)
          ·
            refine ⟨1411574361783178487466125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 941049574522118991644083 1411574361783178487466125)
            ·
              refine ⟨529340385668691932799797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1411574361783178487466125 529340385668691932799797)
              ·
                refine ⟨49625661156439868699981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 529340385668691932799797 49625661156439868699981)
                ·
                  rfl

theorem cell20_326179_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 3, 5].length) (baseStart_326179 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_326179 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_326179 prefixEnd_326179 := by exact prefixLift 326179
  have htrace : WordTrace (prefixWord ++ tailWord_326179) baseStart_326179 baseEnd_326179 := by
    simpa [prefixWord, tailWord_326179, baseEnd_326179] using wordTrace_append hprefix tailTrace_326179
  have hstable : (prefixWord ++ tailWord_326179).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_326179).length < 2 ^ (prefixWord ++ tailWord_326179).sum := by decide
  have hdescent : baseEnd_326179 < baseStart_326179 := by decide
  rcases family_descends (prefixWord ++ tailWord_326179) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_326193 : List Nat := [1, 2, 2, 3, 1, 1, 3, 1, 6]
def baseStart_326193 : Nat := 118140960795 + 326193 * 2 ^ 59
def prefixEnd_326193 : Nat := 4983230072969 + 3 ^ 40 * 326193 * 2
def baseEnd_326193 : Nat := 148883373450797779633219

theorem tailTrace_326193 : CollatzResearch.WordTrace tailWord_326193 prefixEnd_326193 148883373450797779633219 := by
  unfold tailWord_326193
  simp only [CollatzResearch.WordTrace]
  refine ⟨11897236107265945174263233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7931490738177296782842155 11897236107265945174263233)
  ·
    refine ⟨8922927080449458880697425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11897236107265945174263233 8922927080449458880697425)
    ·
      refine ⟨6692195310337094160523069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8922927080449458880697425 6692195310337094160523069)
      ·
        refine ⟨2509573241376410310196151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6692195310337094160523069 2509573241376410310196151)
        ·
          refine ⟨3764359862064615465294227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2509573241376410310196151 3764359862064615465294227)
          ·
            refine ⟨5646539793096923197941341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3764359862064615465294227 5646539793096923197941341)
            ·
              refine ⟨2117452422411346199228003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5646539793096923197941341 2117452422411346199228003)
              ·
                refine ⟨3176178633617019298842005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2117452422411346199228003 3176178633617019298842005)
                ·
                  refine ⟨148883373450797779633219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3176178633617019298842005 148883373450797779633219)
                  ·
                    rfl

theorem cell20_326193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 3, 1, 6].length) (baseStart_326193 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_326193 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_326193 prefixEnd_326193 := by exact prefixLift 326193
  have htrace : WordTrace (prefixWord ++ tailWord_326193) baseStart_326193 baseEnd_326193 := by
    simpa [prefixWord, tailWord_326193, baseEnd_326193] using wordTrace_append hprefix tailTrace_326193
  have hstable : (prefixWord ++ tailWord_326193).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_326193).length < 2 ^ (prefixWord ++ tailWord_326193).sum := by decide
  have hdescent : baseEnd_326193 < baseStart_326193 := by decide
  rcases family_descends (prefixWord ++ tailWord_326193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_326224 : List Nat := [2, 1, 1, 1, 1, 3, 2, 6, 3]
def baseStart_326224 : Nat := 118140960795 + 326224 * 2 ^ 59
def prefixEnd_326224 : Nat := 4983230072969 + 3 ^ 40 * 326224 * 2
def baseEnd_326224 : Nat := 148897522695499449599759

theorem tailTrace_326224 : CollatzResearch.WordTrace tailWord_326224 prefixEnd_326224 148897522695499449599759 := by
  unfold tailWord_326224
  simp only [CollatzResearch.WordTrace]
  refine ⟨5949183385076818734320863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7932244513435758312427817 5949183385076818734320863)
  ·
    refine ⟨8923775077615228101481295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5949183385076818734320863 8923775077615228101481295)
    ·
      refine ⟨13385662616422842152221943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8923775077615228101481295 13385662616422842152221943)
      ·
        refine ⟨20078493924634263228332915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13385662616422842152221943 20078493924634263228332915)
        ·
          refine ⟨30117740886951394842499373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20078493924634263228332915 30117740886951394842499373)
          ·
            refine ⟨11294152832606773065937265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30117740886951394842499373 11294152832606773065937265)
            ·
              refine ⟨8470614624455079799452949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11294152832606773065937265 8470614624455079799452949)
              ·
                refine ⟨397060060521331865599357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 8470614624455079799452949 397060060521331865599357)
                ·
                  refine ⟨148897522695499449599759, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 397060060521331865599357 148897522695499449599759)
                  ·
                    rfl

theorem cell20_326224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 2, 6, 3].length) (baseStart_326224 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_326224 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_326224 prefixEnd_326224 := by exact prefixLift 326224
  have htrace : WordTrace (prefixWord ++ tailWord_326224) baseStart_326224 baseEnd_326224 := by
    simpa [prefixWord, tailWord_326224, baseEnd_326224] using wordTrace_append hprefix tailTrace_326224
  have hstable : (prefixWord ++ tailWord_326224).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_326224).length < 2 ^ (prefixWord ++ tailWord_326224).sum := by decide
  have hdescent : baseEnd_326224 < baseStart_326224 := by decide
  rcases family_descends (prefixWord ++ tailWord_326224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_326255 : List Nat := [1, 1, 2, 1, 3, 2, 6, 4]
def baseStart_326255 : Nat := 118140960795 + 326255 * 2 ^ 59
def prefixEnd_326255 : Nat := 4983230072969 + 3 ^ 40 * 326255 * 2
def baseEnd_326255 : Nat := 49637223980067039855433

theorem tailTrace_326255 : CollatzResearch.WordTrace tailWord_326255 prefixEnd_326255 49637223980067039855433 := by
  unfold tailWord_326255
  simp only [CollatzResearch.WordTrace]
  refine ⟨11899497433041329763020219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7932998288694219842013479 11899497433041329763020219)
  ·
    refine ⟨17849246149561994644530329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11899497433041329763020219 17849246149561994644530329)
    ·
      refine ⟨13386934612171495983397747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17849246149561994644530329 13386934612171495983397747)
      ·
        refine ⟨20080401918257243975096621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13386934612171495983397747 20080401918257243975096621)
        ·
          refine ⟨7530150719346466490661233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20080401918257243975096621 7530150719346466490661233)
          ·
            refine ⟨5647613039509849867995925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7530150719346466490661233 5647613039509849867995925)
            ·
              refine ⟨264731861227024212562309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 5647613039509849867995925 264731861227024212562309)
              ·
                refine ⟨49637223980067039855433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 264731861227024212562309 49637223980067039855433)
                ·
                  rfl

theorem cell20_326255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 6, 4].length) (baseStart_326255 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_326255 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_326255 prefixEnd_326255 := by exact prefixLift 326255
  have htrace : WordTrace (prefixWord ++ tailWord_326255) baseStart_326255 baseEnd_326255 := by
    simpa [prefixWord, tailWord_326255, baseEnd_326255] using wordTrace_append hprefix tailTrace_326255
  have hstable : (prefixWord ++ tailWord_326255).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_326255).length < 2 ^ (prefixWord ++ tailWord_326255).sum := by decide
  have hdescent : baseEnd_326255 < baseStart_326255 := by decide
  rcases family_descends (prefixWord ++ tailWord_326255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_326261 : List Nat := [1, 3, 4, 2, 2, 2, 1, 3, 2]
def baseStart_326261 : Nat := 118140960795 + 326261 * 2 ^ 59
def prefixEnd_326261 : Nat := 4983230072969 + 3 ^ 40 * 326261 * 2
def baseEnd_326261 : Nat := 148914410503691765366275

theorem tailTrace_326261 : CollatzResearch.WordTrace tailWord_326261 prefixEnd_326261 148914410503691765366275 := by
  unfold tailWord_326261
  simp only [CollatzResearch.WordTrace]
  refine ⟨11899716271019592787738637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7933144180679728525159091 11899716271019592787738637)
  ·
    refine ⟨4462393601632347295401989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11899716271019592787738637 4462393601632347295401989)
    ·
      refine ⟨836698800306065117887873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4462393601632347295401989 836698800306065117887873)
      ·
        refine ⟨627524100229548838415905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 836698800306065117887873 627524100229548838415905)
        ·
          refine ⟨470643075172161628811929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 627524100229548838415905 470643075172161628811929)
          ·
            refine ⟨352982306379121221608947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 470643075172161628811929 352982306379121221608947)
            ·
              refine ⟨529473459568681832413421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 352982306379121221608947 529473459568681832413421)
              ·
                refine ⟨198552547338255687155033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 529473459568681832413421 198552547338255687155033)
                ·
                  refine ⟨148914410503691765366275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 198552547338255687155033 148914410503691765366275)
                  ·
                    rfl

theorem cell20_326261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 2, 2, 1, 3, 2].length) (baseStart_326261 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_326261 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_326261 prefixEnd_326261 := by exact prefixLift 326261
  have htrace : WordTrace (prefixWord ++ tailWord_326261) baseStart_326261 baseEnd_326261 := by
    simpa [prefixWord, tailWord_326261, baseEnd_326261] using wordTrace_append hprefix tailTrace_326261
  have hstable : (prefixWord ++ tailWord_326261).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_326261).length < 2 ^ (prefixWord ++ tailWord_326261).sum := by decide
  have hdescent : baseEnd_326261 < baseStart_326261 := by decide
  rcases family_descends (prefixWord ++ tailWord_326261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_326265 : List Nat := [1, 2, 1, 3, 3, 2, 3, 3, 2]
def baseStart_326265 : Nat := 118140960795 + 326265 * 2 ^ 59
def prefixEnd_326265 : Nat := 4983230072969 + 3 ^ 40 * 326265 * 2
def baseEnd_326265 : Nat := 148916236212685529232925

theorem tailTrace_326265 : CollatzResearch.WordTrace tailWord_326265 prefixEnd_326265 148916236212685529232925 := by
  unfold tailWord_326265
  simp only [CollatzResearch.WordTrace]
  refine ⟨11899862163005101470884249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7933241442003400980589499 11899862163005101470884249)
  ·
    refine ⟨8924896622253826103163187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11899862163005101470884249 8924896622253826103163187)
    ·
      refine ⟨13387344933380739154744781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8924896622253826103163187 13387344933380739154744781)
      ·
        refine ⟨5020254350017777183029293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13387344933380739154744781 5020254350017777183029293)
        ·
          refine ⟨1882595381256666443635985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5020254350017777183029293 1882595381256666443635985)
          ·
            refine ⟨1411946535942499832726989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1882595381256666443635985 1411946535942499832726989)
            ·
              refine ⟨529479950978437437272621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1411946535942499832726989 529479950978437437272621)
              ·
                refine ⟨198554981616914038977233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 529479950978437437272621 198554981616914038977233)
                ·
                  refine ⟨148916236212685529232925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 198554981616914038977233 148916236212685529232925)
                  ·
                    rfl

theorem cell20_326265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 3, 3, 2].length) (baseStart_326265 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_326265 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_326265 prefixEnd_326265 := by exact prefixLift 326265
  have htrace : WordTrace (prefixWord ++ tailWord_326265) baseStart_326265 baseEnd_326265 := by
    simpa [prefixWord, tailWord_326265, baseEnd_326265] using wordTrace_append hprefix tailTrace_326265
  have hstable : (prefixWord ++ tailWord_326265).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_326265).length < 2 ^ (prefixWord ++ tailWord_326265).sum := by decide
  have hdescent : baseEnd_326265 < baseStart_326265 := by decide
  rcases family_descends (prefixWord ++ tailWord_326265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_326282 : List Nat := [3, 1, 2, 3, 4, 1, 1, 1, 4]
def baseStart_326282 : Nat := 118140960795 + 326282 * 2 ^ 59
def prefixEnd_326282 : Nat := 4983230072969 + 3 ^ 40 * 326282 * 2
def baseEnd_326282 : Nat := 148923995475909025666189

theorem tailTrace_326282 : CollatzResearch.WordTrace tailWord_326282 prefixEnd_326282 148923995475909025666189 := by
  unfold tailWord_326282
  simp only [CollatzResearch.WordTrace]
  refine ⟨2975120550985878343563275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7933654802629008916168733 2975120550985878343563275)
  ·
    refine ⟨4462680826478817515344913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2975120550985878343563275 4462680826478817515344913)
    ·
      refine ⟨3347010619859113136508685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4462680826478817515344913 3347010619859113136508685)
      ·
        refine ⟨1255128982447167426190757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3347010619859113136508685 1255128982447167426190757)
        ·
          refine ⟨235336684208843892410767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1255128982447167426190757 235336684208843892410767)
          ·
            refine ⟨353005026313265838616151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 235336684208843892410767 353005026313265838616151)
            ·
              refine ⟨529507539469898757924227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 353005026313265838616151 529507539469898757924227)
              ·
                refine ⟨794261309204848136886341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 529507539469898757924227 794261309204848136886341)
                ·
                  refine ⟨148923995475909025666189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 794261309204848136886341 148923995475909025666189)
                  ·
                    rfl

theorem cell20_326282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 4, 1, 1, 1, 4].length) (baseStart_326282 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_326282 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_326282 prefixEnd_326282 := by exact prefixLift 326282
  have htrace : WordTrace (prefixWord ++ tailWord_326282) baseStart_326282 baseEnd_326282 := by
    simpa [prefixWord, tailWord_326282, baseEnd_326282] using wordTrace_append hprefix tailTrace_326282
  have hstable : (prefixWord ++ tailWord_326282).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_326282).length < 2 ^ (prefixWord ++ tailWord_326282).sum := by decide
  have hdescent : baseEnd_326282 < baseStart_326282 := by decide
  rcases family_descends (prefixWord ++ tailWord_326282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_326337 : List Nat := [1, 2, 6, 2, 1, 1, 1, 4, 2]
def baseStart_326337 : Nat := 118140960795 + 326337 * 2 ^ 59
def prefixEnd_326337 : Nat := 4983230072969 + 3 ^ 40 * 326337 * 2
def baseEnd_326337 : Nat := 148949098974573278832631

theorem tailTrace_326337 : CollatzResearch.WordTrace tailWord_326337 prefixEnd_326337 148949098974573278832631 := by
  unfold tailWord_326337
  simp only [CollatzResearch.WordTrace]
  refine ⟨11902488218744257767505265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7934992145829505178336843 11902488218744257767505265)
  ·
    refine ⟨8926866164058193325628949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11902488218744257767505265 8926866164058193325628949)
    ·
      refine ⟨418446851440227812138857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 8926866164058193325628949 418446851440227812138857)
      ·
        refine ⟨313835138580170859104143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 418446851440227812138857 313835138580170859104143)
        ·
          refine ⟨470752707870256288656215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 313835138580170859104143 470752707870256288656215)
          ·
            refine ⟨706129061805384432984323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 470752707870256288656215 706129061805384432984323)
            ·
              refine ⟨1059193592708076649476485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 706129061805384432984323 1059193592708076649476485)
              ·
                refine ⟨198598798632764371776841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1059193592708076649476485 198598798632764371776841)
                ·
                  refine ⟨148949098974573278832631, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 198598798632764371776841 148949098974573278832631)
                  ·
                    rfl

theorem cell20_326337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 1, 1, 1, 4, 2].length) (baseStart_326337 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_326337 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_326337 prefixEnd_326337 := by exact prefixLift 326337
  have htrace : WordTrace (prefixWord ++ tailWord_326337) baseStart_326337 baseEnd_326337 := by
    simpa [prefixWord, tailWord_326337, baseEnd_326337] using wordTrace_append hprefix tailTrace_326337
  have hstable : (prefixWord ++ tailWord_326337).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_326337).length < 2 ^ (prefixWord ++ tailWord_326337).sum := by decide
  have hdescent : baseEnd_326337 < baseStart_326337 := by decide
  rcases family_descends (prefixWord ++ tailWord_326337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_326348 : List Nat := [2, 2, 1, 5, 1, 3, 1, 5]
def baseStart_326348 : Nat := 118140960795 + 326348 * 2 ^ 59
def prefixEnd_326348 : Nat := 4983230072969 + 3 ^ 40 * 326348 * 2
def baseEnd_326348 : Nat := 49651373224768709821973

theorem tailTrace_326348 : CollatzResearch.WordTrace tailWord_326348 prefixEnd_326348 49651373224768709821973 := by
  unfold tailWord_326348
  simp only [CollatzResearch.WordTrace]
  refine ⟨5951444710852203323077849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7935259614469604430770465 5951444710852203323077849)
  ·
    refine ⟨4463583533139152492308387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5951444710852203323077849 4463583533139152492308387)
    ·
      refine ⟨6695375299708728738462581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4463583533139152492308387 6695375299708728738462581)
      ·
        refine ⟨627691434347693319230867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 6695375299708728738462581 627691434347693319230867)
        ·
          refine ⟨941537151521539978846301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 627691434347693319230867 941537151521539978846301)
          ·
            refine ⟨353076431820577492067363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 941537151521539978846301 353076431820577492067363)
            ·
              refine ⟨529614647730866238101045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 353076431820577492067363 529614647730866238101045)
              ·
                refine ⟨49651373224768709821973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 529614647730866238101045 49651373224768709821973)
                ·
                  rfl

theorem cell20_326348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 3, 1, 5].length) (baseStart_326348 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_326348 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_326348 prefixEnd_326348 := by exact prefixLift 326348
  have htrace : WordTrace (prefixWord ++ tailWord_326348) baseStart_326348 baseEnd_326348 := by
    simpa [prefixWord, tailWord_326348, baseEnd_326348] using wordTrace_append hprefix tailTrace_326348
  have hstable : (prefixWord ++ tailWord_326348).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_326348).length < 2 ^ (prefixWord ++ tailWord_326348).sum := by decide
  have hdescent : baseEnd_326348 < baseStart_326348 := by decide
  rcases family_descends (prefixWord ++ tailWord_326348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_326389 : List Nat := [1, 3, 6, 1, 1, 1, 1, 1, 5]
def baseStart_326389 : Nat := 118140960795 + 326389 * 2 ^ 59
def prefixEnd_326389 : Nat := 4983230072969 + 3 ^ 40 * 326389 * 2
def baseEnd_326389 : Nat := 148972833191492209099085

theorem tailTrace_326389 : CollatzResearch.WordTrace tailWord_326389 prefixEnd_326389 148972833191492209099085 := by
  unfold tailWord_326389
  simp only [CollatzResearch.WordTrace]
  refine ⟨11904384814555870648398221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7936256543037247098932147 11904384814555870648398221)
  ·
    refine ⟨4464144305458451493149333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11904384814555870648398221 4464144305458451493149333)
    ·
      refine ⟨209256764318364913741375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 4464144305458451493149333 209256764318364913741375)
      ·
        refine ⟨313885146477547370612063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 209256764318364913741375 313885146477547370612063)
        ·
          refine ⟨470827719716321055918095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 313885146477547370612063 470827719716321055918095)
          ·
            refine ⟨706241579574481583877143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 470827719716321055918095 706241579574481583877143)
            ·
              refine ⟨1059362369361722375815715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 706241579574481583877143 1059362369361722375815715)
              ·
                refine ⟨1589043554042583563723573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1059362369361722375815715 1589043554042583563723573)
                ·
                  refine ⟨148972833191492209099085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1589043554042583563723573 148972833191492209099085)
                  ·
                    rfl

theorem cell20_326389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 1, 1, 1, 1, 5].length) (baseStart_326389 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_326389 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_326389 prefixEnd_326389 := by exact prefixLift 326389
  have htrace : WordTrace (prefixWord ++ tailWord_326389) baseStart_326389 baseEnd_326389 := by
    simpa [prefixWord, tailWord_326389, baseEnd_326389] using wordTrace_append hprefix tailTrace_326389
  have hstable : (prefixWord ++ tailWord_326389).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_326389).length < 2 ^ (prefixWord ++ tailWord_326389).sum := by decide
  have hdescent : baseEnd_326389 < baseStart_326389 := by decide
  rcases family_descends (prefixWord ++ tailWord_326389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_326421 : List Nat := [1, 3, 2, 1, 2, 2, 1, 4, 4]
def baseStart_326421 : Nat := 118140960795 + 326421 * 2 ^ 59
def prefixEnd_326421 : Nat := 4983230072969 + 3 ^ 40 * 326421 * 2
def baseEnd_326421 : Nat := 148987438863442320032287

theorem tailTrace_326421 : CollatzResearch.WordTrace tailWord_326421 prefixEnd_326421 148987438863442320032287 := by
  unfold tailWord_326421
  simp only [CollatzResearch.WordTrace]
  refine ⟨11905551950439940113563117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7937034633626626742375411 11905551950439940113563117)
  ·
    refine ⟨4464581981414977542586169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11905551950439940113563117 4464581981414977542586169)
    ·
      refine ⟨3348436486061233156939627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4464581981414977542586169 3348436486061233156939627)
      ·
        refine ⟨5022654729091849735409441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3348436486061233156939627 5022654729091849735409441)
        ·
          refine ⟨3766991046818887301557081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5022654729091849735409441 3766991046818887301557081)
          ·
            refine ⟨2825243285114165476167811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3766991046818887301557081 2825243285114165476167811)
            ·
              refine ⟨4237864927671248214251717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2825243285114165476167811 4237864927671248214251717)
              ·
                refine ⟨794599673938359040172197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4237864927671248214251717 794599673938359040172197)
                ·
                  refine ⟨148987438863442320032287, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 794599673938359040172197 148987438863442320032287)
                  ·
                    rfl

theorem cell20_326421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 1, 4, 4].length) (baseStart_326421 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_326421 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_326421 prefixEnd_326421 := by exact prefixLift 326421
  have htrace : WordTrace (prefixWord ++ tailWord_326421) baseStart_326421 baseEnd_326421 := by
    simpa [prefixWord, tailWord_326421, baseEnd_326421] using wordTrace_append hprefix tailTrace_326421
  have hstable : (prefixWord ++ tailWord_326421).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_326421).length < 2 ^ (prefixWord ++ tailWord_326421).sum := by decide
  have hdescent : baseEnd_326421 < baseStart_326421 := by decide
  rcases family_descends (prefixWord ++ tailWord_326421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_326434 : List Nat := [3, 3, 1, 1, 2, 4, 1, 3, 2]
def baseStart_326434 : Nat := 118140960795 + 326434 * 2 ^ 59
def prefixEnd_326434 : Nat := 4983230072969 + 3 ^ 40 * 326434 * 2
def baseEnd_326434 : Nat := 148993372417672052598901

theorem tailTrace_326434 : CollatzResearch.WordTrace tailWord_326434 prefixEnd_326434 148993372417672052598901 := by
  unfold tailWord_326434
  simp only [CollatzResearch.WordTrace]
  refine ⟨2976506524848210833446589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7937350732928562222524237 2976506524848210833446589)
  ·
    refine ⟨1116189946818079062542471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2976506524848210833446589 1116189946818079062542471)
    ·
      refine ⟨1674284920227118593813707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1116189946818079062542471 1674284920227118593813707)
      ·
        refine ⟨2511427380340677890720561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1674284920227118593813707 2511427380340677890720561)
        ·
          refine ⟨1883570535255508418040421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2511427380340677890720561 1883570535255508418040421)
          ·
            refine ⟨353169475360407828382579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1883570535255508418040421 353169475360407828382579)
            ·
              refine ⟨529754213040611742573869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 353169475360407828382579 529754213040611742573869)
              ·
                refine ⟨198657829890229403465201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 529754213040611742573869 198657829890229403465201)
                ·
                  refine ⟨148993372417672052598901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 198657829890229403465201 148993372417672052598901)
                  ·
                    rfl

theorem cell20_326434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 4, 1, 3, 2].length) (baseStart_326434 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_326434 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_326434 prefixEnd_326434 := by exact prefixLift 326434
  have htrace : WordTrace (prefixWord ++ tailWord_326434) baseStart_326434 baseEnd_326434 := by
    simpa [prefixWord, tailWord_326434, baseEnd_326434] using wordTrace_append hprefix tailTrace_326434
  have hstable : (prefixWord ++ tailWord_326434).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_326434).length < 2 ^ (prefixWord ++ tailWord_326434).sum := by decide
  have hdescent : baseEnd_326434 < baseStart_326434 := by decide
  rcases family_descends (prefixWord ++ tailWord_326434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_326455 : List Nat := [1, 1, 3, 1, 2, 1, 7, 2, 2]
def baseStart_326455 : Nat := 118140960795 + 326455 * 2 ^ 59
def prefixEnd_326455 : Nat := 4983230072969 + 3 ^ 40 * 326455 * 2
def baseEnd_326455 : Nat := 149002957389889312898815

theorem tailTrace_326455 : CollatzResearch.WordTrace tailWord_326455 prefixEnd_326455 149002957389889312898815 := by
  unfold tailWord_326455
  simp only [CollatzResearch.WordTrace]
  refine ⟨11906792032316763920300819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7937861354877842613533879 11906792032316763920300819)
  ·
    refine ⟨17860188048475145880451229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11906792032316763920300819 17860188048475145880451229)
    ·
      refine ⟨6697570518178179705169211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17860188048475145880451229 6697570518178179705169211)
      ·
        refine ⟨10046355777267269557753817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6697570518178179705169211 10046355777267269557753817)
        ·
          refine ⟨7534766832950452168315363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10046355777267269557753817 7534766832950452168315363)
          ·
            refine ⟨11302150249425678252473045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7534766832950452168315363 11302150249425678252473045)
            ·
              refine ⟨264894146470914334042337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 11302150249425678252473045 264894146470914334042337)
              ·
                refine ⟨198670609853185750531753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 264894146470914334042337 198670609853185750531753)
                ·
                  refine ⟨149002957389889312898815, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 198670609853185750531753 149002957389889312898815)
                  ·
                    rfl

theorem cell20_326455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 7, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 7, 2, 2].length) (baseStart_326455 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_326455 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_326455 prefixEnd_326455 := by exact prefixLift 326455
  have htrace : WordTrace (prefixWord ++ tailWord_326455) baseStart_326455 baseEnd_326455 := by
    simpa [prefixWord, tailWord_326455, baseEnd_326455] using wordTrace_append hprefix tailTrace_326455
  have hstable : (prefixWord ++ tailWord_326455).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_326455).length < 2 ^ (prefixWord ++ tailWord_326455).sum := by decide
  have hdescent : baseEnd_326455 < baseStart_326455 := by decide
  rcases family_descends (prefixWord ++ tailWord_326455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_326462 : List Nat := [4, 2, 1, 2, 3, 1, 2, 5]
def baseStart_326462 : Nat := 118140960795 + 326462 * 2 ^ 59
def prefixEnd_326462 : Nat := 4983230072969 + 3 ^ 40 * 326462 * 2
def baseEnd_326462 : Nat := 49668717460209466555151

theorem tailTrace_326462 : CollatzResearch.WordTrace tailWord_326462 prefixEnd_326462 49668717460209466555151 := by
  unfold tailWord_326462
  simp only [CollatzResearch.WordTrace]
  refine ⟨1488380917911425514475705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 7938031562194269410537093 1488380917911425514475705)
  ·
    refine ⟨1116285688433569135856779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1488380917911425514475705 1116285688433569135856779)
    ·
      refine ⟨1674428532650353703785169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1116285688433569135856779 1674428532650353703785169)
      ·
        refine ⟨1255821399487765277838877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1674428532650353703785169 1255821399487765277838877)
        ·
          refine ⟨470933024807911979189579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1255821399487765277838877 470933024807911979189579)
          ·
            refine ⟨706399537211867968784369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 470933024807911979189579 706399537211867968784369)
            ·
              refine ⟨529799652908900976588277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 706399537211867968784369 529799652908900976588277)
              ·
                refine ⟨49668717460209466555151, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 529799652908900976588277 49668717460209466555151)
                ·
                  rfl

theorem cell20_326462_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 3, 1, 2, 5].length) (baseStart_326462 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_326462 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_326462 prefixEnd_326462 := by exact prefixLift 326462
  have htrace : WordTrace (prefixWord ++ tailWord_326462) baseStart_326462 baseEnd_326462 := by
    simpa [prefixWord, tailWord_326462, baseEnd_326462] using wordTrace_append hprefix tailTrace_326462
  have hstable : (prefixWord ++ tailWord_326462).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_326462).length < 2 ^ (prefixWord ++ tailWord_326462).sum := by decide
  have hdescent : baseEnd_326462 < baseStart_326462 := by decide
  rcases family_descends (prefixWord ++ tailWord_326462) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_326504 : List Nat := [2, 1, 4, 2, 1, 10]
def baseStart_326504 : Nat := 118140960795 + 326504 * 2 ^ 59
def prefixEnd_326504 : Nat := 4983230072969 + 3 ^ 40 * 326504 * 2
def baseEnd_326504 : Nat := 5519456382409737787603

theorem tailTrace_326504 : CollatzResearch.WordTrace tailWord_326504 prefixEnd_326504 5519456382409737787603 := by
  unfold tailWord_326504
  simp only [CollatzResearch.WordTrace]
  refine ⟨5954289604569622644417283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7939052806092830192556377 5954289604569622644417283)
  ·
    refine ⟨8931434406854433966625925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5954289604569622644417283 8931434406854433966625925)
    ·
      refine ⟨1674643951285206368742361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8931434406854433966625925 1674643951285206368742361)
      ·
        refine ⟨1255982963463904776556771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1674643951285206368742361 1255982963463904776556771)
        ·
          refine ⟨1883974445195857164835157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1255982963463904776556771 1883974445195857164835157)
          ·
            refine ⟨5519456382409737787603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 1883974445195857164835157 5519456382409737787603)
            ·
              rfl

theorem cell20_326504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 10].length) (baseStart_326504 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_326504 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_326504 prefixEnd_326504 := by exact prefixLift 326504
  have htrace : WordTrace (prefixWord ++ tailWord_326504) baseStart_326504 baseEnd_326504 := by
    simpa [prefixWord, tailWord_326504, baseEnd_326504] using wordTrace_append hprefix tailTrace_326504
  have hstable : (prefixWord ++ tailWord_326504).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_326504).length < 2 ^ (prefixWord ++ tailWord_326504).sum := by decide
  have hdescent : baseEnd_326504 < baseStart_326504 := by decide
  rcases family_descends (prefixWord ++ tailWord_326504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_326510 : List Nat := [4, 1, 2, 3, 2, 1, 1, 4, 2]
def baseStart_326510 : Nat := 118140960795 + 326510 * 2 ^ 59
def prefixEnd_326510 : Nat := 4983230072969 + 3 ^ 40 * 326510 * 2
def baseEnd_326510 : Nat := 149028060888553566065257

theorem tailTrace_326510 : CollatzResearch.WordTrace tailWord_326510 prefixEnd_326510 149028060888553566065257 := by
  unfold tailWord_326510
  simp only [CollatzResearch.WordTrace]
  refine ⟨1488599755889688539194123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 7939198698078338875701989 1488599755889688539194123)
  ·
    refine ⟨2232899633834532808791185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1488599755889688539194123 2232899633834532808791185)
    ·
      refine ⟨1674674725375899606593389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2232899633834532808791185 1674674725375899606593389)
      ·
        refine ⟨628003022015962352472521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1674674725375899606593389 628003022015962352472521)
        ·
          refine ⟨471002266511971764354391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 628003022015962352472521 471002266511971764354391)
          ·
            refine ⟨706503399767957646531587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 471002266511971764354391 706503399767957646531587)
            ·
              refine ⟨1059755099651936469797381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 706503399767957646531587 1059755099651936469797381)
              ·
                refine ⟨198704081184738088087009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1059755099651936469797381 198704081184738088087009)
                ·
                  refine ⟨149028060888553566065257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 198704081184738088087009 149028060888553566065257)
                  ·
                    rfl

theorem cell20_326510_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 2, 1, 1, 4, 2].length) (baseStart_326510 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_326510 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_326510 prefixEnd_326510 := by exact prefixLift 326510
  have htrace : WordTrace (prefixWord ++ tailWord_326510) baseStart_326510 baseEnd_326510 := by
    simpa [prefixWord, tailWord_326510, baseEnd_326510] using wordTrace_append hprefix tailTrace_326510
  have hstable : (prefixWord ++ tailWord_326510).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_326510).length < 2 ^ (prefixWord ++ tailWord_326510).sum := by decide
  have hdescent : baseEnd_326510 < baseStart_326510 := by decide
  rcases family_descends (prefixWord ++ tailWord_326510) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_326511 : List Nat := [1, 1, 2, 1, 3, 1, 1, 5, 5]
def baseStart_326511 : Nat := 118140960795 + 326511 * 2 ^ 59
def prefixEnd_326511 : Nat := 4983230072969 + 3 ^ 40 * 326511 * 2
def baseEnd_326511 : Nat := 149028517315802007031919

theorem tailTrace_326511 : CollatzResearch.WordTrace tailWord_326511 prefixEnd_326511 149028517315802007031919 := by
  unfold tailWord_326511
  simp only [CollatzResearch.WordTrace]
  refine ⟨11908834520113885484339387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7939223013409256989559591 11908834520113885484339387)
  ·
    refine ⟨17863251780170828226509081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11908834520113885484339387 17863251780170828226509081)
    ·
      refine ⟨13397438835128121169881811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17863251780170828226509081 13397438835128121169881811)
      ·
        refine ⟨20096158252692181754822717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13397438835128121169881811 20096158252692181754822717)
        ·
          refine ⟨7536059344759568158058519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20096158252692181754822717 7536059344759568158058519)
          ·
            refine ⟨11304089017139352237087779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7536059344759568158058519 11304089017139352237087779)
            ·
              refine ⟨16956133525709028355631669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11304089017139352237087779 16956133525709028355631669)
              ·
                refine ⟨1589637518035221408340469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 16956133525709028355631669 1589637518035221408340469)
                ·
                  refine ⟨149028517315802007031919, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1589637518035221408340469 149028517315802007031919)
                  ·
                    rfl

theorem cell20_326511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 5, 5].length) (baseStart_326511 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_326511 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_326511 prefixEnd_326511 := by exact prefixLift 326511
  have htrace : WordTrace (prefixWord ++ tailWord_326511) baseStart_326511 baseEnd_326511 := by
    simpa [prefixWord, tailWord_326511, baseEnd_326511] using wordTrace_append hprefix tailTrace_326511
  have hstable : (prefixWord ++ tailWord_326511).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_326511).length < 2 ^ (prefixWord ++ tailWord_326511).sum := by decide
  have hdescent : baseEnd_326511 < baseStart_326511 := by decide
  rcases family_descends (prefixWord ++ tailWord_326511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_326521 : List Nat := [1, 2, 1, 3, 2, 5, 1, 5]
def baseStart_326521 : Nat := 118140960795 + 326521 * 2 ^ 59
def prefixEnd_326521 : Nat := 4983230072969 + 3 ^ 40 * 326521 * 2
def baseEnd_326521 : Nat := 49677693862762138899515

theorem tailTrace_326521 : CollatzResearch.WordTrace tailWord_326521 prefixEnd_326521 49677693862762138899515 := by
  unfold tailWord_326521
  simp only [CollatzResearch.WordTrace]
  refine ⟨11909199250077657192203417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7939466166718438128135611 11909199250077657192203417)
  ·
    refine ⟨8931899437558242894152563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11909199250077657192203417 8931899437558242894152563)
    ·
      refine ⟨13397849156337364341228845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8931899437558242894152563 13397849156337364341228845)
      ·
        refine ⟨5024193433626511627960817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13397849156337364341228845 5024193433626511627960817)
        ·
          refine ⟨3768145075219883720970613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5024193433626511627960817 3768145075219883720970613)
          ·
            refine ⟨353263600801864098840995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 3768145075219883720970613 353263600801864098840995)
            ·
              refine ⟨529895401202796148261493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 353263600801864098840995 529895401202796148261493)
              ·
                refine ⟨49677693862762138899515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 529895401202796148261493 49677693862762138899515)
                ·
                  rfl

theorem cell20_326521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 5, 1, 5].length) (baseStart_326521 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_326521 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_326521 prefixEnd_326521 := by exact prefixLift 326521
  have htrace : WordTrace (prefixWord ++ tailWord_326521) baseStart_326521 baseEnd_326521 := by
    simpa [prefixWord, tailWord_326521, baseEnd_326521] using wordTrace_append hprefix tailTrace_326521
  have hstable : (prefixWord ++ tailWord_326521).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_326521).length < 2 ^ (prefixWord ++ tailWord_326521).sum := by decide
  have hdescent : baseEnd_326521 < baseStart_326521 := by decide
  rcases family_descends (prefixWord ++ tailWord_326521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_326535 : List Nat := [1, 1, 4, 2, 3, 1, 1, 1, 6]
def baseStart_326535 : Nat := 118140960795 + 326535 * 2 ^ 59
def prefixEnd_326535 : Nat := 4983230072969 + 3 ^ 40 * 326535 * 2
def baseEnd_326535 : Nat := 149039471569764590231821

theorem tailTrace_326535 : CollatzResearch.WordTrace tailWord_326535 prefixEnd_326535 149039471569764590231821 := by
  unfold tailWord_326535
  simp only [CollatzResearch.WordTrace]
  refine ⟨11909709872026937583213059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7939806581351291722142039 11909709872026937583213059)
  ·
    refine ⟨17864564808040406374819589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11909709872026937583213059 17864564808040406374819589)
    ·
      refine ⟨3349605901507576195278673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 17864564808040406374819589 3349605901507576195278673)
      ·
        refine ⟨2512204426130682146459005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3349605901507576195278673 2512204426130682146459005)
        ·
          refine ⟨942076659799005804922127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2512204426130682146459005 942076659799005804922127)
          ·
            refine ⟨1413114989698508707383191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 942076659799005804922127 1413114989698508707383191)
            ·
              refine ⟨2119672484547763061074787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1413114989698508707383191 2119672484547763061074787)
              ·
                refine ⟨3179508726821644591612181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2119672484547763061074787 3179508726821644591612181)
                ·
                  refine ⟨149039471569764590231821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3179508726821644591612181 149039471569764590231821)
                  ·
                    rfl

theorem cell20_326535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 1, 1, 6].length) (baseStart_326535 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_326535 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_326535 prefixEnd_326535 := by exact prefixLift 326535
  have htrace : WordTrace (prefixWord ++ tailWord_326535) baseStart_326535 baseEnd_326535 := by
    simpa [prefixWord, tailWord_326535, baseEnd_326535] using wordTrace_append hprefix tailTrace_326535
  have hstable : (prefixWord ++ tailWord_326535).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_326535).length < 2 ^ (prefixWord ++ tailWord_326535).sum := by decide
  have hdescent : baseEnd_326535 < baseStart_326535 := by decide
  rcases family_descends (prefixWord ++ tailWord_326535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_326538 : List Nat := [3, 1, 2, 4, 1, 2, 3, 4]
def baseStart_326538 : Nat := 118140960795 + 326538 * 2 ^ 59
def prefixEnd_326538 : Nat := 4983230072969 + 3 ^ 40 * 326538 * 2
def baseEnd_326538 : Nat := 49680280283836637710603

theorem tailTrace_326538 : CollatzResearch.WordTrace tailWord_326538 prefixEnd_326538 49680280283836637710603 := by
  unfold tailWord_326538
  simp only [CollatzResearch.WordTrace]
  refine ⟨2977454822754017273893067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7939879527344046063714845 2977454822754017273893067)
  ·
    refine ⟨4466182234131025910839601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2977454822754017273893067 4466182234131025910839601)
    ·
      refine ⟨3349636675598269433129701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4466182234131025910839601 3349636675598269433129701)
      ·
        refine ⟨628056876674675518711819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3349636675598269433129701 628056876674675518711819)
        ·
          refine ⟨942085315012013278067729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 628056876674675518711819 942085315012013278067729)
          ·
            refine ⟨706563986259009958550797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 942085315012013278067729 706563986259009958550797)
            ·
              refine ⟨264961494847128734456549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 706563986259009958550797 264961494847128734456549)
              ·
                refine ⟨49680280283836637710603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 264961494847128734456549 49680280283836637710603)
                ·
                  rfl

theorem cell20_326538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 2, 3, 4].length) (baseStart_326538 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_326538 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_326538 prefixEnd_326538 := by exact prefixLift 326538
  have htrace : WordTrace (prefixWord ++ tailWord_326538) baseStart_326538 baseEnd_326538 := by
    simpa [prefixWord, tailWord_326538, baseEnd_326538] using wordTrace_append hprefix tailTrace_326538
  have hstable : (prefixWord ++ tailWord_326538).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_326538).length < 2 ^ (prefixWord ++ tailWord_326538).sum := by decide
  have hdescent : baseEnd_326538 < baseStart_326538 := by decide
  rcases family_descends (prefixWord ++ tailWord_326538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_326562 : List Nat := [3, 3, 1, 2, 2, 3, 1, 2, 3]
def baseStart_326562 : Nat := 118140960795 + 326562 * 2 ^ 59
def prefixEnd_326562 : Nat := 4983230072969 + 3 ^ 40 * 326562 * 2
def baseEnd_326562 : Nat := 149051795105472496331711

theorem tailTrace_326562 : CollatzResearch.WordTrace tailWord_326562 prefixEnd_326562 149051795105472496331711 := by
  unfold tailWord_326562
  simp only [CollatzResearch.WordTrace]
  refine ⟨2977673660732280298611485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7940463095286080796297293 2977673660732280298611485)
  ·
    refine ⟨1116627622774605111979307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2977673660732280298611485 1116627622774605111979307)
    ·
      refine ⟨1674941434161907667968961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1116627622774605111979307 1674941434161907667968961)
      ·
        refine ⟨1256206075621430750976721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1674941434161907667968961 1256206075621430750976721)
        ·
          refine ⟨942154556716073063232541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1256206075621430750976721 942154556716073063232541)
          ·
            refine ⟨353307958768527398712203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 942154556716073063232541 353307958768527398712203)
            ·
              refine ⟨529961938152791098068305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 353307958768527398712203 529961938152791098068305)
              ·
                refine ⟨397471453614593323551229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 529961938152791098068305 397471453614593323551229)
                ·
                  refine ⟨149051795105472496331711, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 397471453614593323551229 149051795105472496331711)
                  ·
                    rfl

theorem cell20_326562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 3, 1, 2, 3].length) (baseStart_326562 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_326562 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_326562 prefixEnd_326562 := by exact prefixLift 326562
  have htrace : WordTrace (prefixWord ++ tailWord_326562) baseStart_326562 baseEnd_326562 := by
    simpa [prefixWord, tailWord_326562, baseEnd_326562] using wordTrace_append hprefix tailTrace_326562
  have hstable : (prefixWord ++ tailWord_326562).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_326562).length < 2 ^ (prefixWord ++ tailWord_326562).sum := by decide
  have hdescent : baseEnd_326562 < baseStart_326562 := by decide
  rcases family_descends (prefixWord ++ tailWord_326562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_326607 : List Nat := [1, 1, 2, 1, 1, 8, 1, 3, 2]
def baseStart_326607 : Nat := 118140960795 + 326607 * 2 ^ 59
def prefixEnd_326607 : Nat := 4983230072969 + 3 ^ 40 * 326607 * 2
def baseEnd_326607 : Nat := 149072334331652339831527

theorem tailTrace_326607 : CollatzResearch.WordTrace tailWord_326607 prefixEnd_326607 149072334331652339831527 := by
  unfold tailWord_326607
  simp only [CollatzResearch.WordTrace]
  refine ⟨11912335927766093879834075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7941557285177395919889383 11912335927766093879834075)
  ·
    refine ⟨17868503891649140819751113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11912335927766093879834075 17868503891649140819751113)
    ·
      refine ⟨13401377918736855614813335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17868503891649140819751113 13401377918736855614813335)
      ·
        refine ⟨20102066878105283422220003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13401377918736855614813335 20102066878105283422220003)
        ·
          refine ⟨30153100317157925133330005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20102066878105283422220003 30153100317157925133330005)
          ·
            refine ⟨353356644341694435156211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 30153100317157925133330005 353356644341694435156211)
            ·
              refine ⟨530034966512541652734317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 353356644341694435156211 530034966512541652734317)
              ·
                refine ⟨198763112442203119775369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 530034966512541652734317 198763112442203119775369)
                ·
                  refine ⟨149072334331652339831527, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 198763112442203119775369 149072334331652339831527)
                  ·
                    rfl

theorem cell20_326607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 8, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 8, 1, 3, 2].length) (baseStart_326607 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_326607 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_326607 prefixEnd_326607 := by exact prefixLift 326607
  have htrace : WordTrace (prefixWord ++ tailWord_326607) baseStart_326607 baseEnd_326607 := by
    simpa [prefixWord, tailWord_326607, baseEnd_326607] using wordTrace_append hprefix tailTrace_326607
  have hstable : (prefixWord ++ tailWord_326607).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_326607).length < 2 ^ (prefixWord ++ tailWord_326607).sum := by decide
  have hdescent : baseEnd_326607 < baseStart_326607 := by decide
  rcases family_descends (prefixWord ++ tailWord_326607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_326614 : List Nat := [5, 2, 1, 1, 2, 3, 6]
def baseStart_326614 : Nat := 118140960795 + 326614 * 2 ^ 59
def prefixEnd_326614 : Nat := 4983230072969 + 3 ^ 40 * 326614 * 2
def baseEnd_326614 : Nat := 16563947702487936288685

theorem tailTrace_326614 : CollatzResearch.WordTrace tailWord_326614 prefixEnd_326614 16563947702487936288685 := by
  unfold tailWord_326614
  simp only [CollatzResearch.WordTrace]
  refine ⟨744536952421295879708681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 7941727492493822716892597 744536952421295879708681)
  ·
    refine ⟨558402714315971909781511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 744536952421295879708681 558402714315971909781511)
    ·
      refine ⟨837604071473957864672267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 558402714315971909781511 837604071473957864672267)
      ·
        refine ⟨1256406107210936797008401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 837604071473957864672267 1256406107210936797008401)
        ·
          refine ⟨942304580408202597756301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1256406107210936797008401 942304580408202597756301)
          ·
            refine ⟨353364217653075974158613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 942304580408202597756301 353364217653075974158613)
            ·
              refine ⟨16563947702487936288685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 353364217653075974158613 16563947702487936288685)
              ·
                rfl

theorem cell20_326614_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 3, 6].length) (baseStart_326614 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_326614 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_326614 prefixEnd_326614 := by exact prefixLift 326614
  have htrace : WordTrace (prefixWord ++ tailWord_326614) baseStart_326614 baseEnd_326614 := by
    simpa [prefixWord, tailWord_326614, baseEnd_326614] using wordTrace_append hprefix tailTrace_326614
  have hstable : (prefixWord ++ tailWord_326614).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_326614).length < 2 ^ (prefixWord ++ tailWord_326614).sum := by decide
  have hdescent : baseEnd_326614 < baseStart_326614 := by decide
  rcases family_descends (prefixWord ++ tailWord_326614) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_326618 : List Nat := [3, 1, 1, 2, 4, 1, 8]
def baseStart_326618 : Nat := 118140960795 + 326618 * 2 ^ 59
def prefixEnd_326618 : Nat := 4983230072969 + 3 ^ 40 * 326618 * 2
def baseEnd_326618 : Nat := 16564150559042798940535

theorem tailTrace_326618 : CollatzResearch.WordTrace tailWord_326618 prefixEnd_326618 16564150559042798940535 := by
  unfold tailWord_326618
  simp only [CollatzResearch.WordTrace]
  refine ⟨2978184282681560689621127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7941824753817495172323005 2978184282681560689621127)
  ·
    refine ⟨4467276424022341034431691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2978184282681560689621127 4467276424022341034431691)
    ·
      refine ⟨6700914636033511551647537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4467276424022341034431691 6700914636033511551647537)
      ·
        refine ⟨5025685977025133663735653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6700914636033511551647537 5025685977025133663735653)
        ·
          refine ⟨942316120692212561950435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5025685977025133663735653 942316120692212561950435)
          ·
            refine ⟨1413474181038318842925653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 942316120692212561950435 1413474181038318842925653)
            ·
              refine ⟨16564150559042798940535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1413474181038318842925653 16564150559042798940535)
              ·
                rfl

theorem cell20_326618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 8].length) (baseStart_326618 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_326618 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_326618 prefixEnd_326618 := by exact prefixLift 326618
  have htrace : WordTrace (prefixWord ++ tailWord_326618) baseStart_326618 baseEnd_326618 := by
    simpa [prefixWord, tailWord_326618, baseEnd_326618] using wordTrace_append hprefix tailTrace_326618
  have hstable : (prefixWord ++ tailWord_326618).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_326618).length < 2 ^ (prefixWord ++ tailWord_326618).sum := by decide
  have hdescent : baseEnd_326618 < baseStart_326618 := by decide
  rcases family_descends (prefixWord ++ tailWord_326618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_326680 : List Nat := [2, 1, 2, 3, 2, 2, 1, 4, 3]
def baseStart_326680 : Nat := 118140960795 + 326680 * 2 ^ 59
def prefixEnd_326680 : Nat := 4983230072969 + 3 ^ 40 * 326680 * 2
def baseEnd_326680 : Nat := 149105653520788530397895

theorem tailTrace_326680 : CollatzResearch.WordTrace tailWord_326680 prefixEnd_326680 149105653520788530397895 := by
  unfold tailWord_326680
  simp only [CollatzResearch.WordTrace]
  refine ⟨5957499228250813673620747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7943332304334418231494329 5957499228250813673620747)
  ·
    refine ⟨8936248842376220510431121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5957499228250813673620747 8936248842376220510431121)
    ·
      refine ⟨6702186631782165382823341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8936248842376220510431121 6702186631782165382823341)
      ·
        refine ⟨2513319986918312018558753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6702186631782165382823341 2513319986918312018558753)
        ·
          refine ⟨1884989990188734013919065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2513319986918312018558753 1884989990188734013919065)
          ·
            refine ⟨1413742492641550510439299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1884989990188734013919065 1413742492641550510439299)
            ·
              refine ⟨2120613738962325765658949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1413742492641550510439299 2120613738962325765658949)
              ·
                refine ⟨397615076055436081061053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2120613738962325765658949 397615076055436081061053)
                ·
                  refine ⟨149105653520788530397895, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 397615076055436081061053 149105653520788530397895)
                  ·
                    rfl

theorem cell20_326680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 1, 4, 3].length) (baseStart_326680 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_326680 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_326680 prefixEnd_326680 := by exact prefixLift 326680
  have htrace : WordTrace (prefixWord ++ tailWord_326680) baseStart_326680 baseEnd_326680 := by
    simpa [prefixWord, tailWord_326680, baseEnd_326680] using wordTrace_append hprefix tailTrace_326680
  have hstable : (prefixWord ++ tailWord_326680).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_326680).length < 2 ^ (prefixWord ++ tailWord_326680).sum := by decide
  have hdescent : baseEnd_326680 < baseStart_326680 := by decide
  rcases family_descends (prefixWord ++ tailWord_326680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_326766 : List Nat := [4, 1, 2, 2, 1, 4, 2, 4]
def baseStart_326766 : Nat := 118140960795 + 326766 * 2 ^ 59
def prefixEnd_326766 : Nat := 4983230072969 + 3 ^ 40 * 326766 * 2
def baseEnd_326766 : Nat := 49714968754718151176959

theorem tailTrace_326766 : CollatzResearch.WordTrace tailWord_326766 prefixEnd_326766 49714968754718151176959 := by
  unfold tailWord_326766
  simp only [CollatzResearch.WordTrace]
  refine ⟨1489766891773758004359019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 7945423422793376023248101 1489766891773758004359019)
  ·
    refine ⟨2234650337660637006538529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1489766891773758004359019 2234650337660637006538529)
    ·
      refine ⟨1675987753245477754903897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2234650337660637006538529 1675987753245477754903897)
      ·
        refine ⟨1256990814934108316177923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1675987753245477754903897 1256990814934108316177923)
        ·
          refine ⟨1885486222401162474266885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1256990814934108316177923 1885486222401162474266885)
          ·
            refine ⟨353528666700217963925041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1885486222401162474266885 353528666700217963925041)
            ·
              refine ⟨265146500025163472943781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 353528666700217963925041 265146500025163472943781)
              ·
                refine ⟨49714968754718151176959, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 265146500025163472943781 49714968754718151176959)
                ·
                  rfl

theorem cell20_326766_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 4, 2, 4].length) (baseStart_326766 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_326766 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_326766 prefixEnd_326766 := by exact prefixLift 326766
  have htrace : WordTrace (prefixWord ++ tailWord_326766) baseStart_326766 baseEnd_326766 := by
    simpa [prefixWord, tailWord_326766, baseEnd_326766] using wordTrace_append hprefix tailTrace_326766
  have hstable : (prefixWord ++ tailWord_326766).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_326766).length < 2 ^ (prefixWord ++ tailWord_326766).sum := by decide
  have hdescent : baseEnd_326766 < baseStart_326766 := by decide
  rcases family_descends (prefixWord ++ tailWord_326766) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_326770 : List Nat := [3, 2, 1, 2, 2, 1, 3, 6]
def baseStart_326770 : Nat := 118140960795 + 326770 * 2 ^ 59
def prefixEnd_326770 : Nat := 4983230072969 + 3 ^ 40 * 326770 * 2
def baseEnd_326770 : Nat := 49715577324382739132509

theorem tailTrace_326770 : CollatzResearch.WordTrace tailWord_326770 prefixEnd_326770 49715577324382739132509 := by
  unfold tailWord_326770
  simp only [CollatzResearch.WordTrace]
  refine ⟨2979570256543893179504441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7945520684117048478678509 2979570256543893179504441)
  ·
    refine ⟨2234677692407919884628331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2979570256543893179504441 2234677692407919884628331)
    ·
      refine ⟨3352016538611879826942497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2234677692407919884628331 3352016538611879826942497)
      ·
        refine ⟨2514012403958909870206873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3352016538611879826942497 2514012403958909870206873)
        ·
          refine ⟨1885509302969182402655155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2514012403958909870206873 1885509302969182402655155)
          ·
            refine ⟨2828263954453773603982733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1885509302969182402655155 2828263954453773603982733)
            ·
              refine ⟨1060598982920165101493525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2828263954453773603982733 1060598982920165101493525)
              ·
                refine ⟨49715577324382739132509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1060598982920165101493525 49715577324382739132509)
                ·
                  rfl

theorem cell20_326770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 3, 6].length) (baseStart_326770 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_326770 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_326770 prefixEnd_326770 := by exact prefixLift 326770
  have htrace : WordTrace (prefixWord ++ tailWord_326770) baseStart_326770 baseEnd_326770 := by
    simpa [prefixWord, tailWord_326770, baseEnd_326770] using wordTrace_append hprefix tailTrace_326770
  have hstable : (prefixWord ++ tailWord_326770).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_326770).length < 2 ^ (prefixWord ++ tailWord_326770).sum := by decide
  have hdescent : baseEnd_326770 < baseStart_326770 := by decide
  rcases family_descends (prefixWord ++ tailWord_326770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_326784 : List Nat := [2, 1, 1, 2, 1, 3, 2, 2, 6]
def baseStart_326784 : Nat := 118140960795 + 326784 * 2 ^ 59
def prefixEnd_326784 : Nat := 4983230072969 + 3 ^ 40 * 326784 * 2
def baseEnd_326784 : Nat := 149153121954626390930803

theorem tailTrace_326784 : CollatzResearch.WordTrace tailWord_326784 prefixEnd_326784 149153121954626390930803 := by
  unfold tailWord_326784
  simp only [CollatzResearch.WordTrace]
  refine ⟨5959395824062426554513703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7945861098749902072684937 5959395824062426554513703)
  ·
    refine ⟨8939093736093639831770555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5959395824062426554513703 8939093736093639831770555)
    ·
      refine ⟨13408640604140459747655833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8939093736093639831770555 13408640604140459747655833)
      ·
        refine ⟨10056480453105344810741875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13408640604140459747655833 10056480453105344810741875)
        ·
          refine ⟨15084720679658017216112813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10056480453105344810741875 15084720679658017216112813)
          ·
            refine ⟨5656770254871756456042305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15084720679658017216112813 5656770254871756456042305)
            ·
              refine ⟨4242577691153817342031729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5656770254871756456042305 4242577691153817342031729)
              ·
                refine ⟨3181933268365363006523797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4242577691153817342031729 3181933268365363006523797)
                ·
                  refine ⟨149153121954626390930803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3181933268365363006523797 149153121954626390930803)
                  ·
                    rfl

theorem cell20_326784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 2, 2, 6].length) (baseStart_326784 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_326784 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_326784 prefixEnd_326784 := by exact prefixLift 326784
  have htrace : WordTrace (prefixWord ++ tailWord_326784) baseStart_326784 baseEnd_326784 := by
    simpa [prefixWord, tailWord_326784, baseEnd_326784] using wordTrace_append hprefix tailTrace_326784
  have hstable : (prefixWord ++ tailWord_326784).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_326784).length < 2 ^ (prefixWord ++ tailWord_326784).sum := by decide
  have hdescent : baseEnd_326784 < baseStart_326784 := by decide
  rcases family_descends (prefixWord ++ tailWord_326784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_326794 : List Nat := [3, 1, 2, 3, 1, 1, 2, 4, 3]
def baseStart_326794 : Nat := 118140960795 + 326794 * 2 ^ 59
def prefixEnd_326794 : Nat := 4983230072969 + 3 ^ 40 * 326794 * 2
def baseEnd_326794 : Nat := 149157686227110800597429

theorem tailTrace_326794 : CollatzResearch.WordTrace tailWord_326794 prefixEnd_326794 149157686227110800597429 := by
  unfold tailWord_326794
  simp only [CollatzResearch.WordTrace]
  refine ⟨2979789094522156204222859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7946104252059083211260957 2979789094522156204222859)
  ·
    refine ⟨4469683641783234306334289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2979789094522156204222859 4469683641783234306334289)
    ·
      refine ⟨3352262731337425729750717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4469683641783234306334289 3352262731337425729750717)
      ·
        refine ⟨1257098524251534648656519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3352262731337425729750717 1257098524251534648656519)
        ·
          refine ⟨1885647786377301972984779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1257098524251534648656519 1885647786377301972984779)
          ·
            refine ⟨2828471679565952959477169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1885647786377301972984779 2828471679565952959477169)
            ·
              refine ⟨2121353759674464719607877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2828471679565952959477169 2121353759674464719607877)
              ·
                refine ⟨397753829938962134926477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2121353759674464719607877 397753829938962134926477)
                ·
                  refine ⟨149157686227110800597429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 397753829938962134926477 149157686227110800597429)
                  ·
                    rfl

theorem cell20_326794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 2, 4, 3].length) (baseStart_326794 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_326794 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_326794 prefixEnd_326794 := by exact prefixLift 326794
  have htrace : WordTrace (prefixWord ++ tailWord_326794) baseStart_326794 baseEnd_326794 := by
    simpa [prefixWord, tailWord_326794, baseEnd_326794] using wordTrace_append hprefix tailTrace_326794
  have hstable : (prefixWord ++ tailWord_326794).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_326794).length < 2 ^ (prefixWord ++ tailWord_326794).sum := by decide
  have hdescent : baseEnd_326794 < baseStart_326794 := by decide
  rcases family_descends (prefixWord ++ tailWord_326794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_326808 : List Nat := [2, 1, 2, 4, 2, 1, 1, 7]
def baseStart_326808 : Nat := 118140960795 + 326808 * 2 ^ 59
def prefixEnd_326808 : Nat := 4983230072969 + 3 ^ 40 * 326808 * 2
def baseEnd_326808 : Nat := 49721358736196324710235

theorem tailTrace_326808 : CollatzResearch.WordTrace tailWord_326808 prefixEnd_326808 49721358736196324710235 := by
  unfold tailWord_326808
  simp only [CollatzResearch.WordTrace]
  refine ⟨5959833500018952603950539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7946444666691936805267385 5959833500018952603950539)
  ·
    refine ⟨8939750250028428905925809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5959833500018952603950539 8939750250028428905925809)
    ·
      refine ⟨6704812687521321679444357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8939750250028428905925809 6704812687521321679444357)
      ·
        refine ⟨1257152378910247814895817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6704812687521321679444357 1257152378910247814895817)
        ·
          refine ⟨942864284182685861171863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1257152378910247814895817 942864284182685861171863)
          ·
            refine ⟨1414296426274028791757795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 942864284182685861171863 1414296426274028791757795)
            ·
              refine ⟨2121444639411043187636693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1414296426274028791757795 2121444639411043187636693)
              ·
                refine ⟨49721358736196324710235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2121444639411043187636693 49721358736196324710235)
                ·
                  rfl

theorem cell20_326808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 1, 7].length) (baseStart_326808 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_326808 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_326808 prefixEnd_326808 := by exact prefixLift 326808
  have htrace : WordTrace (prefixWord ++ tailWord_326808) baseStart_326808 baseEnd_326808 := by
    simpa [prefixWord, tailWord_326808, baseEnd_326808] using wordTrace_append hprefix tailTrace_326808
  have hstable : (prefixWord ++ tailWord_326808).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_326808).length < 2 ^ (prefixWord ++ tailWord_326808).sum := by decide
  have hdescent : baseEnd_326808 < baseStart_326808 := by decide
  rcases family_descends (prefixWord ++ tailWord_326808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_326846 : List Nat := [4, 2, 1, 1, 3, 9]
def baseStart_326846 : Nat := 118140960795 + 326846 * 2 ^ 59
def prefixEnd_326846 : Nat := 4983230072969 + 3 ^ 40 * 326846 * 2
def baseEnd_326846 : Nat := 5525237794223323365329

theorem tailTrace_326846 : CollatzResearch.WordTrace tailWord_326846 prefixEnd_326846 5525237794223323365329 := by
  unfold tailWord_326846
  simp only [CollatzResearch.WordTrace]
  refine ⟨1490131621737529712223049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 7947368649266825131856261 1490131621737529712223049)
  ·
    refine ⟨1117598716303147284167287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1490131621737529712223049 1117598716303147284167287)
    ·
      refine ⟨1676398074454720926250931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1117598716303147284167287 1676398074454720926250931)
      ·
        refine ⟨2514597111682081389376397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1676398074454720926250931 2514597111682081389376397)
        ·
          refine ⟨942973916880780521016149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2514597111682081389376397 942973916880780521016149)
          ·
            refine ⟨5525237794223323365329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 942973916880780521016149 5525237794223323365329)
            ·
              rfl

theorem cell20_326846_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 9].length) (baseStart_326846 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_326846 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_326846 prefixEnd_326846 := by exact prefixLift 326846
  have htrace : WordTrace (prefixWord ++ tailWord_326846) baseStart_326846 baseEnd_326846 := by
    simpa [prefixWord, tailWord_326846, baseEnd_326846] using wordTrace_append hprefix tailTrace_326846
  have hstable : (prefixWord ++ tailWord_326846).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_326846).length < 2 ^ (prefixWord ++ tailWord_326846).sum := by decide
  have hdescent : baseEnd_326846 < baseStart_326846 := by decide
  rcases family_descends (prefixWord ++ tailWord_326846) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_326849 : List Nat := [1, 2, 6, 1, 1, 1, 1, 4, 3]
def baseStart_326849 : Nat := 118140960795 + 326849 * 2 ^ 59
def prefixEnd_326849 : Nat := 4983230072969 + 3 ^ 40 * 326849 * 2
def baseEnd_326849 : Nat := 149182789725775053763871

theorem tailTrace_326849 : CollatzResearch.WordTrace tailWord_326849 prefixEnd_326849 149182789725775053763871 := by
  unfold tailWord_326849
  simp only [CollatzResearch.WordTrace]
  refine ⟨11921162392889369210143601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7947441595259579473429067 11921162392889369210143601)
  ·
    refine ⟨8940871794667026907607701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11921162392889369210143601 8940871794667026907607701)
    ·
      refine ⟨419103365375016886294111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 8940871794667026907607701 419103365375016886294111)
      ·
        refine ⟨628655048062525329441167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 419103365375016886294111 628655048062525329441167)
        ·
          refine ⟨942982572093787994161751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 628655048062525329441167 942982572093787994161751)
          ·
            refine ⟨1414473858140681991242627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 942982572093787994161751 1414473858140681991242627)
            ·
              refine ⟨2121710787211022986863941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1414473858140681991242627 2121710787211022986863941)
              ·
                refine ⟨397820772602066810036989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2121710787211022986863941 397820772602066810036989)
                ·
                  refine ⟨149182789725775053763871, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 397820772602066810036989 149182789725775053763871)
                  ·
                    rfl

theorem cell20_326849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 1, 4, 3].length) (baseStart_326849 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_326849 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_326849 prefixEnd_326849 := by exact prefixLift 326849
  have htrace : WordTrace (prefixWord ++ tailWord_326849) baseStart_326849 baseEnd_326849 := by
    simpa [prefixWord, tailWord_326849, baseEnd_326849] using wordTrace_append hprefix tailTrace_326849
  have hstable : (prefixWord ++ tailWord_326849).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_326849).length < 2 ^ (prefixWord ++ tailWord_326849).sum := by decide
  have hdescent : baseEnd_326849 < baseStart_326849 := by decide
  rcases family_descends (prefixWord ++ tailWord_326849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_326894 : List Nat := [4, 1, 2, 1, 1, 1, 3, 5, 2]
def baseStart_326894 : Nat := 118140960795 + 326894 * 2 ^ 59
def prefixEnd_326894 : Nat := 4983230072969 + 3 ^ 40 * 326894 * 2
def baseEnd_326894 : Nat := 149203328951954897263687

theorem tailTrace_326894 : CollatzResearch.WordTrace tailWord_326894 prefixEnd_326894 149203328951954897263687 := by
  unfold tailWord_326894
  simp only [CollatzResearch.WordTrace]
  refine ⟨1490350459715792736941467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 7948535785150894597021157 1490350459715792736941467)
  ·
    refine ⟨2235525689573689105412201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1490350459715792736941467 2235525689573689105412201)
    ·
      refine ⟨1676644267180266829059151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2235525689573689105412201 1676644267180266829059151)
      ·
        refine ⟨2514966400770400243588727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1676644267180266829059151 2514966400770400243588727)
        ·
          refine ⟨3772449601155600365383091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2514966400770400243588727 3772449601155600365383091)
          ·
            refine ⟨5658674401733400548074637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3772449601155600365383091 5658674401733400548074637)
            ·
              refine ⟨2122002900650025205527989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5658674401733400548074637 2122002900650025205527989)
              ·
                refine ⟨198937771935939863018249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2122002900650025205527989 198937771935939863018249)
                ·
                  refine ⟨149203328951954897263687, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 198937771935939863018249 149203328951954897263687)
                  ·
                    rfl

theorem cell20_326894_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 3, 5, 2].length) (baseStart_326894 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_326894 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_326894 prefixEnd_326894 := by exact prefixLift 326894
  have htrace : WordTrace (prefixWord ++ tailWord_326894) baseStart_326894 baseEnd_326894 := by
    simpa [prefixWord, tailWord_326894, baseEnd_326894] using wordTrace_append hprefix tailTrace_326894
  have hstable : (prefixWord ++ tailWord_326894).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_326894).length < 2 ^ (prefixWord ++ tailWord_326894).sum := by decide
  have hdescent : baseEnd_326894 < baseStart_326894 := by decide
  rcases family_descends (prefixWord ++ tailWord_326894) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_326900 : List Nat := [2, 6, 1, 2, 1, 2, 1, 2, 3]
def baseStart_326900 : Nat := 118140960795 + 326900 * 2 ^ 59
def prefixEnd_326900 : Nat := 4983230072969 + 3 ^ 40 * 326900 * 2
def baseEnd_326900 : Nat := 149206067515445543063663

theorem tailTrace_326900 : CollatzResearch.WordTrace tailWord_326900 prefixEnd_326900 149206067515445543063663 := by
  unfold tailWord_326900
  simp only [CollatzResearch.WordTrace]
  refine ⟨5961511257852302460125077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7948681677136403280166769 5961511257852302460125077)
  ·
    refine ⟨279445840211826677818363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 5961511257852302460125077 279445840211826677818363)
    ·
      refine ⟨419168760317740016727545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 279445840211826677818363 419168760317740016727545)
      ·
        refine ⟨314376570238305012545659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 419168760317740016727545 314376570238305012545659)
        ·
          refine ⟨471564855357457518818489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 314376570238305012545659 471564855357457518818489)
          ·
            refine ⟨353673641518093139113867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 471564855357457518818489 353673641518093139113867)
            ·
              refine ⟨530510462277139708670801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 353673641518093139113867 530510462277139708670801)
              ·
                refine ⟨397882846707854781503101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 530510462277139708670801 397882846707854781503101)
                ·
                  refine ⟨149206067515445543063663, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 397882846707854781503101 149206067515445543063663)
                  ·
                    rfl

theorem cell20_326900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 1, 2, 1, 2, 3].length) (baseStart_326900 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_326900 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_326900 prefixEnd_326900 := by exact prefixLift 326900
  have htrace : WordTrace (prefixWord ++ tailWord_326900) baseStart_326900 baseEnd_326900 := by
    simpa [prefixWord, tailWord_326900, baseEnd_326900] using wordTrace_append hprefix tailTrace_326900
  have hstable : (prefixWord ++ tailWord_326900).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_326900).length < 2 ^ (prefixWord ++ tailWord_326900).sum := by decide
  have hdescent : baseEnd_326900 < baseStart_326900 := by decide
  rcases family_descends (prefixWord ++ tailWord_326900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_326905 : List Nat := [1, 2, 1, 3, 1, 1, 11]
def baseStart_326905 : Nat := 118140960795 + 326905 * 2 ^ 59
def prefixEnd_326905 : Nat := 4983230072969 + 3 ^ 40 * 326905 * 2
def baseEnd_326905 : Nat := 16578705516854194210775

theorem tailTrace_326905 : CollatzResearch.WordTrace tailWord_326905 prefixEnd_326905 16578705516854194210775 := by
  unfold tailWord_326905
  simp only [CollatzResearch.WordTrace]
  refine ⟨11923204880686490774182169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7948803253790993849454779 11923204880686490774182169)
  ·
    refine ⟨8942403660514868080636627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11923204880686490774182169 8942403660514868080636627)
    ·
      refine ⟨13413605490772302120954941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8942403660514868080636627 13413605490772302120954941)
      ·
        refine ⟨5030102059039613295358103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13413605490772302120954941 5030102059039613295358103)
        ·
          refine ⟨7545153088559419943037155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5030102059039613295358103 7545153088559419943037155)
          ·
            refine ⟨11317729632839129914555733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7545153088559419943037155 11317729632839129914555733)
            ·
              refine ⟨16578705516854194210775, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 11317729632839129914555733 16578705516854194210775)
              ·
                rfl

theorem cell20_326905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 11].length) (baseStart_326905 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_326905 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_326905 prefixEnd_326905 := by exact prefixLift 326905
  have htrace : WordTrace (prefixWord ++ tailWord_326905) baseStart_326905 baseEnd_326905 := by
    simpa [prefixWord, tailWord_326905, baseEnd_326905] using wordTrace_append hprefix tailTrace_326905
  have hstable : (prefixWord ++ tailWord_326905).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_326905).length < 2 ^ (prefixWord ++ tailWord_326905).sum := by decide
  have hdescent : baseEnd_326905 < baseStart_326905 := by decide
  rcases family_descends (prefixWord ++ tailWord_326905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_326908 : List Nat := [2, 2, 2, 1, 5, 1, 1, 1, 5]
def baseStart_326908 : Nat := 118140960795 + 326908 * 2 ^ 59
def prefixEnd_326908 : Nat := 4983230072969 + 3 ^ 40 * 326908 * 2
def baseEnd_326908 : Nat := 149209718933433070796963

theorem tailTrace_326908 : CollatzResearch.WordTrace tailWord_326908 prefixEnd_326908 149209718933433070796963 := by
  unfold tailWord_326908
  simp only [CollatzResearch.WordTrace]
  refine ⟨5961657149837811143270689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7948876199783748191027585 5961657149837811143270689)
  ·
    refine ⟨4471242862378358357453017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5961657149837811143270689 4471242862378358357453017)
    ·
      refine ⟨3353432146783768768089763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4471242862378358357453017 3353432146783768768089763)
      ·
        refine ⟨5030148220175653152134645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3353432146783768768089763 5030148220175653152134645)
        ·
          refine ⟨471576395641467483012623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 5030148220175653152134645 471576395641467483012623)
          ·
            refine ⟨707364593462201224518935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 471576395641467483012623 707364593462201224518935)
            ·
              refine ⟨1061046890193301836778403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 707364593462201224518935 1061046890193301836778403)
              ·
                refine ⟨1591570335289952755167605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1061046890193301836778403 1591570335289952755167605)
                ·
                  refine ⟨149209718933433070796963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1591570335289952755167605 149209718933433070796963)
                  ·
                    rfl

theorem cell20_326908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 5, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 5, 1, 1, 1, 5].length) (baseStart_326908 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_326908 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_326908 prefixEnd_326908 := by exact prefixLift 326908
  have htrace : WordTrace (prefixWord ++ tailWord_326908) baseStart_326908 baseEnd_326908 := by
    simpa [prefixWord, tailWord_326908, baseEnd_326908] using wordTrace_append hprefix tailTrace_326908
  have hstable : (prefixWord ++ tailWord_326908).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_326908).length < 2 ^ (prefixWord ++ tailWord_326908).sum := by decide
  have hdescent : baseEnd_326908 < baseStart_326908 := by decide
  rcases family_descends (prefixWord ++ tailWord_326908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_326915 : List Nat := [1, 1, 1, 3, 2, 5, 2, 1, 4]
def baseStart_326915 : Nat := 118140960795 + 326915 * 2 ^ 59
def prefixEnd_326915 : Nat := 4983230072969 + 3 ^ 40 * 326915 * 2
def baseEnd_326915 : Nat := 149212913924172157563601

theorem tailTrace_326915 : CollatzResearch.WordTrace tailWord_326915 prefixEnd_326915 149212913924172157563601 := by
  unfold tailWord_326915
  simp only [CollatzResearch.WordTrace]
  refine ⟨11923569610650262482046199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7949046407100174988030799 11923569610650262482046199)
  ·
    refine ⟨17885354415975393723069299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11923569610650262482046199 17885354415975393723069299)
    ·
      refine ⟨26828031623963090584603949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17885354415975393723069299 26828031623963090584603949)
      ·
        refine ⟨10060511858986158969226481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26828031623963090584603949 10060511858986158969226481)
        ·
          refine ⟨7545383894239619226919861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10060511858986158969226481 7545383894239619226919861)
          ·
            refine ⟨707379740084964302523737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 7545383894239619226919861 707379740084964302523737)
            ·
              refine ⟨530534805063723226892803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 707379740084964302523737 530534805063723226892803)
              ·
                refine ⟨795802207595584840339205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 530534805063723226892803 795802207595584840339205)
                ·
                  refine ⟨149212913924172157563601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 795802207595584840339205 149212913924172157563601)
                  ·
                    rfl

theorem cell20_326915_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 5, 2, 1, 4].length) (baseStart_326915 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_326915 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_326915 prefixEnd_326915 := by exact prefixLift 326915
  have htrace : WordTrace (prefixWord ++ tailWord_326915) baseStart_326915 baseEnd_326915 := by
    simpa [prefixWord, tailWord_326915, baseEnd_326915] using wordTrace_append hprefix tailTrace_326915
  have hstable : (prefixWord ++ tailWord_326915).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_326915).length < 2 ^ (prefixWord ++ tailWord_326915).sum := by decide
  have hdescent : baseEnd_326915 < baseStart_326915 := by decide
  rcases family_descends (prefixWord ++ tailWord_326915) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_326949 : List Nat := [1, 3, 1, 2, 4, 3, 1, 3, 2]
def baseStart_326949 : Nat := 118140960795 + 326949 * 2 ^ 59
def prefixEnd_326949 : Nat := 4983230072969 + 3 ^ 40 * 326949 * 2
def baseEnd_326949 : Nat := 149228432450619150430129

theorem tailTrace_326949 : CollatzResearch.WordTrace tailWord_326949 prefixEnd_326949 149228432450619150430129 := by
  unfold tailWord_326949
  simp only [CollatzResearch.WordTrace]
  refine ⟨11924809692527086288783901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7949873128351390859189267 11924809692527086288783901)
  ·
    refine ⟨4471803634697657358293963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11924809692527086288783901 4471803634697657358293963)
    ·
      refine ⟨6707705452046486037440945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4471803634697657358293963 6707705452046486037440945)
      ·
        refine ⟨5030779089034864528080709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6707705452046486037440945 5030779089034864528080709)
        ·
          refine ⟨943271079194037099015133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5030779089034864528080709 943271079194037099015133)
          ·
            refine ⟨353726654697763912130675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 943271079194037099015133 353726654697763912130675)
            ·
              refine ⟨530589982046645868196013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 353726654697763912130675 530589982046645868196013)
              ·
                refine ⟨198971243267492200573505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 530589982046645868196013 198971243267492200573505)
                ·
                  refine ⟨149228432450619150430129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 198971243267492200573505 149228432450619150430129)
                  ·
                    rfl

theorem cell20_326949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 3, 1, 3, 2].length) (baseStart_326949 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_326949 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_326949 prefixEnd_326949 := by exact prefixLift 326949
  have htrace : WordTrace (prefixWord ++ tailWord_326949) baseStart_326949 baseEnd_326949 := by
    simpa [prefixWord, tailWord_326949, baseEnd_326949] using wordTrace_append hprefix tailTrace_326949
  have hstable : (prefixWord ++ tailWord_326949).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_326949).length < 2 ^ (prefixWord ++ tailWord_326949).sum := by decide
  have hdescent : baseEnd_326949 < baseStart_326949 := by decide
  rcases family_descends (prefixWord ++ tailWord_326949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_326966 : List Nat := [5, 1, 2, 3, 1, 2, 1, 1, 4]
def baseStart_326966 : Nat := 118140960795 + 326966 * 2 ^ 59
def prefixEnd_326966 : Nat := 4983230072969 + 3 ^ 40 * 326966 * 2
def baseEnd_326966 : Nat := 149236191713842646863393

theorem tailTrace_326966 : CollatzResearch.WordTrace tailWord_326966 prefixEnd_326966 149236191713842646863393 := by
  unfold tailWord_326966
  simp only [CollatzResearch.WordTrace]
  refine ⟨745339358341593637009547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 7950286488976998794768501 745339358341593637009547)
  ·
    refine ⟨1118009037512390455514321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 745339358341593637009547 1118009037512390455514321)
    ·
      refine ⟨838506778134292841635741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1118009037512390455514321 838506778134292841635741)
      ·
        refine ⟨314440041800359815613403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 838506778134292841635741 314440041800359815613403)
        ·
          refine ⟨471660062700539723420105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 314440041800359815613403 471660062700539723420105)
          ·
            refine ⟨353745047025404792565079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 471660062700539723420105 353745047025404792565079)
            ·
              refine ⟨530617570538107188847619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 353745047025404792565079 530617570538107188847619)
              ·
                refine ⟨795926355807160783271429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 530617570538107188847619 795926355807160783271429)
                ·
                  refine ⟨149236191713842646863393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 795926355807160783271429 149236191713842646863393)
                  ·
                    rfl

theorem cell20_326966_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 1, 2, 1, 1, 4].length) (baseStart_326966 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_326966 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_326966 prefixEnd_326966 := by exact prefixLift 326966
  have htrace : WordTrace (prefixWord ++ tailWord_326966) baseStart_326966 baseEnd_326966 := by
    simpa [prefixWord, tailWord_326966, baseEnd_326966] using wordTrace_append hprefix tailTrace_326966
  have hstable : (prefixWord ++ tailWord_326966).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_326966).length < 2 ^ (prefixWord ++ tailWord_326966).sum := by decide
  have hdescent : baseEnd_326966 < baseStart_326966 := by decide
  rcases family_descends (prefixWord ++ tailWord_326966) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_326977 : List Nat := [1, 2, 5, 2, 1, 2, 2, 5]
def baseStart_326977 : Nat := 118140960795 + 326977 * 2 ^ 59
def prefixEnd_326977 : Nat := 4983230072969 + 3 ^ 40 * 326977 * 2
def baseEnd_326977 : Nat := 49747070804525165832227

theorem tailTrace_326977 : CollatzResearch.WordTrace tailWord_326977 prefixEnd_326977 49747070804525165832227 := by
  unfold tailWord_326977
  simp only [CollatzResearch.WordTrace]
  refine ⟨11925830936425647070803185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7950553957617098047202123 11925830936425647070803185)
  ·
    refine ⟨8944373202319235303102389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11925830936425647070803185 8944373202319235303102389)
    ·
      refine ⟨838534987717428309665849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 8944373202319235303102389 838534987717428309665849)
      ·
        refine ⟨628901240788071232249387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 838534987717428309665849 628901240788071232249387)
        ·
          refine ⟨943351861182106848374081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 628901240788071232249387 943351861182106848374081)
          ·
            refine ⟨707513895886580136280561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 943351861182106848374081 707513895886580136280561)
            ·
              refine ⟨530635421914935102210421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 707513895886580136280561 530635421914935102210421)
              ·
                refine ⟨49747070804525165832227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 530635421914935102210421 49747070804525165832227)
                ·
                  rfl

theorem cell20_326977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 2, 2, 5].length) (baseStart_326977 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_326977 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_326977 prefixEnd_326977 := by exact prefixLift 326977
  have htrace : WordTrace (prefixWord ++ tailWord_326977) baseStart_326977 baseEnd_326977 := by
    simpa [prefixWord, tailWord_326977, baseEnd_326977] using wordTrace_append hprefix tailTrace_326977
  have hstable : (prefixWord ++ tailWord_326977).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_326977).length < 2 ^ (prefixWord ++ tailWord_326977).sum := by decide
  have hdescent : baseEnd_326977 < baseStart_326977 := by decide
  rcases family_descends (prefixWord ++ tailWord_326977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_326980 : List Nat := [2, 3, 4, 1, 1, 1, 4, 1, 3]
def baseStart_326980 : Nat := 118140960795 + 326980 * 2 ^ 59
def prefixEnd_326980 : Nat := 4983230072969 + 3 ^ 40 * 326980 * 2
def baseEnd_326980 : Nat := 149242581695320820396669

theorem tailTrace_326980 : CollatzResearch.WordTrace tailWord_326980 prefixEnd_326980 149242581695320820396669 := by
  unfold tailWord_326980
  simp only [CollatzResearch.WordTrace]
  refine ⟨5962970177707389291581197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7950626903609852388774929 5962970177707389291581197)
  ·
    refine ⟨2236113816640270984342949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5962970177707389291581197 2236113816640270984342949)
    ·
      refine ⟨419271340620050809564303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2236113816640270984342949 419271340620050809564303)
      ·
        refine ⟨628907010930076214346455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 419271340620050809564303 628907010930076214346455)
        ·
          refine ⟨943360516395114321519683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 628907010930076214346455 943360516395114321519683)
          ·
            refine ⟨1415040774592671482279525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 943360516395114321519683 1415040774592671482279525)
            ·
              refine ⟨265320145236125902927411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1415040774592671482279525 265320145236125902927411)
              ·
                refine ⟨397980217854188854391117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 265320145236125902927411 397980217854188854391117)
                ·
                  refine ⟨149242581695320820396669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 397980217854188854391117 149242581695320820396669)
                  ·
                    rfl

theorem cell20_326980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 4, 1, 3].length) (baseStart_326980 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_326980 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_326980 prefixEnd_326980 := by exact prefixLift 326980
  have htrace : WordTrace (prefixWord ++ tailWord_326980) baseStart_326980 baseEnd_326980 := by
    simpa [prefixWord, tailWord_326980, baseEnd_326980] using wordTrace_append hprefix tailTrace_326980
  have hstable : (prefixWord ++ tailWord_326980).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_326980).length < 2 ^ (prefixWord ++ tailWord_326980).sum := by decide
  have hdescent : baseEnd_326980 < baseStart_326980 := by decide
  rcases family_descends (prefixWord ++ tailWord_326980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_327074 : List Nat := [3, 3, 1, 2, 1, 3, 7]
def baseStart_327074 : Nat := 118140960795 + 327074 * 2 ^ 59
def prefixEnd_327074 : Nat := 4983230072969 + 3 ^ 40 * 327074 * 2
def baseEnd_327074 : Nat := 16587276206297141251439

theorem tailTrace_327074 : CollatzResearch.WordTrace tailWord_327074 prefixEnd_327074 16587276206297141251439 := by
  unfold tailWord_327074
  simp only [CollatzResearch.WordTrace]
  refine ⟨2982342204268558159271069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7952912544716155091389517 2982342204268558159271069)
  ·
    refine ⟨1118378326600709309726651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2982342204268558159271069 1118378326600709309726651)
    ·
      refine ⟨1677567489901063964589977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1118378326600709309726651 1677567489901063964589977)
      ·
        refine ⟨1258175617425797973442483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1677567489901063964589977 1258175617425797973442483)
        ·
          refine ⟨1887263426138696960163725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1258175617425797973442483 1887263426138696960163725)
          ·
            refine ⟨707723784802011360061397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1887263426138696960163725 707723784802011360061397)
            ·
              refine ⟨16587276206297141251439, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 707723784802011360061397 16587276206297141251439)
              ·
                rfl

theorem cell20_327074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 3, 7].length) (baseStart_327074 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_327074 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_327074 prefixEnd_327074 := by exact prefixLift 327074
  have htrace : WordTrace (prefixWord ++ tailWord_327074) baseStart_327074 baseEnd_327074 := by
    simpa [prefixWord, tailWord_327074, baseEnd_327074] using wordTrace_append hprefix tailTrace_327074
  have hstable : (prefixWord ++ tailWord_327074).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_327074).length < 2 ^ (prefixWord ++ tailWord_327074).sum := by decide
  have hdescent : baseEnd_327074 < baseStart_327074 := by decide
  rcases family_descends (prefixWord ++ tailWord_327074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_327095 : List Nat := [1, 1, 3, 1, 3, 2, 2, 7]
def baseStart_327095 : Nat := 118140960795 + 327095 * 2 ^ 59
def prefixEnd_327095 : Nat := 4983230072969 + 3 ^ 40 * 327095 * 2
def baseEnd_327095 : Nat := 49765023609630510520955

theorem tailTrace_327095 : CollatzResearch.WordTrace tailWord_327095 prefixEnd_327095 49765023609630510520955 := by
  unfold tailWord_327095
  simp only [CollatzResearch.WordTrace]
  refine ⟨11930134749998153223598739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7953423166665435482399159 11930134749998153223598739)
  ·
    refine ⟨17895202124997229835398109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11930134749998153223598739 17895202124997229835398109)
    ·
      refine ⟨6710700796873961188274291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17895202124997229835398109 6710700796873961188274291)
      ·
        refine ⟨10066051195310941782411437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6710700796873961188274291 10066051195310941782411437)
        ·
          refine ⟨3774769198241603168404289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10066051195310941782411437 3774769198241603168404289)
          ·
            refine ⟨2831076898681202376303217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3774769198241603168404289 2831076898681202376303217)
            ·
              refine ⟨2123307674010901782227413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2831076898681202376303217 2123307674010901782227413)
              ·
                refine ⟨49765023609630510520955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2123307674010901782227413 49765023609630510520955)
                ·
                  rfl

theorem cell20_327095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 2, 7].length) (baseStart_327095 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_327095 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_327095 prefixEnd_327095 := by exact prefixLift 327095
  have htrace : WordTrace (prefixWord ++ tailWord_327095) baseStart_327095 baseEnd_327095 := by
    simpa [prefixWord, tailWord_327095, baseEnd_327095] using wordTrace_append hprefix tailTrace_327095
  have hstable : (prefixWord ++ tailWord_327095).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_327095).length < 2 ^ (prefixWord ++ tailWord_327095).sum := by decide
  have hdescent : baseEnd_327095 < baseStart_327095 := by decide
  rcases family_descends (prefixWord ++ tailWord_327095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_327108 : List Nat := [2, 3, 3, 2, 1, 3, 2, 4]
def baseStart_327108 : Nat := 118140960795 + 327108 * 2 ^ 59
def prefixEnd_327108 : Nat := 4983230072969 + 3 ^ 40 * 327108 * 2
def baseEnd_327108 : Nat := 49767001461040421376493

theorem tailTrace_327108 : CollatzResearch.WordTrace tailWord_327108 prefixEnd_327108 49767001461040421376493 := by
  unfold tailWord_327108
  simp only [CollatzResearch.WordTrace]
  refine ⟨5965304449475528221910989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7953739265967370962547985 5965304449475528221910989)
  ·
    refine ⟨2236989168553323083216621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5965304449475528221910989 2236989168553323083216621)
    ·
      refine ⟨838870938207496156206233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2236989168553323083216621 838870938207496156206233)
      ·
        refine ⟨629153203655622117154675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 838870938207496156206233 629153203655622117154675)
        ·
          refine ⟨943729805483433175732013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 629153203655622117154675 943729805483433175732013)
          ·
            refine ⟨353898677056287440899505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 943729805483433175732013 353898677056287440899505)
            ·
              refine ⟨265424007792215580674629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 353898677056287440899505 265424007792215580674629)
              ·
                refine ⟨49767001461040421376493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 265424007792215580674629 49767001461040421376493)
                ·
                  rfl

theorem cell20_327108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 3, 2, 4].length) (baseStart_327108 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_327108 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_327108 prefixEnd_327108 := by exact prefixLift 327108
  have htrace : WordTrace (prefixWord ++ tailWord_327108) baseStart_327108 baseEnd_327108 := by
    simpa [prefixWord, tailWord_327108, baseEnd_327108] using wordTrace_append hprefix tailTrace_327108
  have hstable : (prefixWord ++ tailWord_327108).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_327108).length < 2 ^ (prefixWord ++ tailWord_327108).sum := by decide
  have hdescent : baseEnd_327108 < baseStart_327108 := by decide
  rcases family_descends (prefixWord ++ tailWord_327108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_327139 : List Nat := [1, 1, 1, 6, 2, 2, 3, 2, 2]
def baseStart_327139 : Nat := 118140960795 + 327139 * 2 ^ 59
def prefixEnd_327139 : Nat := 4983230072969 + 3 ^ 40 * 327139 * 2
def baseEnd_327139 : Nat := 149315153627822934096019

theorem tailTrace_327139 : CollatzResearch.WordTrace tailWord_327139 prefixEnd_327139 149315153627822934096019 := by
  unfold tailWord_327139
  simp only [CollatzResearch.WordTrace]
  refine ⟨11931739561838748738200471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7954493041225832492133647 11931739561838748738200471)
  ·
    refine ⟨17897609342758123107300707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11931739561838748738200471 17897609342758123107300707)
    ·
      refine ⟨26846414014137184660951061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17897609342758123107300707 26846414014137184660951061)
      ·
        refine ⟨1258425656912680530982081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 26846414014137184660951061 1258425656912680530982081)
        ·
          refine ⟨943819242684510398236561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1258425656912680530982081 943819242684510398236561)
          ·
            refine ⟨707864432013382798677421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 943819242684510398236561 707864432013382798677421)
            ·
              refine ⟨265449162005018549504033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 707864432013382798677421 265449162005018549504033)
              ·
                refine ⟨199086871503763912128025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 265449162005018549504033 199086871503763912128025)
                ·
                  refine ⟨149315153627822934096019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 199086871503763912128025 149315153627822934096019)
                  ·
                    rfl

theorem cell20_327139_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 2, 3, 2, 2].length) (baseStart_327139 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_327139 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_327139 prefixEnd_327139 := by exact prefixLift 327139
  have htrace : WordTrace (prefixWord ++ tailWord_327139) baseStart_327139 baseEnd_327139 := by
    simpa [prefixWord, tailWord_327139, baseEnd_327139] using wordTrace_append hprefix tailTrace_327139
  have hstable : (prefixWord ++ tailWord_327139).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_327139).length < 2 ^ (prefixWord ++ tailWord_327139).sum := by decide
  have hdescent : baseEnd_327139 < baseStart_327139 := by decide
  rcases family_descends (prefixWord ++ tailWord_327139) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_327143 : List Nat := [1, 1, 5, 2, 1, 2, 3, 1, 4]
def baseStart_327143 : Nat := 118140960795 + 327143 * 2 ^ 59
def prefixEnd_327143 : Nat := 4983230072969 + 3 ^ 40 * 327143 * 2
def baseEnd_327143 : Nat := 149316979336816697962669

theorem tailTrace_327143 : CollatzResearch.WordTrace tailWord_327143 prefixEnd_327143 149316979336816697962669 := by
  unfold tailWord_327143
  simp only [CollatzResearch.WordTrace]
  refine ⟨11931885453824257421346083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7954590302549504947564055 11931885453824257421346083)
  ·
    refine ⟨17897828180736386132019125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11931885453824257421346083 17897828180736386132019125)
    ·
      refine ⟨1677921391944036199876793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 17897828180736386132019125 1677921391944036199876793)
      ·
        refine ⟨1258441043958027149907595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1677921391944036199876793 1258441043958027149907595)
        ·
          refine ⟨1887661565937040724861393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1258441043958027149907595 1887661565937040724861393)
          ·
            refine ⟨1415746174452780543646045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1887661565937040724861393 1415746174452780543646045)
            ·
              refine ⟨530904815419792703867267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1415746174452780543646045 530904815419792703867267)
              ·
                refine ⟨796357223129689055800901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 530904815419792703867267 796357223129689055800901)
                ·
                  refine ⟨149316979336816697962669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 796357223129689055800901 149316979336816697962669)
                  ·
                    rfl

theorem cell20_327143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 3, 1, 4].length) (baseStart_327143 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_327143 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_327143 prefixEnd_327143 := by exact prefixLift 327143
  have htrace : WordTrace (prefixWord ++ tailWord_327143) baseStart_327143 baseEnd_327143 := by
    simpa [prefixWord, tailWord_327143, baseEnd_327143] using wordTrace_append hprefix tailTrace_327143
  have hstable : (prefixWord ++ tailWord_327143).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_327143).length < 2 ^ (prefixWord ++ tailWord_327143).sum := by decide
  have hdescent : baseEnd_327143 < baseStart_327143 := by decide
  rcases family_descends (prefixWord ++ tailWord_327143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_327149 : List Nat := [1, 5, 1, 3, 3, 1, 2, 1, 3]
def baseStart_327149 : Nat := 118140960795 + 327149 * 2 ^ 59
def prefixEnd_327149 : Nat := 4983230072969 + 3 ^ 40 * 327149 * 2
def baseEnd_327149 : Nat := 149319717900307343762645

theorem tailTrace_327149 : CollatzResearch.WordTrace tailWord_327149 prefixEnd_327149 149319717900307343762645 := by
  unfold tailWord_327149
  simp only [CollatzResearch.WordTrace]
  refine ⟨11932104291802520446064501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7954736194535013630709667 11932104291802520446064501)
  ·
    refine ⟨1118634777356486291818547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 11932104291802520446064501 1118634777356486291818547)
    ·
      refine ⟨1677952166034729437727821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1118634777356486291818547 1677952166034729437727821)
      ·
        refine ⟨629232062263023539147933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1677952166034729437727821 629232062263023539147933)
        ·
          refine ⟨235962023348633827180475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 629232062263023539147933 235962023348633827180475)
          ·
            refine ⟨353943035022950740770713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 235962023348633827180475 353943035022950740770713)
            ·
              refine ⟨265457276267213055578035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 353943035022950740770713 265457276267213055578035)
              ·
                refine ⟨398185914400819583367053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 265457276267213055578035 398185914400819583367053)
                ·
                  refine ⟨149319717900307343762645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 398185914400819583367053 149319717900307343762645)
                  ·
                    rfl

theorem cell20_327149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 3, 1, 2, 1, 3].length) (baseStart_327149 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_327149 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_327149 prefixEnd_327149 := by exact prefixLift 327149
  have htrace : WordTrace (prefixWord ++ tailWord_327149) baseStart_327149 baseEnd_327149 := by
    simpa [prefixWord, tailWord_327149, baseEnd_327149] using wordTrace_append hprefix tailTrace_327149
  have hstable : (prefixWord ++ tailWord_327149).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_327149).length < 2 ^ (prefixWord ++ tailWord_327149).sum := by decide
  have hdescent : baseEnd_327149 < baseStart_327149 := by decide
  rcases family_descends (prefixWord ++ tailWord_327149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_327150 : List Nat := [4, 1, 2, 1, 2, 1, 4, 5]
def baseStart_327150 : Nat := 118140960795 + 327150 * 2 ^ 59
def prefixEnd_327150 : Nat := 4983230072969 + 3 ^ 40 * 327150 * 2
def baseEnd_327150 : Nat := 49773391442518594909769

theorem tailTrace_327150 : CollatzResearch.WordTrace tailWord_327150 prefixEnd_327150 49773391442518594909769 := by
  unfold tailWord_327150
  simp only [CollatzResearch.WordTrace]
  refine ⟨1491517595599862202106363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 7954760509865931744567269 1491517595599862202106363)
  ·
    refine ⟨2237276393399793303159545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1491517595599862202106363 2237276393399793303159545)
    ·
      refine ⟨1677957295049844977369659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2237276393399793303159545 1677957295049844977369659)
      ·
        refine ⟨2516935942574767466054489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1677957295049844977369659 2516935942574767466054489)
        ·
          refine ⟨1887701956931075599540867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2516935942574767466054489 1887701956931075599540867)
          ·
            refine ⟨2831552935396613399311301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1887701956931075599540867 2831552935396613399311301)
            ·
              refine ⟨530916175386865012370869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2831552935396613399311301 530916175386865012370869)
              ·
                refine ⟨49773391442518594909769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 530916175386865012370869 49773391442518594909769)
                ·
                  rfl

theorem cell20_327150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 4, 5].length) (baseStart_327150 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_327150 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_327150 prefixEnd_327150 := by exact prefixLift 327150
  have htrace : WordTrace (prefixWord ++ tailWord_327150) baseStart_327150 baseEnd_327150 := by
    simpa [prefixWord, tailWord_327150, baseEnd_327150] using wordTrace_append hprefix tailTrace_327150
  have hstable : (prefixWord ++ tailWord_327150).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_327150).length < 2 ^ (prefixWord ++ tailWord_327150).sum := by decide
  have hdescent : baseEnd_327150 < baseStart_327150 := by decide
  rcases family_descends (prefixWord ++ tailWord_327150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_327153 : List Nat := [1, 2, 2, 2, 3, 4, 2, 1, 3]
def baseStart_327153 : Nat := 118140960795 + 327153 * 2 ^ 59
def prefixEnd_327153 : Nat := 4983230072969 + 3 ^ 40 * 327153 * 2
def baseEnd_327153 : Nat := 149321543609301107629295

theorem tailTrace_327153 : CollatzResearch.WordTrace tailWord_327153 prefixEnd_327153 149321543609301107629295 := by
  unfold tailWord_327153
  simp only [CollatzResearch.WordTrace]
  refine ⟨11932250183788029129210113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7954833455858686086140075 11932250183788029129210113)
  ·
    refine ⟨8949187637841021846907585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11932250183788029129210113 8949187637841021846907585)
    ·
      refine ⟨6711890728380766385180689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8949187637841021846907585 6711890728380766385180689)
      ·
        refine ⟨5033918046285574788885517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6711890728380766385180689 5033918046285574788885517)
        ·
          refine ⟨1887719267357090545832069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5033918046285574788885517 1887719267357090545832069)
          ·
            refine ⟨353947362629454477343513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1887719267357090545832069 353947362629454477343513)
            ·
              refine ⟨265460521972090858007635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 353947362629454477343513 265460521972090858007635)
              ·
                refine ⟨398190782958136287011453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 265460521972090858007635 398190782958136287011453)
                ·
                  refine ⟨149321543609301107629295, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 398190782958136287011453 149321543609301107629295)
                  ·
                    rfl

theorem cell20_327153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 4, 2, 1, 3].length) (baseStart_327153 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_327153 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_327153 prefixEnd_327153 := by exact prefixLift 327153
  have htrace : WordTrace (prefixWord ++ tailWord_327153) baseStart_327153 baseEnd_327153 := by
    simpa [prefixWord, tailWord_327153, baseEnd_327153] using wordTrace_append hprefix tailTrace_327153
  have hstable : (prefixWord ++ tailWord_327153).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_327153).length < 2 ^ (prefixWord ++ tailWord_327153).sum := by decide
  have hdescent : baseEnd_327153 < baseStart_327153 := by decide
  rcases family_descends (prefixWord ++ tailWord_327153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_327164 : List Nat := [2, 2, 2, 1, 2, 1, 2, 4, 4]
def baseStart_327164 : Nat := 118140960795 + 327164 * 2 ^ 59
def prefixEnd_327164 : Nat := 4983230072969 + 3 ^ 40 * 327164 * 2
def baseEnd_327164 : Nat := 149326564309033958262583

theorem tailTrace_327164 : CollatzResearch.WordTrace tailWord_327164 prefixEnd_327164 149326564309033958262583 := by
  unfold tailWord_327164
  simp only [CollatzResearch.WordTrace]
  refine ⟨5966325693374089003930273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7955100924498785338573697 5966325693374089003930273)
  ·
    refine ⟨4474744270030566752947705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5966325693374089003930273 4474744270030566752947705)
    ·
      refine ⟨3356058202522925064710779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4474744270030566752947705 3356058202522925064710779)
      ·
        refine ⟨5034087303784387597066169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3356058202522925064710779 5034087303784387597066169)
        ·
          refine ⟨3775565477838290697799627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5034087303784387597066169 3775565477838290697799627)
          ·
            refine ⟨5663348216757436046699441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3775565477838290697799627 5663348216757436046699441)
            ·
              refine ⟨4247511162568077035024581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5663348216757436046699441 4247511162568077035024581)
              ·
                refine ⟨796408342981514444067109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4247511162568077035024581 796408342981514444067109)
                ·
                  refine ⟨149326564309033958262583, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 796408342981514444067109 149326564309033958262583)
                  ·
                    rfl

theorem cell20_327164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 2, 4, 4].length) (baseStart_327164 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_327164 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_327164 prefixEnd_327164 := by exact prefixLift 327164
  have htrace : WordTrace (prefixWord ++ tailWord_327164) baseStart_327164 baseEnd_327164 := by
    simpa [prefixWord, tailWord_327164, baseEnd_327164] using wordTrace_append hprefix tailTrace_327164
  have hstable : (prefixWord ++ tailWord_327164).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_327164).length < 2 ^ (prefixWord ++ tailWord_327164).sum := by decide
  have hdescent : baseEnd_327164 < baseStart_327164 := by decide
  rcases family_descends (prefixWord ++ tailWord_327164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_327188 : List Nat := [2, 4, 3, 1, 10]
def baseStart_327188 : Nat := 118140960795 + 327188 * 2 ^ 59
def prefixEnd_327188 : Nat := 4983230072969 + 3 ^ 40 * 327188 * 2
def baseEnd_327188 : Nat := 1843673068678969647685

theorem tailTrace_327188 : CollatzResearch.WordTrace tailWord_327188 prefixEnd_327188 1843673068678969647685 := by
  unfold tailWord_327188
  simp only [CollatzResearch.WordTrace]
  refine ⟨5966763369330615053367109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7955684492440820071156145 5966763369330615053367109)
  ·
    refine ⟨1118768131749490322506333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5966763369330615053367109 1118768131749490322506333)
    ·
      refine ⟨419538049406058870939875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1118768131749490322506333 419538049406058870939875)
      ·
        refine ⟨629307074109088306409813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 419538049406058870939875 629307074109088306409813)
        ·
          refine ⟨1843673068678969647685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 10 629307074109088306409813 1843673068678969647685)
          ·
            rfl

theorem cell20_327188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 10].length) (baseStart_327188 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_327188 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_327188 prefixEnd_327188 := by exact prefixLift 327188
  have htrace : WordTrace (prefixWord ++ tailWord_327188) baseStart_327188 baseEnd_327188 := by
    simpa [prefixWord, tailWord_327188, baseEnd_327188] using wordTrace_append hprefix tailTrace_327188
  have hstable : (prefixWord ++ tailWord_327188).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_327188).length < 2 ^ (prefixWord ++ tailWord_327188).sum := by decide
  have hdescent : baseEnd_327188 < baseStart_327188 := by decide
  rcases family_descends (prefixWord ++ tailWord_327188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_327216 : List Nat := [2, 1, 1, 1, 2, 3, 1, 2, 7]
def baseStart_327216 : Nat := 118140960795 + 327216 * 2 ^ 59
def prefixEnd_327216 : Nat := 4983230072969 + 3 ^ 40 * 327216 * 2
def baseEnd_327216 : Nat := 149350298525952888529037

theorem tailTrace_327216 : CollatzResearch.WordTrace tailWord_327216 prefixEnd_327216 149350298525952888529037 := by
  unfold tailWord_327216
  simp only [CollatzResearch.WordTrace]
  refine ⟨5967273991279895444376751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7956365321706527259169001 5967273991279895444376751)
  ·
    refine ⟨8950910986919843166565127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5967273991279895444376751 8950910986919843166565127)
    ·
      refine ⟨13426366480379764749847691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8950910986919843166565127 13426366480379764749847691)
      ·
        refine ⟨20139549720569647124771537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13426366480379764749847691 20139549720569647124771537)
        ·
          refine ⟨15104662290427235343578653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20139549720569647124771537 15104662290427235343578653)
          ·
            refine ⟨5664248358910213253841995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15104662290427235343578653 5664248358910213253841995)
            ·
              refine ⟨8496372538365319880762993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5664248358910213253841995 8496372538365319880762993)
              ·
                refine ⟨6372279403773989910572245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8496372538365319880762993 6372279403773989910572245)
                ·
                  refine ⟨149350298525952888529037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6372279403773989910572245 149350298525952888529037)
                  ·
                    rfl

theorem cell20_327216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 1, 2, 7].length) (baseStart_327216 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_327216 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_327216 prefixEnd_327216 := by exact prefixLift 327216
  have htrace : WordTrace (prefixWord ++ tailWord_327216) baseStart_327216 baseEnd_327216 := by
    simpa [prefixWord, tailWord_327216, baseEnd_327216] using wordTrace_append hprefix tailTrace_327216
  have hstable : (prefixWord ++ tailWord_327216).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_327216).length < 2 ^ (prefixWord ++ tailWord_327216).sum := by decide
  have hdescent : baseEnd_327216 < baseStart_327216 := by decide
  rcases family_descends (prefixWord ++ tailWord_327216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_327222 : List Nat := [5, 1, 2, 1, 3, 1, 3, 4]
def baseStart_327222 : Nat := 118140960795 + 327222 * 2 ^ 59
def prefixEnd_327222 : Nat := 4983230072969 + 3 ^ 40 * 327222 * 2
def baseEnd_327222 : Nat := 49784345696481178109671

theorem tailTrace_327222 : CollatzResearch.WordTrace tailWord_327222 prefixEnd_327222 49784345696481178109671 := by
  unfold tailWord_327222
  simp only [CollatzResearch.WordTrace]
  refine ⟨745922926283628369591995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 7956511213692035942314613 745922926283628369591995)
  ·
    refine ⟨1118884389425442554387993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 745922926283628369591995 1118884389425442554387993)
    ·
      refine ⟨839163292069081915790995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1118884389425442554387993 839163292069081915790995)
      ·
        refine ⟨1258744938103622873686493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 839163292069081915790995 1258744938103622873686493)
        ·
          refine ⟨472029351788858577632435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1258744938103622873686493 472029351788858577632435)
          ·
            refine ⟨708044027683287866448653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 472029351788858577632435 708044027683287866448653)
            ·
              refine ⟨265516510381232949918245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 708044027683287866448653 265516510381232949918245)
              ·
                refine ⟨49784345696481178109671, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 265516510381232949918245 49784345696481178109671)
                ·
                  rfl

theorem cell20_327222_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 3, 1, 3, 4].length) (baseStart_327222 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_327222 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_327222 prefixEnd_327222 := by exact prefixLift 327222
  have htrace : WordTrace (prefixWord ++ tailWord_327222) baseStart_327222 baseEnd_327222 := by
    simpa [prefixWord, tailWord_327222, baseEnd_327222] using wordTrace_append hprefix tailTrace_327222
  have hstable : (prefixWord ++ tailWord_327222).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_327222).length < 2 ^ (prefixWord ++ tailWord_327222).sum := by decide
  have hdescent : baseEnd_327222 < baseStart_327222 := by decide
  rcases family_descends (prefixWord ++ tailWord_327222) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_327226 : List Nat := [3, 1, 1, 1, 3, 2, 5, 4]
def baseStart_327226 : Nat := 118140960795 + 327226 * 2 ^ 59
def prefixEnd_327226 : Nat := 4983230072969 + 3 ^ 40 * 327226 * 2
def baseEnd_327226 : Nat := 49784954266145766065221

theorem tailTrace_327226 : CollatzResearch.WordTrace tailWord_327226 prefixEnd_327226 49784954266145766065221 := by
  unfold tailWord_327226
  simp only [CollatzResearch.WordTrace]
  refine ⟨2983728178130890649154383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7956608475015708397745021 2983728178130890649154383)
  ·
    refine ⟨4475592267196335973731575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2983728178130890649154383 4475592267196335973731575)
    ·
      refine ⟨6713388400794503960597363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4475592267196335973731575 6713388400794503960597363)
      ·
        refine ⟨10070082601191755940896045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6713388400794503960597363 10070082601191755940896045)
        ·
          refine ⟨3776280975446908477836017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10070082601191755940896045 3776280975446908477836017)
          ·
            refine ⟨2832210731585181358377013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3776280975446908477836017 2832210731585181358377013)
            ·
              refine ⟨265519756086110752347845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 2832210731585181358377013 265519756086110752347845)
              ·
                refine ⟨49784954266145766065221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 265519756086110752347845 49784954266145766065221)
                ·
                  rfl

theorem cell20_327226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 5, 4].length) (baseStart_327226 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_327226 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_327226 prefixEnd_327226 := by exact prefixLift 327226
  have htrace : WordTrace (prefixWord ++ tailWord_327226) baseStart_327226 baseEnd_327226 := by
    simpa [prefixWord, tailWord_327226, baseEnd_327226] using wordTrace_append hprefix tailTrace_327226
  have hstable : (prefixWord ++ tailWord_327226).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_327226).length < 2 ^ (prefixWord ++ tailWord_327226).sum := by decide
  have hdescent : baseEnd_327226 < baseStart_327226 := by decide
  rcases family_descends (prefixWord ++ tailWord_327226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_327233 : List Nat := [1, 2, 5, 1, 1, 1, 2, 2, 5]
def baseStart_327233 : Nat := 118140960795 + 327233 * 2 ^ 59
def prefixEnd_327233 : Nat := 4983230072969 + 3 ^ 40 * 327233 * 2
def baseEnd_327233 : Nat := 149358057789176384962301

theorem tailTrace_327233 : CollatzResearch.WordTrace tailWord_327233 prefixEnd_327233 149358057789176384962301 := by
  unfold tailWord_327233
  simp only [CollatzResearch.WordTrace]
  refine ⟨11935168023498202792122353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7956778682332135194748235 11935168023498202792122353)
  ·
    refine ⟨8951376017623652094091765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11935168023498202792122353 8951376017623652094091765)
    ·
      refine ⟨839191501652217383821103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 8951376017623652094091765 839191501652217383821103)
      ·
        refine ⟨1258787252478326075731655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 839191501652217383821103 1258787252478326075731655)
        ·
          refine ⟨1888180878717489113597483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1258787252478326075731655 1888180878717489113597483)
          ·
            refine ⟨2832271318076233670396225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1888180878717489113597483 2832271318076233670396225)
            ·
              refine ⟨2124203488557175252797169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2832271318076233670396225 2124203488557175252797169)
              ·
                refine ⟨1593152616417881439597877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2124203488557175252797169 1593152616417881439597877)
                ·
                  refine ⟨149358057789176384962301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1593152616417881439597877 149358057789176384962301)
                  ·
                    rfl

theorem cell20_327233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 2, 2, 5].length) (baseStart_327233 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_327233 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_327233 prefixEnd_327233 := by exact prefixLift 327233
  have htrace : WordTrace (prefixWord ++ tailWord_327233) baseStart_327233 baseEnd_327233 := by
    simpa [prefixWord, tailWord_327233, baseEnd_327233] using wordTrace_append hprefix tailTrace_327233
  have hstable : (prefixWord ++ tailWord_327233).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_327233).length < 2 ^ (prefixWord ++ tailWord_327233).sum := by decide
  have hdescent : baseEnd_327233 < baseStart_327233 := by decide
  rcases family_descends (prefixWord ++ tailWord_327233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_327250 : List Nat := [3, 2, 2, 1, 2, 2, 3, 2, 3]
def baseStart_327250 : Nat := 118140960795 + 327250 * 2 ^ 59
def prefixEnd_327250 : Nat := 4983230072969 + 3 ^ 40 * 327250 * 2
def baseEnd_327250 : Nat := 149365817052399881395565

theorem tailTrace_327250 : CollatzResearch.WordTrace tailWord_327250 prefixEnd_327250 149365817052399881395565 := by
  unfold tailWord_327250
  simp only [CollatzResearch.WordTrace]
  refine ⟨2983947016109153673872801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7957192042957743130327469 2983947016109153673872801)
  ·
    refine ⟨2237960262081865255404601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2983947016109153673872801 2237960262081865255404601)
    ·
      refine ⟨1678470196561398941553451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2237960262081865255404601 1678470196561398941553451)
      ·
        refine ⟨2517705294842098412330177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1678470196561398941553451 2517705294842098412330177)
        ·
          refine ⟨1888278971131573809247633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2517705294842098412330177 1888278971131573809247633)
          ·
            refine ⟨1416209228348680356935725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1888278971131573809247633 1416209228348680356935725)
            ·
              refine ⟨531078460630755133850897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1416209228348680356935725 531078460630755133850897)
              ·
                refine ⟨398308845473066350388173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 531078460630755133850897 398308845473066350388173)
                ·
                  refine ⟨149365817052399881395565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 398308845473066350388173 149365817052399881395565)
                  ·
                    rfl

theorem cell20_327250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 3, 2, 3].length) (baseStart_327250 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_327250 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_327250 prefixEnd_327250 := by exact prefixLift 327250
  have htrace : WordTrace (prefixWord ++ tailWord_327250) baseStart_327250 baseEnd_327250 := by
    simpa [prefixWord, tailWord_327250, baseEnd_327250] using wordTrace_append hprefix tailTrace_327250
  have hstable : (prefixWord ++ tailWord_327250).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_327250).length < 2 ^ (prefixWord ++ tailWord_327250).sum := by decide
  have hdescent : baseEnd_327250 < baseStart_327250 := by decide
  rcases family_descends (prefixWord ++ tailWord_327250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_327271 : List Nat := [1, 1, 5, 1, 1, 1, 2, 5, 3]
def baseStart_327271 : Nat := 118140960795 + 327271 * 2 ^ 59
def prefixEnd_327271 : Nat := 4983230072969 + 3 ^ 40 * 327271 * 2
def baseEnd_327271 : Nat := 149375402024617141695479

theorem tailTrace_327271 : CollatzResearch.WordTrace tailWord_327271 prefixEnd_327271 149375402024617141695479 := by
  unfold tailWord_327271
  simp only [CollatzResearch.WordTrace]
  refine ⟨11936553997360535282005667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7957702664907023521337111 11936553997360535282005667)
  ·
    refine ⟨17904830996040802923008501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11936553997360535282005667 17904830996040802923008501)
    ·
      refine ⟨1678577905878825274032047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 17904830996040802923008501 1678577905878825274032047)
      ·
        refine ⟨2517866858818237911048071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1678577905878825274032047 2517866858818237911048071)
        ·
          refine ⟨3776800288227356866572107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2517866858818237911048071 3776800288227356866572107)
          ·
            refine ⟨5665200432341035299858161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3776800288227356866572107 5665200432341035299858161)
            ·
              refine ⟨4248900324255776474893621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5665200432341035299858161 4248900324255776474893621)
              ·
                refine ⟨398334405398979044521277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4248900324255776474893621 398334405398979044521277)
                ·
                  refine ⟨149375402024617141695479, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 398334405398979044521277 149375402024617141695479)
                  ·
                    rfl

theorem cell20_327271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 2, 5, 3].length) (baseStart_327271 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_327271 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_327271 prefixEnd_327271 := by exact prefixLift 327271
  have htrace : WordTrace (prefixWord ++ tailWord_327271) baseStart_327271 baseEnd_327271 := by
    simpa [prefixWord, tailWord_327271, baseEnd_327271] using wordTrace_append hprefix tailTrace_327271
  have hstable : (prefixWord ++ tailWord_327271).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_327271).length < 2 ^ (prefixWord ++ tailWord_327271).sum := by decide
  have hdescent : baseEnd_327271 < baseStart_327271 := by decide
  rcases family_descends (prefixWord ++ tailWord_327271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_327361 : List Nat := [1, 2, 6, 11]
def baseStart_327361 : Nat := 118140960795 + 327361 * 2 ^ 59
def prefixEnd_327361 : Nat := 4983230072969 + 3 ^ 40 * 327361 * 2
def baseEnd_327361 : Nat := 614882635707723574877

theorem tailTrace_327361 : CollatzResearch.WordTrace tailWord_327361 prefixEnd_327361 614882635707723574877 := by
  unfold tailWord_327361
  simp only [CollatzResearch.WordTrace]
  refine ⟨11939836567034480652781937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7959891044689653768521291 11939836567034480652781937)
  ·
    refine ⟨8954877425275860489586453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11939836567034480652781937 8954877425275860489586453)
    ·
      refine ⟨419759879309805960449365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 8954877425275860489586453 419759879309805960449365)
      ·
        refine ⟨614882635707723574877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 11 419759879309805960449365 614882635707723574877)
        ·
          rfl

theorem cell20_327361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 11].length) (baseStart_327361 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_327361 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_327361 prefixEnd_327361 := by exact prefixLift 327361
  have htrace : WordTrace (prefixWord ++ tailWord_327361) baseStart_327361 baseEnd_327361 := by
    simpa [prefixWord, tailWord_327361, baseEnd_327361] using wordTrace_append hprefix tailTrace_327361
  have hstable : (prefixWord ++ tailWord_327361).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_327361).length < 2 ^ (prefixWord ++ tailWord_327361).sum := by decide
  have hdescent : baseEnd_327361 < baseStart_327361 := by decide
  rcases family_descends (prefixWord ++ tailWord_327361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_327364 : List Nat := [2, 3, 3, 1, 1, 1, 4, 2, 3]
def baseStart_327364 : Nat := 118140960795 + 327364 * 2 ^ 59
def prefixEnd_327364 : Nat := 4983230072969 + 3 ^ 40 * 327364 * 2
def baseEnd_327364 : Nat := 149417849758722151595099

theorem tailTrace_327364 : CollatzResearch.WordTrace tailWord_327364 prefixEnd_327364 149417849758722151595099 := by
  unfold tailWord_327364
  simp only [CollatzResearch.WordTrace]
  refine ⟨5969972993011806082570573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7959963990682408110094097 5969972993011806082570573)
  ·
    refine ⟨2238739872379427280963965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5969972993011806082570573 2238739872379427280963965)
    ·
      refine ⟨839527452142285230361487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2238739872379427280963965 839527452142285230361487)
      ·
        refine ⟨1259291178213427845542231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 839527452142285230361487 1259291178213427845542231)
        ·
          refine ⟨1888936767320141768313347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1259291178213427845542231 1888936767320141768313347)
          ·
            refine ⟨2833405150980212652470021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1888936767320141768313347 2833405150980212652470021)
            ·
              refine ⟨531263465808789872338129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2833405150980212652470021 531263465808789872338129)
              ·
                refine ⟨398447599356592404253597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 531263465808789872338129 398447599356592404253597)
                ·
                  refine ⟨149417849758722151595099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 398447599356592404253597 149417849758722151595099)
                  ·
                    rfl

theorem cell20_327364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 4, 2, 3].length) (baseStart_327364 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_327364 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_327364 prefixEnd_327364 := by exact prefixLift 327364
  have htrace : WordTrace (prefixWord ++ tailWord_327364) baseStart_327364 baseEnd_327364 := by
    simpa [prefixWord, tailWord_327364, baseEnd_327364] using wordTrace_append hprefix tailTrace_327364
  have hstable : (prefixWord ++ tailWord_327364).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_327364).length < 2 ^ (prefixWord ++ tailWord_327364).sum := by decide
  have hdescent : baseEnd_327364 < baseStart_327364 := by decide
  rcases family_descends (prefixWord ++ tailWord_327364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_327375 : List Nat := [1, 1, 2, 1, 1, 3, 1, 2, 8]
def baseStart_327375 : Nat := 118140960795 + 327375 * 2 ^ 59
def prefixEnd_327375 : Nat := 4983230072969 + 3 ^ 40 * 327375 * 2
def baseEnd_327375 : Nat := 149422870458455002228387

theorem tailTrace_327375 : CollatzResearch.WordTrace tailWord_327375 prefixEnd_327375 149422870458455002228387 := by
  unfold tailWord_327375
  simp only [CollatzResearch.WordTrace]
  refine ⟨11940347188983761043791579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7960231459322507362527719 11940347188983761043791579)
  ·
    refine ⟨17910520783475641565687369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11940347188983761043791579 17910520783475641565687369)
    ·
      refine ⟨13432890587606731174265527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17910520783475641565687369 13432890587606731174265527)
      ·
        refine ⟨20149335881410096761398291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13432890587606731174265527 20149335881410096761398291)
        ·
          refine ⟨30224003822115145142097437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20149335881410096761398291 30224003822115145142097437)
          ·
            refine ⟨11334001433293179428286539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30224003822115145142097437 11334001433293179428286539)
            ·
              refine ⟨17001002149939769142429809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11334001433293179428286539 17001002149939769142429809)
              ·
                refine ⟨12750751612454826856822357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17001002149939769142429809 12750751612454826856822357)
                ·
                  refine ⟨149422870458455002228387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 12750751612454826856822357 149422870458455002228387)
                  ·
                    rfl

theorem cell20_327375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 2, 8].length) (baseStart_327375 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_327375 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_327375 prefixEnd_327375 := by exact prefixLift 327375
  have htrace : WordTrace (prefixWord ++ tailWord_327375) baseStart_327375 baseEnd_327375 := by
    simpa [prefixWord, tailWord_327375, baseEnd_327375] using wordTrace_append hprefix tailTrace_327375
  have hstable : (prefixWord ++ tailWord_327375).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_327375).length < 2 ^ (prefixWord ++ tailWord_327375).sum := by decide
  have hdescent : baseEnd_327375 < baseStart_327375 := by decide
  rcases family_descends (prefixWord ++ tailWord_327375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_327378 : List Nat := [3, 2, 2, 2, 2, 1, 3, 5]
def baseStart_327378 : Nat := 118140960795 + 327378 * 2 ^ 59
def prefixEnd_327378 : Nat := 4983230072969 + 3 ^ 40 * 327378 * 2
def baseEnd_327378 : Nat := 49808079913400108376125

theorem tailTrace_327378 : CollatzResearch.WordTrace tailWord_327378 prefixEnd_327378 49808079913400108376125 := by
  unfold tailWord_327378
  simp only [CollatzResearch.WordTrace]
  refine ⟨2985114151993223139037697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7960304405315261704100525 2985114151993223139037697)
  ·
    refine ⟨2238835613994917354278273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2985114151993223139037697 2238835613994917354278273)
    ·
      refine ⟨1679126710496188015708705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2238835613994917354278273 1679126710496188015708705)
      ·
        refine ⟨1259345032872141011781529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1679126710496188015708705 1259345032872141011781529)
        ·
          refine ⟨944508774654105758836147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1259345032872141011781529 944508774654105758836147)
          ·
            refine ⟨1416763161981158638254221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 944508774654105758836147 1416763161981158638254221)
            ·
              refine ⟨531286185742934489345333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1416763161981158638254221 531286185742934489345333)
              ·
                refine ⟨49808079913400108376125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 531286185742934489345333 49808079913400108376125)
                ·
                  rfl

theorem cell20_327378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 3, 5].length) (baseStart_327378 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_327378 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_327378 prefixEnd_327378 := by exact prefixLift 327378
  have htrace : WordTrace (prefixWord ++ tailWord_327378) baseStart_327378 baseEnd_327378 := by
    simpa [prefixWord, tailWord_327378, baseEnd_327378] using wordTrace_append hprefix tailTrace_327378
  have hstable : (prefixWord ++ tailWord_327378).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_327378).length < 2 ^ (prefixWord ++ tailWord_327378).sum := by decide
  have hdescent : baseEnd_327378 < baseStart_327378 := by decide
  rcases family_descends (prefixWord ++ tailWord_327378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_327385 : List Nat := [1, 2, 1, 2, 3, 3, 2, 3, 3]
def baseStart_327385 : Nat := 118140960795 + 327385 * 2 ^ 59
def prefixEnd_327385 : Nat := 4983230072969 + 3 ^ 40 * 327385 * 2
def baseEnd_327385 : Nat := 149427434730939411895013

theorem tailTrace_327385 : CollatzResearch.WordTrace tailWord_327385 prefixEnd_327385 149427434730939411895013 := by
  unfold tailWord_327385
  simp only [CollatzResearch.WordTrace]
  refine ⟨11940711918947532751655609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7960474612631688501103739 11940711918947532751655609)
  ·
    refine ⟨8955533939210649563741707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11940711918947532751655609 8955533939210649563741707)
    ·
      refine ⟨13433300908815974345612561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8955533939210649563741707 13433300908815974345612561)
      ·
        refine ⟨10074975681611980759209421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13433300908815974345612561 10074975681611980759209421)
        ·
          refine ⟨3778115880604492784703533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10074975681611980759209421 3778115880604492784703533)
          ·
            refine ⟨1416793455226684794263825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3778115880604492784703533 1416793455226684794263825)
            ·
              refine ⟨1062595091420013595697869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1416793455226684794263825 1062595091420013595697869)
              ·
                refine ⟨398473159282505098386701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1062595091420013595697869 398473159282505098386701)
                ·
                  refine ⟨149427434730939411895013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 398473159282505098386701 149427434730939411895013)
                  ·
                    rfl

theorem cell20_327385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 2, 3, 3].length) (baseStart_327385 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_327385 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_327385 prefixEnd_327385 := by exact prefixLift 327385
  have htrace : WordTrace (prefixWord ++ tailWord_327385) baseStart_327385 baseEnd_327385 := by
    simpa [prefixWord, tailWord_327385, baseEnd_327385] using wordTrace_append hprefix tailTrace_327385
  have hstable : (prefixWord ++ tailWord_327385).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_327385).length < 2 ^ (prefixWord ++ tailWord_327385).sum := by decide
  have hdescent : baseEnd_327385 < baseStart_327385 := by decide
  rcases family_descends (prefixWord ++ tailWord_327385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_327388 : List Nat := [2, 2, 5, 1, 2, 1, 1, 2, 4]
def baseStart_327388 : Nat := 118140960795 + 327388 * 2 ^ 59
def prefixEnd_327388 : Nat := 4983230072969 + 3 ^ 40 * 327388 * 2
def baseEnd_327388 : Nat := 149428804012684734795001

theorem tailTrace_327388 : CollatzResearch.WordTrace tailWord_327388 prefixEnd_327388 149428804012684734795001 := by
  unfold tailWord_327388
  simp only [CollatzResearch.WordTrace]
  refine ⟨5970410668968332132007409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7960547558624442842676545 5970410668968332132007409)
  ·
    refine ⟨4477808001726249099005557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5970410668968332132007409 4477808001726249099005557)
    ·
      refine ⟨419794500161835853031771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 4477808001726249099005557 419794500161835853031771)
      ·
        refine ⟨629691750242753779547657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 419794500161835853031771 629691750242753779547657)
        ·
          refine ⟨472268812682065334660743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 629691750242753779547657 472268812682065334660743)
          ·
            refine ⟨708403219023098001991115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 472268812682065334660743 708403219023098001991115)
            ·
              refine ⟨1062604828534647002986673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 708403219023098001991115 1062604828534647002986673)
              ·
                refine ⟨796953621400985252240005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1062604828534647002986673 796953621400985252240005)
                ·
                  refine ⟨149428804012684734795001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 796953621400985252240005 149428804012684734795001)
                  ·
                    rfl

theorem cell20_327388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 2, 1, 1, 2, 4].length) (baseStart_327388 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_327388 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_327388 prefixEnd_327388 := by exact prefixLift 327388
  have htrace : WordTrace (prefixWord ++ tailWord_327388) baseStart_327388 baseEnd_327388 := by
    simpa [prefixWord, tailWord_327388, baseEnd_327388] using wordTrace_append hprefix tailTrace_327388
  have hstable : (prefixWord ++ tailWord_327388).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_327388).length < 2 ^ (prefixWord ++ tailWord_327388).sum := by decide
  have hdescent : baseEnd_327388 < baseStart_327388 := by decide
  rcases family_descends (prefixWord ++ tailWord_327388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_327395 : List Nat := [1, 1, 1, 7, 2, 1, 3, 4]
def baseStart_327395 : Nat := 118140960795 + 327395 * 2 ^ 59
def prefixEnd_327395 : Nat := 4983230072969 + 3 ^ 40 * 327395 * 2
def baseEnd_327395 : Nat := 49810666334474607187213

theorem tailTrace_327395 : CollatzResearch.WordTrace tailWord_327395 prefixEnd_327395 49810666334474607187213 := by
  unfold tailWord_327395
  simp only [CollatzResearch.WordTrace]
  refine ⟨11941076648911304459519639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7960717765940869639679759 11941076648911304459519639)
  ·
    refine ⟨17911614973366956689279459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11941076648911304459519639 17911614973366956689279459)
    ·
      refine ⟨26867422460050435033919189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17911614973366956689279459 26867422460050435033919189)
      ·
        refine ⟨629705213907432071107481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 26867422460050435033919189 629705213907432071107481)
        ·
          refine ⟨472278910430574053330611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 629705213907432071107481 472278910430574053330611)
          ·
            refine ⟨708418365645861079995917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 472278910430574053330611 708418365645861079995917)
            ·
              refine ⟨265656887117197904998469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 708418365645861079995917 265656887117197904998469)
              ·
                refine ⟨49810666334474607187213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 265656887117197904998469 49810666334474607187213)
                ·
                  rfl

theorem cell20_327395_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 2, 1, 3, 4].length) (baseStart_327395 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_327395 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_327395 prefixEnd_327395 := by exact prefixLift 327395
  have htrace : WordTrace (prefixWord ++ tailWord_327395) baseStart_327395 baseEnd_327395 := by
    simpa [prefixWord, tailWord_327395, baseEnd_327395] using wordTrace_append hprefix tailTrace_327395
  have hstable : (prefixWord ++ tailWord_327395).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_327395).length < 2 ^ (prefixWord ++ tailWord_327395).sum := by decide
  have hdescent : baseEnd_327395 < baseStart_327395 := by decide
  rcases family_descends (prefixWord ++ tailWord_327395) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_327409 : List Nat := [1, 2, 2, 2, 2, 3, 1, 5, 2]
def baseStart_327409 : Nat := 118140960795 + 327409 * 2 ^ 59
def prefixEnd_327409 : Nat := 4983230072969 + 3 ^ 40 * 327409 * 2
def baseEnd_327409 : Nat := 149438388984901995094915

theorem tailTrace_327409 : CollatzResearch.WordTrace tailWord_327409 prefixEnd_327409 149438388984901995094915 := by
  unfold tailWord_327409
  simp only [CollatzResearch.WordTrace]
  refine ⟨11941587270860584850529281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7961058180573723233686187 11941587270860584850529281)
  ·
    refine ⟨8956190453145438637896961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11941587270860584850529281 8956190453145438637896961)
    ·
      refine ⟨6717142839859078978422721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8956190453145438637896961 6717142839859078978422721)
      ·
        refine ⟨5037857129894309233817041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6717142839859078978422721 5037857129894309233817041)
        ·
          refine ⟨3778392847420731925362781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5037857129894309233817041 3778392847420731925362781)
          ·
            refine ⟨1416897317782774472011043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3778392847420731925362781 1416897317782774472011043)
            ·
              refine ⟨2125345976674161708016565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1416897317782774472011043 2125345976674161708016565)
              ·
                refine ⟨199251185313202660126553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2125345976674161708016565 199251185313202660126553)
                ·
                  refine ⟨149438388984901995094915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 199251185313202660126553 149438388984901995094915)
                  ·
                    rfl

theorem cell20_327409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 1, 5, 2].length) (baseStart_327409 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_327409 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_327409 prefixEnd_327409 := by exact prefixLift 327409
  have htrace : WordTrace (prefixWord ++ tailWord_327409) baseStart_327409 baseEnd_327409 := by
    simpa [prefixWord, tailWord_327409, baseEnd_327409] using wordTrace_append hprefix tailTrace_327409
  have hstable : (prefixWord ++ tailWord_327409).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_327409).length < 2 ^ (prefixWord ++ tailWord_327409).sum := by decide
  have hdescent : baseEnd_327409 < baseStart_327409 := by decide
  rcases family_descends (prefixWord ++ tailWord_327409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_327423 : List Nat := [1, 1, 2, 2, 1, 3, 5, 2, 3]
def baseStart_327423 : Nat := 118140960795 + 327423 * 2 ^ 59
def prefixEnd_327423 : Nat := 4983230072969 + 3 ^ 40 * 327423 * 2
def baseEnd_327423 : Nat := 149444778966380168628191

theorem tailTrace_327423 : CollatzResearch.WordTrace tailWord_327423 prefixEnd_327423 149444778966380168628191 := by
  unfold tailWord_327423
  simp only [CollatzResearch.WordTrace]
  refine ⟨11942097892809865241538923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7961398595206576827692615 11942097892809865241538923)
  ·
    refine ⟨17913146839214797862308385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11942097892809865241538923 17913146839214797862308385)
    ·
      refine ⟨13434860129411098396731289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17913146839214797862308385 13434860129411098396731289)
      ·
        refine ⟨10076145097058323797548467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13434860129411098396731289 10076145097058323797548467)
        ·
          refine ⟨15114217645587485696322701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10076145097058323797548467 15114217645587485696322701)
          ·
            refine ⟨5667831617095307136121013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15114217645587485696322701 5667831617095307136121013)
            ·
              refine ⟨531359214102685044011345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 5667831617095307136121013 531359214102685044011345)
              ·
                refine ⟨398519410577013783008509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 531359214102685044011345 398519410577013783008509)
                ·
                  refine ⟨149444778966380168628191, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 398519410577013783008509 149444778966380168628191)
                  ·
                    rfl

theorem cell20_327423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 5, 2, 3].length) (baseStart_327423 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_327423 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_327423 prefixEnd_327423 := by exact prefixLift 327423
  have htrace : WordTrace (prefixWord ++ tailWord_327423) baseStart_327423 baseEnd_327423 := by
    simpa [prefixWord, tailWord_327423, baseEnd_327423] using wordTrace_append hprefix tailTrace_327423
  have hstable : (prefixWord ++ tailWord_327423).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_327423).length < 2 ^ (prefixWord ++ tailWord_327423).sum := by decide
  have hdescent : baseEnd_327423 < baseStart_327423 := by decide
  rcases family_descends (prefixWord ++ tailWord_327423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_327426 : List Nat := [3, 4, 1, 1, 1, 1, 1, 6, 2]
def baseStart_327426 : Nat := 118140960795 + 327426 * 2 ^ 59
def prefixEnd_327426 : Nat := 4983230072969 + 3 ^ 40 * 327426 * 2
def baseEnd_327426 : Nat := 149446148248125491528179

theorem tailTrace_327426 : CollatzResearch.WordTrace tailWord_327426 prefixEnd_327426 149446148248125491528179 := by
  unfold tailWord_327426
  simp only [CollatzResearch.WordTrace]
  refine ⟨2985551827949749188474533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7961471541199331169265421 2985551827949749188474533)
  ·
    refine ⟨559790967740577972838975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2985551827949749188474533 559790967740577972838975)
    ·
      refine ⟨839686451610866959258463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 559790967740577972838975 839686451610866959258463)
      ·
        refine ⟨1259529677416300438887695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 839686451610866959258463 1259529677416300438887695)
        ·
          refine ⟨1889294516124450658331543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1259529677416300438887695 1889294516124450658331543)
          ·
            refine ⟨2833941774186675987497315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1889294516124450658331543 2833941774186675987497315)
            ·
              refine ⟨4250912661280013981245973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2833941774186675987497315 4250912661280013981245973)
              ·
                refine ⟨199261530997500655370905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 4250912661280013981245973 199261530997500655370905)
                ·
                  refine ⟨149446148248125491528179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 199261530997500655370905 149446148248125491528179)
                  ·
                    rfl

theorem cell20_327426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 1, 6, 2].length) (baseStart_327426 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_327426 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_327426 prefixEnd_327426 := by exact prefixLift 327426
  have htrace : WordTrace (prefixWord ++ tailWord_327426) baseStart_327426 baseEnd_327426 := by
    simpa [prefixWord, tailWord_327426, baseEnd_327426] using wordTrace_append hprefix tailTrace_327426
  have hstable : (prefixWord ++ tailWord_327426).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_327426).length < 2 ^ (prefixWord ++ tailWord_327426).sum := by decide
  have hdescent : baseEnd_327426 < baseStart_327426 := by decide
  rcases family_descends (prefixWord ++ tailWord_327426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_327464 : List Nat := [2, 1, 5, 1, 1, 2, 3, 3, 2]
def baseStart_327464 : Nat := 118140960795 + 327464 * 2 ^ 59
def prefixEnd_327464 : Nat := 4983230072969 + 3 ^ 40 * 327464 * 2
def baseEnd_327464 : Nat := 149463492483566248261357

theorem tailTrace_327464 : CollatzResearch.WordTrace tailWord_327464 prefixEnd_327464 149463492483566248261357 := by
  unfold tailWord_327464
  simp only [CollatzResearch.WordTrace]
  refine ⟨5971796642830664621890723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7962395523774219495854297 5971796642830664621890723)
  ·
    refine ⟨8957694964245996932836085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5971796642830664621890723 8957694964245996932836085)
    ·
      refine ⟨839783902898062212453383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 8957694964245996932836085 839783902898062212453383)
      ·
        refine ⟨1259675854347093318680075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 839783902898062212453383 1259675854347093318680075)
        ·
          refine ⟨1889513781520639978020113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1259675854347093318680075 1889513781520639978020113)
          ·
            refine ⟨1417135336140479983515085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1889513781520639978020113 1417135336140479983515085)
            ·
              refine ⟨531425751052679993818157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1417135336140479983515085 531425751052679993818157)
              ·
                refine ⟨199284656644754997681809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 531425751052679993818157 199284656644754997681809)
                ·
                  refine ⟨149463492483566248261357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 199284656644754997681809 149463492483566248261357)
                  ·
                    rfl

theorem cell20_327464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 3, 3, 2].length) (baseStart_327464 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_327464 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_327464 prefixEnd_327464 := by exact prefixLift 327464
  have htrace : WordTrace (prefixWord ++ tailWord_327464) baseStart_327464 baseEnd_327464 := by
    simpa [prefixWord, tailWord_327464, baseEnd_327464] using wordTrace_append hprefix tailTrace_327464
  have hstable : (prefixWord ++ tailWord_327464).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_327464).length < 2 ^ (prefixWord ++ tailWord_327464).sum := by decide
  have hdescent : baseEnd_327464 < baseStart_327464 := by decide
  rcases family_descends (prefixWord ++ tailWord_327464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_327478 : List Nat := [5, 1, 2, 2, 1, 1, 2, 1, 5]
def baseStart_327478 : Nat := 118140960795 + 327478 * 2 ^ 59
def prefixEnd_327478 : Nat := 4983230072969 + 3 ^ 40 * 327478 * 2
def baseEnd_327478 : Nat := 149469882465044421794633

theorem tailTrace_327478 : CollatzResearch.WordTrace tailWord_327478 prefixEnd_327478 149469882465044421794633 := by
  unfold tailWord_327478
  simp only [CollatzResearch.WordTrace]
  refine ⟨746506494225663102174443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 7962735938407073089860725 746506494225663102174443)
  ·
    refine ⟨1119759741338494653261665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 746506494225663102174443 1119759741338494653261665)
    ·
      refine ⟨839819806003870989946249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1119759741338494653261665 839819806003870989946249)
      ·
        refine ⟨629864854502903242459687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 839819806003870989946249 629864854502903242459687)
        ·
          refine ⟨944797281754354863689531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 629864854502903242459687 944797281754354863689531)
          ·
            refine ⟨1417195922631532295534297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 944797281754354863689531 1417195922631532295534297)
            ·
              refine ⟨1062896941973649221650723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1417195922631532295534297 1062896941973649221650723)
              ·
                refine ⟨1594345412960473832476085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1062896941973649221650723 1594345412960473832476085)
                ·
                  refine ⟨149469882465044421794633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1594345412960473832476085 149469882465044421794633)
                  ·
                    rfl

theorem cell20_327478_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 2, 1, 5].length) (baseStart_327478 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_327478 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_327478 prefixEnd_327478 := by exact prefixLift 327478
  have htrace : WordTrace (prefixWord ++ tailWord_327478) baseStart_327478 baseEnd_327478 := by
    simpa [prefixWord, tailWord_327478, baseEnd_327478] using wordTrace_append hprefix tailTrace_327478
  have hstable : (prefixWord ++ tailWord_327478).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_327478).length < 2 ^ (prefixWord ++ tailWord_327478).sum := by decide
  have hdescent : baseEnd_327478 < baseStart_327478 := by decide
  rcases family_descends (prefixWord ++ tailWord_327478) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_327481 : List Nat := [1, 2, 1, 7, 2, 1, 1, 1, 4]
def baseStart_327481 : Nat := 118140960795 + 327481 * 2 ^ 59
def prefixEnd_327481 : Nat := 4983230072969 + 3 ^ 40 * 327481 * 2
def baseEnd_327481 : Nat := 149471251746789744694621

theorem tailTrace_327481 : CollatzResearch.WordTrace tailWord_327481 prefixEnd_327481 149471251746789744694621 := by
  unfold tailWord_327481
  simp only [CollatzResearch.WordTrace]
  refine ⟨11944213326599741147150297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7962808884399827431433531 11944213326599741147150297)
  ·
    refine ⟨8958159994949805860362723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11944213326599741147150297 8958159994949805860362723)
    ·
      refine ⟨13437239992424708790544085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8958159994949805860362723 13437239992424708790544085)
      ·
        refine ⟨314935312322454112278377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 13437239992424708790544085 314935312322454112278377)
        ·
          refine ⟨236201484241840584208783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 314935312322454112278377 236201484241840584208783)
          ·
            refine ⟨354302226362760876313175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 236201484241840584208783 354302226362760876313175)
            ·
              refine ⟨531453339544141314469763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 354302226362760876313175 531453339544141314469763)
              ·
                refine ⟨797180009316211971704645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 531453339544141314469763 797180009316211971704645)
                ·
                  refine ⟨149471251746789744694621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 797180009316211971704645 149471251746789744694621)
                  ·
                    rfl

theorem cell20_327481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 2, 1, 1, 1, 4].length) (baseStart_327481 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_327481 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_327481 prefixEnd_327481 := by exact prefixLift 327481
  have htrace : WordTrace (prefixWord ++ tailWord_327481) baseStart_327481 baseEnd_327481 := by
    simpa [prefixWord, tailWord_327481, baseEnd_327481] using wordTrace_append hprefix tailTrace_327481
  have hstable : (prefixWord ++ tailWord_327481).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_327481).length < 2 ^ (prefixWord ++ tailWord_327481).sum := by decide
  have hdescent : baseEnd_327481 < baseStart_327481 := by decide
  rcases family_descends (prefixWord ++ tailWord_327481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_327485 : List Nat := [1, 4, 1, 4, 1, 1, 3, 1, 4]
def baseStart_327485 : Nat := 118140960795 + 327485 * 2 ^ 59
def prefixEnd_327485 : Nat := 4983230072969 + 3 ^ 40 * 327485 * 2
def baseEnd_327485 : Nat := 149473077455783508561271

theorem tailTrace_327485 : CollatzResearch.WordTrace tailWord_327485 prefixEnd_327485 149473077455783508561271 := by
  unfold tailWord_327485
  simp only [CollatzResearch.WordTrace]
  refine ⟨11944359218585249830295909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7962906145723499886863939 11944359218585249830295909)
  ·
    refine ⟨2239567353484734343180483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 11944359218585249830295909 2239567353484734343180483)
    ·
      refine ⟨3359351030227101514770725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2239567353484734343180483 3359351030227101514770725)
      ·
        refine ⟨629878318167581534019511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3359351030227101514770725 629878318167581534019511)
        ·
          refine ⟨944817477251372301029267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 629878318167581534019511 944817477251372301029267)
          ·
            refine ⟨1417226215877058451543901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 944817477251372301029267 1417226215877058451543901)
            ·
              refine ⟨531459830953896919328963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1417226215877058451543901 531459830953896919328963)
              ·
                refine ⟨797189746430845378993445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 531459830953896919328963 797189746430845378993445)
                ·
                  refine ⟨149473077455783508561271, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 797189746430845378993445 149473077455783508561271)
                  ·
                    rfl

theorem cell20_327485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 3, 1, 4].length) (baseStart_327485 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_327485 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_327485 prefixEnd_327485 := by exact prefixLift 327485
  have htrace : WordTrace (prefixWord ++ tailWord_327485) baseStart_327485 baseEnd_327485 := by
    simpa [prefixWord, tailWord_327485, baseEnd_327485] using wordTrace_append hprefix tailTrace_327485
  have hstable : (prefixWord ++ tailWord_327485).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_327485).length < 2 ^ (prefixWord ++ tailWord_327485).sum := by decide
  have hdescent : baseEnd_327485 < baseStart_327485 := by decide
  rcases family_descends (prefixWord ++ tailWord_327485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_327530 : List Nat := [3, 1, 3, 4, 1, 8]
def baseStart_327530 : Nat := 118140960795 + 327530 * 2 ^ 59
def prefixEnd_327530 : Nat := 4983230072969 + 3 ^ 40 * 327530 * 2
def baseEnd_327530 : Nat := 5536800617850494520781

theorem tailTrace_327530 : CollatzResearch.WordTrace tailWord_327530 prefixEnd_327530 5536800617850494520781 := by
  unfold tailWord_327530
  simp only [CollatzResearch.WordTrace]
  refine ⟨2986500125855555628921011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7964000335614815010456029 2986500125855555628921011)
  ·
    refine ⟨4479750188783333443381517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2986500125855555628921011 4479750188783333443381517)
    ·
      refine ⟨1679906320793750041268069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4479750188783333443381517 1679906320793750041268069)
      ·
        refine ⟨314982435148828132737763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1679906320793750041268069 314982435148828132737763)
        ·
          refine ⟨472473652723242199106645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 314982435148828132737763 472473652723242199106645)
          ·
            refine ⟨5536800617850494520781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 472473652723242199106645 5536800617850494520781)
            ·
              rfl

theorem cell20_327530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 1, 8].length) (baseStart_327530 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_327530 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_327530 prefixEnd_327530 := by exact prefixLift 327530
  have htrace : WordTrace (prefixWord ++ tailWord_327530) baseStart_327530 baseEnd_327530 := by
    simpa [prefixWord, tailWord_327530, baseEnd_327530] using wordTrace_append hprefix tailTrace_327530
  have hstable : (prefixWord ++ tailWord_327530).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_327530).length < 2 ^ (prefixWord ++ tailWord_327530).sum := by decide
  have hdescent : baseEnd_327530 < baseStart_327530 := by decide
  rcases family_descends (prefixWord ++ tailWord_327530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_327537 : List Nat := [1, 2, 2, 2, 1, 3, 4, 2, 3]
def baseStart_327537 : Nat := 118140960795 + 327537 * 2 ^ 59
def prefixEnd_327537 : Nat := 4983230072969 + 3 ^ 40 * 327537 * 2
def baseEnd_327537 : Nat := 149496811672702438827725

theorem tailTrace_327537 : CollatzResearch.WordTrace tailWord_327537 prefixEnd_327537 149496811672702438827725 := by
  unfold tailWord_327537
  simp only [CollatzResearch.WordTrace]
  refine ⟨11946255814396862711188865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7964170542931241807459243 11946255814396862711188865)
  ·
    refine ⟨8959691860797647033391649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11946255814396862711188865 8959691860797647033391649)
    ·
      refine ⟨6719768895598235275043737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8959691860797647033391649 6719768895598235275043737)
      ·
        refine ⟨5039826671698676456282803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6719768895598235275043737 5039826671698676456282803)
        ·
          refine ⟨7559740007548014684424205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5039826671698676456282803 7559740007548014684424205)
          ·
            refine ⟨2834902502830505506659077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7559740007548014684424205 2834902502830505506659077)
            ·
              refine ⟨531544219280719782498577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2834902502830505506659077 531544219280719782498577)
              ·
                refine ⟨398658164460539836873933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 531544219280719782498577 398658164460539836873933)
                ·
                  refine ⟨149496811672702438827725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 398658164460539836873933 149496811672702438827725)
                  ·
                    rfl

theorem cell20_327537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 4, 2, 3].length) (baseStart_327537 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_327537 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_327537 prefixEnd_327537 := by exact prefixLift 327537
  have htrace : WordTrace (prefixWord ++ tailWord_327537) baseStart_327537 baseEnd_327537 := by
    simpa [prefixWord, tailWord_327537, baseEnd_327537] using wordTrace_append hprefix tailTrace_327537
  have hstable : (prefixWord ++ tailWord_327537).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_327537).length < 2 ^ (prefixWord ++ tailWord_327537).sum := by decide
  have hdescent : baseEnd_327537 < baseStart_327537 := by decide
  rcases family_descends (prefixWord ++ tailWord_327537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_327578 : List Nat := [3, 1, 1, 4, 2, 2, 2, 3, 2]
def baseStart_327578 : Nat := 118140960795 + 327578 * 2 ^ 59
def prefixEnd_327578 : Nat := 4983230072969 + 3 ^ 40 * 327578 * 2
def baseEnd_327578 : Nat := 149515525189888518460891

theorem tailTrace_327578 : CollatzResearch.WordTrace tailWord_327578 prefixEnd_327578 149515525189888518460891 := by
  unfold tailWord_327578
  simp only [CollatzResearch.WordTrace]
  refine ⟨2986937801812081678357847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7965167471498884475620925 2986937801812081678357847)
  ·
    refine ⟨4480406702718122517536771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2986937801812081678357847 4480406702718122517536771)
    ·
      refine ⟨6720610054077183776305157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4480406702718122517536771 6720610054077183776305157)
      ·
        refine ⟨1260114385139471958057217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6720610054077183776305157 1260114385139471958057217)
        ·
          refine ⟨945085788854603968542913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1260114385139471958057217 945085788854603968542913)
          ·
            refine ⟨708814341640952976407185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 945085788854603968542913 708814341640952976407185)
            ·
              refine ⟨531610756230714732305389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 708814341640952976407185 531610756230714732305389)
              ·
                refine ⟨199354033586518024614521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 531610756230714732305389 199354033586518024614521)
                ·
                  refine ⟨149515525189888518460891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 199354033586518024614521 149515525189888518460891)
                  ·
                    rfl

theorem cell20_327578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 2, 2, 3, 2].length) (baseStart_327578 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_327578 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_327578 prefixEnd_327578 := by exact prefixLift 327578
  have htrace : WordTrace (prefixWord ++ tailWord_327578) baseStart_327578 baseEnd_327578 := by
    simpa [prefixWord, tailWord_327578, baseEnd_327578] using wordTrace_append hprefix tailTrace_327578
  have hstable : (prefixWord ++ tailWord_327578).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_327578).length < 2 ^ (prefixWord ++ tailWord_327578).sum := by decide
  have hdescent : baseEnd_327578 < baseStart_327578 := by decide
  rcases family_descends (prefixWord ++ tailWord_327578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_327650 : List Nat := [3, 3, 3, 1, 2, 1, 3, 2, 2]
def baseStart_327650 : Nat := 118140960795 + 327650 * 2 ^ 59
def prefixEnd_327650 : Nat := 4983230072969 + 3 ^ 40 * 327650 * 2
def baseEnd_327650 : Nat := 149548387951776268060597

theorem tailTrace_327650 : CollatzResearch.WordTrace tailWord_327650 prefixEnd_327650 149548387951776268060597 := by
  unfold tailWord_327650
  simp only [CollatzResearch.WordTrace]
  refine ⟨2987594315746870752513101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7966918175324988673368269 2987594315746870752513101)
  ·
    refine ⟨1120347868405076532192413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2987594315746870752513101 1120347868405076532192413)
    ·
      refine ⟨420130450651903699572155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1120347868405076532192413 420130450651903699572155)
      ·
        refine ⟨630195675977855549358233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 420130450651903699572155 630195675977855549358233)
        ·
          refine ⟨472646756983391662018675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 630195675977855549358233 472646756983391662018675)
          ·
            refine ⟨708970135475087493028013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 472646756983391662018675 708970135475087493028013)
            ·
              refine ⟨265863800803157809885505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 708970135475087493028013 265863800803157809885505)
              ·
                refine ⟨199397850602368357414129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 265863800803157809885505 199397850602368357414129)
                ·
                  refine ⟨149548387951776268060597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 199397850602368357414129 149548387951776268060597)
                  ·
                    rfl

theorem cell20_327650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 2, 1, 3, 2, 2].length) (baseStart_327650 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_327650 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_327650 prefixEnd_327650 := by exact prefixLift 327650
  have htrace : WordTrace (prefixWord ++ tailWord_327650) baseStart_327650 baseEnd_327650 := by
    simpa [prefixWord, tailWord_327650, baseEnd_327650] using wordTrace_append hprefix tailTrace_327650
  have hstable : (prefixWord ++ tailWord_327650).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_327650).length < 2 ^ (prefixWord ++ tailWord_327650).sum := by decide
  have hdescent : baseEnd_327650 < baseStart_327650 := by decide
  rcases family_descends (prefixWord ++ tailWord_327650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_327661 : List Nat := [1, 5, 1, 4, 1, 1, 2, 5]
def baseStart_327661 : Nat := 118140960795 + 327661 * 2 ^ 59
def prefixEnd_327661 : Nat := 4983230072969 + 3 ^ 40 * 327661 * 2
def baseEnd_327661 : Nat := 49851136217169706231295

theorem tailTrace_327661 : CollatzResearch.WordTrace tailWord_327661 prefixEnd_327661 49851136217169706231295 := by
  unfold tailWord_327661
  simp only [CollatzResearch.WordTrace]
  refine ⟨11950778465947631888702837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7967185643965087925801891 11950778465947631888702837)
  ·
    refine ⟨1120385481182590489565891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 11950778465947631888702837 1120385481182590489565891)
    ·
      refine ⟨1680578221773885734348837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1120385481182590489565891 1680578221773885734348837)
      ·
        refine ⟨315108416582603575190407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1680578221773885734348837 315108416582603575190407)
        ·
          refine ⟨472662624873905362785611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 315108416582603575190407 472662624873905362785611)
          ·
            refine ⟨708993937310858044178417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 472662624873905362785611 708993937310858044178417)
            ·
              refine ⟨531745452983143533133813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 708993937310858044178417 531745452983143533133813)
              ·
                refine ⟨49851136217169706231295, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 531745452983143533133813 49851136217169706231295)
                ·
                  rfl

theorem cell20_327661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 1, 1, 2, 5].length) (baseStart_327661 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_327661 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_327661 prefixEnd_327661 := by exact prefixLift 327661
  have htrace : WordTrace (prefixWord ++ tailWord_327661) baseStart_327661 baseEnd_327661 := by
    simpa [prefixWord, tailWord_327661, baseEnd_327661] using wordTrace_append hprefix tailTrace_327661
  have hstable : (prefixWord ++ tailWord_327661).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_327661).length < 2 ^ (prefixWord ++ tailWord_327661).sum := by decide
  have hdescent : baseEnd_327661 < baseStart_327661 := by decide
  rcases family_descends (prefixWord ++ tailWord_327661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_327679 : List Nat := [1, 1, 2, 2, 1, 2, 1, 6, 4]
def baseStart_327679 : Nat := 118140960795 + 327679 * 2 ^ 59
def prefixEnd_327679 : Nat := 4983230072969 + 3 ^ 40 * 327679 * 2
def baseEnd_327679 : Nat := 149561624341981056093811

theorem tailTrace_327679 : CollatzResearch.WordTrace tailWord_327679 prefixEnd_327679 149561624341981056093811 := by
  unfold tailWord_327679
  simp only [CollatzResearch.WordTrace]
  refine ⟨11951434979882420962858091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7967623319921613975238727 11951434979882420962858091)
  ·
    refine ⟨17927152469823631444287137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11951434979882420962858091 17927152469823631444287137)
    ·
      refine ⟨13445364352367723583215353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17927152469823631444287137 13445364352367723583215353)
      ·
        refine ⟨10084023264275792687411515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13445364352367723583215353 10084023264275792687411515)
        ·
          refine ⟨15126034896413689031117273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10084023264275792687411515 15126034896413689031117273)
          ·
            refine ⟨11344526172310266773337955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15126034896413689031117273 11344526172310266773337955)
            ·
              refine ⟨17016789258465400160006933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11344526172310266773337955 17016789258465400160006933)
              ·
                refine ⟨797661996490565632500325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 17016789258465400160006933 797661996490565632500325)
                ·
                  refine ⟨149561624341981056093811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 797661996490565632500325 149561624341981056093811)
                  ·
                    rfl

theorem cell20_327679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 6, 4].length) (baseStart_327679 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_327679 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_327679 prefixEnd_327679 := by exact prefixLift 327679
  have htrace : WordTrace (prefixWord ++ tailWord_327679) baseStart_327679 baseEnd_327679 := by
    simpa [prefixWord, tailWord_327679, baseEnd_327679] using wordTrace_append hprefix tailTrace_327679
  have hstable : (prefixWord ++ tailWord_327679).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_327679).length < 2 ^ (prefixWord ++ tailWord_327679).sum := by decide
  have hdescent : baseEnd_327679 < baseStart_327679 := by decide
  rcases family_descends (prefixWord ++ tailWord_327679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_327703 : List Nat := [1, 1, 3, 5, 2, 8]
def baseStart_327703 : Nat := 118140960795 + 327703 * 2 ^ 59
def prefixEnd_327703 : Nat := 4983230072969 + 3 ^ 40 * 327703 * 2
def baseEnd_327703 : Nat := 5539725133183097751619

theorem tailTrace_327703 : CollatzResearch.WordTrace tailWord_327703 prefixEnd_327703 5539725133183097751619 := by
  unfold tailWord_327703
  simp only [CollatzResearch.WordTrace]
  refine ⟨11952310331795473061731763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7968206887863648707821175 11952310331795473061731763)
  ·
    refine ⟨17928465497693209592597645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11952310331795473061731763 17928465497693209592597645)
    ·
      refine ⟨6723174561634953597224117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17928465497693209592597645 6723174561634953597224117)
      ·
        refine ⟨630297615153276899739761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 6723174561634953597224117 630297615153276899739761)
        ·
          refine ⟨472723211364957674804821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 630297615153276899739761 472723211364957674804821)
          ·
            refine ⟨5539725133183097751619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 472723211364957674804821 5539725133183097751619)
            ·
              rfl

theorem cell20_327703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 2, 8].length) (baseStart_327703 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_327703 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_327703 prefixEnd_327703 := by exact prefixLift 327703
  have htrace : WordTrace (prefixWord ++ tailWord_327703) baseStart_327703 baseEnd_327703 := by
    simpa [prefixWord, tailWord_327703, baseEnd_327703] using wordTrace_append hprefix tailTrace_327703
  have hstable : (prefixWord ++ tailWord_327703).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_327703).length < 2 ^ (prefixWord ++ tailWord_327703).sum := by decide
  have hdescent : baseEnd_327703 < baseStart_327703 := by decide
  rcases family_descends (prefixWord ++ tailWord_327703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_327709 : List Nat := [1, 4, 2, 2, 2, 3, 2, 2, 2]
def baseStart_327709 : Nat := 118140960795 + 327709 * 2 ^ 59
def prefixEnd_327709 : Nat := 4983230072969 + 3 ^ 40 * 327709 * 2
def baseEnd_327709 : Nat := 149575317159434285093689

theorem tailTrace_327709 : CollatzResearch.WordTrace tailWord_327709 prefixEnd_327709 149575317159434285093689 := by
  unfold tailWord_327709
  simp only [CollatzResearch.WordTrace]
  refine ⟨11952529169773736086450181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7968352779849157390966787 11952529169773736086450181)
  ·
    refine ⟨2241099219332575516209409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 11952529169773736086450181 2241099219332575516209409)
    ·
      refine ⟨1680824414499431637157057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2241099219332575516209409 1680824414499431637157057)
      ·
        refine ⟨1260618310874573727867793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1680824414499431637157057 1260618310874573727867793)
        ·
          refine ⟨945463733155930295900845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1260618310874573727867793 945463733155930295900845)
          ·
            refine ⟨354548899933473860962817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 945463733155930295900845 354548899933473860962817)
            ·
              refine ⟨265911674950105395722113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 354548899933473860962817 265911674950105395722113)
              ·
                refine ⟨199433756212579046791585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 265911674950105395722113 199433756212579046791585)
                ·
                  refine ⟨149575317159434285093689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 199433756212579046791585 149575317159434285093689)
                  ·
                    rfl

theorem cell20_327709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 3, 2, 2, 2].length) (baseStart_327709 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_327709 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_327709 prefixEnd_327709 := by exact prefixLift 327709
  have htrace : WordTrace (prefixWord ++ tailWord_327709) baseStart_327709 baseEnd_327709 := by
    simpa [prefixWord, tailWord_327709, baseEnd_327709] using wordTrace_append hprefix tailTrace_327709
  have hstable : (prefixWord ++ tailWord_327709).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_327709).length < 2 ^ (prefixWord ++ tailWord_327709).sum := by decide
  have hdescent : baseEnd_327709 < baseStart_327709 := by decide
  rcases family_descends (prefixWord ++ tailWord_327709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_327724 : List Nat := [2, 2, 1, 1, 1, 2, 2, 9]
def baseStart_327724 : Nat := 118140960795 + 327724 * 2 ^ 59
def prefixEnd_327724 : Nat := 4983230072969 + 3 ^ 40 * 327724 * 2
def baseEnd_327724 : Nat := 49860721189386966531209

theorem tailTrace_327724 : CollatzResearch.WordTrace tailWord_327724 prefixEnd_327724 49860721189386966531209 := by
  unfold tailWord_327724
  simp only [CollatzResearch.WordTrace]
  refine ⟨5976538132359696824123113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7968717509812929098830817 5976538132359696824123113)
  ·
    refine ⟨4482403599269772618092335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5976538132359696824123113 4482403599269772618092335)
    ·
      refine ⟨6723605398904658927138503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4482403599269772618092335 6723605398904658927138503)
      ·
        refine ⟨10085408098356988390707755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6723605398904658927138503 10085408098356988390707755)
        ·
          refine ⟨15128112147535482586061633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10085408098356988390707755 15128112147535482586061633)
          ·
            refine ⟨11346084110651611939546225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15128112147535482586061633 11346084110651611939546225)
            ·
              refine ⟨8509563082988708954659669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11346084110651611939546225 8509563082988708954659669)
              ·
                refine ⟨49860721189386966531209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 8509563082988708954659669 49860721189386966531209)
                ·
                  rfl

theorem cell20_327724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 2, 9].length) (baseStart_327724 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_327724 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_327724 prefixEnd_327724 := by exact prefixLift 327724
  have htrace : WordTrace (prefixWord ++ tailWord_327724) baseStart_327724 baseEnd_327724 := by
    simpa [prefixWord, tailWord_327724, baseEnd_327724] using wordTrace_append hprefix tailTrace_327724
  have hstable : (prefixWord ++ tailWord_327724).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_327724).length < 2 ^ (prefixWord ++ tailWord_327724).sum := by decide
  have hdescent : baseEnd_327724 < baseStart_327724 := by decide
  rcases family_descends (prefixWord ++ tailWord_327724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_327751 : List Nat := [1, 1, 4, 1, 3, 1, 4, 3, 2]
def baseStart_327751 : Nat := 118140960795 + 327751 * 2 ^ 59
def prefixEnd_327751 : Nat := 4983230072969 + 3 ^ 40 * 327751 * 2
def baseEnd_327751 : Nat := 149594487103868805693517

theorem tailTrace_327751 : CollatzResearch.WordTrace tailWord_327751 prefixEnd_327751 149594487103868805693517 := by
  unfold tailWord_327751
  simp only [CollatzResearch.WordTrace]
  refine ⟨11954061035621577259479107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7969374023747718172986071 11954061035621577259479107)
  ·
    refine ⟨17931091553432365889218661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11954061035621577259479107 17931091553432365889218661)
    ·
      refine ⟨3362079666268568604228499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 17931091553432365889218661 3362079666268568604228499)
      ·
        refine ⟨5043119499402852906342749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3362079666268568604228499 5043119499402852906342749)
        ·
          refine ⟨1891169812276069839878531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5043119499402852906342749 1891169812276069839878531)
          ·
            refine ⟨2836754718414104759817797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1891169812276069839878531 2836754718414104759817797)
            ·
              refine ⟨531891509702644642465837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2836754718414104759817797 531891509702644642465837)
              ·
                refine ⟨199459316138491740924689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 531891509702644642465837 199459316138491740924689)
                ·
                  refine ⟨149594487103868805693517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 199459316138491740924689 149594487103868805693517)
                  ·
                    rfl

theorem cell20_327751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 4, 3, 2].length) (baseStart_327751 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_327751 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_327751 prefixEnd_327751 := by exact prefixLift 327751
  have htrace : WordTrace (prefixWord ++ tailWord_327751) baseStart_327751 baseEnd_327751 := by
    simpa [prefixWord, tailWord_327751, baseEnd_327751] using wordTrace_append hprefix tailTrace_327751
  have hstable : (prefixWord ++ tailWord_327751).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_327751).length < 2 ^ (prefixWord ++ tailWord_327751).sum := by decide
  have hdescent : baseEnd_327751 < baseStart_327751 := by decide
  rcases family_descends (prefixWord ++ tailWord_327751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_327765 : List Nat := [1, 3, 2, 2, 1, 3, 3, 2, 3]
def baseStart_327765 : Nat := 118140960795 + 327765 * 2 ^ 59
def prefixEnd_327765 : Nat := 4983230072969 + 3 ^ 40 * 327765 * 2
def baseEnd_327765 : Nat := 149600877085346979226793

theorem tailTrace_327765 : CollatzResearch.WordTrace tailWord_327765 prefixEnd_327765 149600877085346979226793 := by
  unfold tailWord_327765
  simp only [CollatzResearch.WordTrace]
  refine ⟨11954571657570857650488749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7969714438380571766992499 11954571657570857650488749)
  ·
    refine ⟨4482964371589071618933281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11954571657570857650488749 4482964371589071618933281)
    ·
      refine ⟨3362223278691803714199961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4482964371589071618933281 3362223278691803714199961)
      ·
        refine ⟨2521667459018852785649971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3362223278691803714199961 2521667459018852785649971)
        ·
          refine ⟨3782501188528279178474957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2521667459018852785649971 3782501188528279178474957)
          ·
            refine ⟨1418437945698104691928109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3782501188528279178474957 1418437945698104691928109)
            ·
              refine ⟨531914229636789259473041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1418437945698104691928109 531914229636789259473041)
              ·
                refine ⟨398935672227591944604781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 531914229636789259473041 398935672227591944604781)
                ·
                  refine ⟨149600877085346979226793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 398935672227591944604781 149600877085346979226793)
                  ·
                    rfl

theorem cell20_327765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 3, 2, 3].length) (baseStart_327765 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_327765 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_327765 prefixEnd_327765 := by exact prefixLift 327765
  have htrace : WordTrace (prefixWord ++ tailWord_327765) baseStart_327765 baseEnd_327765 := by
    simpa [prefixWord, tailWord_327765, baseEnd_327765] using wordTrace_append hprefix tailTrace_327765
  have hstable : (prefixWord ++ tailWord_327765).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_327765).length < 2 ^ (prefixWord ++ tailWord_327765).sum := by decide
  have hdescent : baseEnd_327765 < baseStart_327765 := by decide
  rcases family_descends (prefixWord ++ tailWord_327765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_327772 : List Nat := [2, 2, 4, 1, 1, 2, 1, 3, 4]
def baseStart_327772 : Nat := 118140960795 + 327772 * 2 ^ 59
def prefixEnd_327772 : Nat := 4983230072969 + 3 ^ 40 * 327772 * 2
def baseEnd_327772 : Nat := 149604072076086065993431

theorem tailTrace_327772 : CollatzResearch.WordTrace tailWord_327772 prefixEnd_327772 149604072076086065993431 := by
  unfold tailWord_327772
  simp only [CollatzResearch.WordTrace]
  refine ⟨5977413484272748922996785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7969884645696998563995713 5977413484272748922996785)
  ·
    refine ⟨4483060113204561692247589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5977413484272748922996785 4483060113204561692247589)
    ·
      refine ⟨840573771225855317296423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4483060113204561692247589 840573771225855317296423)
      ·
        refine ⟨1260860656838782975944635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 840573771225855317296423 1260860656838782975944635)
        ·
          refine ⟨1891290985258174463916953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1260860656838782975944635 1891290985258174463916953)
          ·
            refine ⟨1418468238943630847937715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1891290985258174463916953 1418468238943630847937715)
            ·
              refine ⟨2127702358415446271906573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1418468238943630847937715 2127702358415446271906573)
              ·
                refine ⟨797888384405792351964965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2127702358415446271906573 797888384405792351964965)
                ·
                  refine ⟨149604072076086065993431, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 797888384405792351964965 149604072076086065993431)
                  ·
                    rfl

theorem cell20_327772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 1, 3, 4].length) (baseStart_327772 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_327772 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_327772 prefixEnd_327772 := by exact prefixLift 327772
  have htrace : WordTrace (prefixWord ++ tailWord_327772) baseStart_327772 baseEnd_327772 := by
    simpa [prefixWord, tailWord_327772, baseEnd_327772] using wordTrace_append hprefix tailTrace_327772
  have hstable : (prefixWord ++ tailWord_327772).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_327772).length < 2 ^ (prefixWord ++ tailWord_327772).sum := by decide
  have hdescent : baseEnd_327772 < baseStart_327772 := by decide
  rcases family_descends (prefixWord ++ tailWord_327772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_327793 : List Nat := [1, 2, 2, 2, 1, 1, 3, 4, 4]
def baseStart_327793 : Nat := 118140960795 + 327793 * 2 ^ 59
def prefixEnd_327793 : Nat := 4983230072969 + 3 ^ 40 * 327793 * 2
def baseEnd_327793 : Nat := 149613657048303326293345

theorem tailTrace_327793 : CollatzResearch.WordTrace tailWord_327793 prefixEnd_327793 149613657048303326293345 := by
  unfold tailWord_327793
  simp only [CollatzResearch.WordTrace]
  refine ⟨11955592901469418432508033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7970395267646278955005355 11955592901469418432508033)
  ·
    refine ⟨8966694676102063824381025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11955592901469418432508033 8966694676102063824381025)
    ·
      refine ⟨6725021007076547868285769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8966694676102063824381025 6725021007076547868285769)
      ·
        refine ⟨5043765755307410901214327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6725021007076547868285769 5043765755307410901214327)
        ·
          refine ⟨7565648632961116351821491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5043765755307410901214327 7565648632961116351821491)
          ·
            refine ⟨11348472949441674527732237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7565648632961116351821491 11348472949441674527732237)
            ·
              refine ⟨4255677356040627947899589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11348472949441674527732237 4255677356040627947899589)
              ·
                refine ⟨797939504257617740231173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4255677356040627947899589 797939504257617740231173)
                ·
                  refine ⟨149613657048303326293345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 797939504257617740231173 149613657048303326293345)
                  ·
                    rfl

theorem cell20_327793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 3, 4, 4].length) (baseStart_327793 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_327793 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_327793 prefixEnd_327793 := by exact prefixLift 327793
  have htrace : WordTrace (prefixWord ++ tailWord_327793) baseStart_327793 baseEnd_327793 := by
    simpa [prefixWord, tailWord_327793, baseEnd_327793] using wordTrace_append hprefix tailTrace_327793
  have hstable : (prefixWord ++ tailWord_327793).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_327793).length < 2 ^ (prefixWord ++ tailWord_327793).sum := by decide
  have hdescent : baseEnd_327793 < baseStart_327793 := by decide
  rcases family_descends (prefixWord ++ tailWord_327793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_327824 : List Nat := [2, 1, 1, 1, 1, 1, 6, 4, 3]
def baseStart_327824 : Nat := 118140960795 + 327824 * 2 ^ 59
def prefixEnd_327824 : Nat := 4983230072969 + 3 ^ 40 * 327824 * 2
def baseEnd_327824 : Nat := 149627806293004996259885

theorem tailTrace_327824 : CollatzResearch.WordTrace tailWord_327824 prefixEnd_327824 149627806293004996259885 := by
  unfold tailWord_327824
  simp only [CollatzResearch.WordTrace]
  refine ⟨5978361782178555363443263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7971149042904740484591017 5978361782178555363443263)
  ·
    refine ⟨8967542673267833045164895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5978361782178555363443263 8967542673267833045164895)
    ·
      refine ⟨13451314009901749567747343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8967542673267833045164895 13451314009901749567747343)
      ·
        refine ⟨20176971014852624351621015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13451314009901749567747343 20176971014852624351621015)
        ·
          refine ⟨30265456522278936527431523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20176971014852624351621015 30265456522278936527431523)
          ·
            refine ⟨45398184783418404791147285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30265456522278936527431523 45398184783418404791147285)
            ·
              refine ⟨2128039911722737724585029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 45398184783418404791147285 2128039911722737724585029)
              ·
                refine ⟨399007483448013323359693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2128039911722737724585029 399007483448013323359693)
                ·
                  refine ⟨149627806293004996259885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 399007483448013323359693 149627806293004996259885)
                  ·
                    rfl

theorem cell20_327824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 6, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 6, 4, 3].length) (baseStart_327824 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_327824 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_327824 prefixEnd_327824 := by exact prefixLift 327824
  have htrace : WordTrace (prefixWord ++ tailWord_327824) baseStart_327824 baseEnd_327824 := by
    simpa [prefixWord, tailWord_327824, baseEnd_327824] using wordTrace_append hprefix tailTrace_327824
  have hstable : (prefixWord ++ tailWord_327824).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_327824).length < 2 ^ (prefixWord ++ tailWord_327824).sum := by decide
  have hdescent : baseEnd_327824 < baseStart_327824 := by decide
  rcases family_descends (prefixWord ++ tailWord_327824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_327834 : List Nat := [3, 1, 1, 5, 2, 1, 2, 5]
def baseStart_327834 : Nat := 118140960795 + 327834 * 2 ^ 59
def prefixEnd_327834 : Nat := 4983230072969 + 3 ^ 40 * 327834 * 2
def baseEnd_327834 : Nat := 49877456855163135308837

theorem tailTrace_327834 : CollatzResearch.WordTrace tailWord_327834 prefixEnd_327834 49877456855163135308837 := by
  unfold tailWord_327834
  simp only [CollatzResearch.WordTrace]
  refine ⟨2989272073580220608687639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7971392196213921623167037 2989272073580220608687639)
  ·
    refine ⟨4483908110370330913031459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2989272073580220608687639 4483908110370330913031459)
    ·
      refine ⟨6725862165555496369547189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4483908110370330913031459 6725862165555496369547189)
      ·
        refine ⟨630549578020827784645049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 6725862165555496369547189 630549578020827784645049)
        ·
          refine ⟨472912183515620838483787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 630549578020827784645049 472912183515620838483787)
          ·
            refine ⟨709368275273431257725681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 472912183515620838483787 709368275273431257725681)
            ·
              refine ⟨532026206455073443294261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 709368275273431257725681 532026206455073443294261)
              ·
                refine ⟨49877456855163135308837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 532026206455073443294261 49877456855163135308837)
                ·
                  rfl

theorem cell20_327834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 2, 1, 2, 5].length) (baseStart_327834 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_327834 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_327834 prefixEnd_327834 := by exact prefixLift 327834
  have htrace : WordTrace (prefixWord ++ tailWord_327834) baseStart_327834 baseEnd_327834 := by
    simpa [prefixWord, tailWord_327834, baseEnd_327834] using wordTrace_append hprefix tailTrace_327834
  have hstable : (prefixWord ++ tailWord_327834).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_327834).length < 2 ^ (prefixWord ++ tailWord_327834).sum := by decide
  have hdescent : baseEnd_327834 < baseStart_327834 := by decide
  rcases family_descends (prefixWord ++ tailWord_327834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_327841 : List Nat := [1, 2, 3, 3, 1, 3, 1, 3, 3]
def baseStart_327841 : Nat := 118140960795 + 327841 * 2 ^ 59
def prefixEnd_327841 : Nat := 4983230072969 + 3 ^ 40 * 327841 * 2
def baseEnd_327841 : Nat := 149635565556228492693149

theorem tailTrace_327841 : CollatzResearch.WordTrace tailWord_327841 prefixEnd_327841 149635565556228492693149 := by
  unfold tailWord_327841
  simp only [CollatzResearch.WordTrace]
  refine ⟨11957343605295522630255377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7971562403530348420170251 11957343605295522630255377)
  ·
    refine ⟨8968007703971641972691533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11957343605295522630255377 8968007703971641972691533)
    ·
      refine ⟨3363002888989365739759325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8968007703971641972691533 3363002888989365739759325)
      ·
        refine ⟨1261126083371012152409747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3363002888989365739759325 1261126083371012152409747)
        ·
          refine ⟨1891689125056518228614621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1261126083371012152409747 1891689125056518228614621)
          ·
            refine ⟨709383421896194335730483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1891689125056518228614621 709383421896194335730483)
            ·
              refine ⟨1064075132844291503595725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 709383421896194335730483 1064075132844291503595725)
              ·
                refine ⟨399028174816609313848397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1064075132844291503595725 399028174816609313848397)
                ·
                  refine ⟨149635565556228492693149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 399028174816609313848397 149635565556228492693149)
                  ·
                    rfl

theorem cell20_327841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 3, 1, 3, 3].length) (baseStart_327841 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_327841 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_327841 prefixEnd_327841 := by exact prefixLift 327841
  have htrace : WordTrace (prefixWord ++ tailWord_327841) baseStart_327841 baseEnd_327841 := by
    simpa [prefixWord, tailWord_327841, baseEnd_327841] using wordTrace_append hprefix tailTrace_327841
  have hstable : (prefixWord ++ tailWord_327841).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_327841).length < 2 ^ (prefixWord ++ tailWord_327841).sum := by decide
  have hdescent : baseEnd_327841 < baseStart_327841 := by decide
  rcases family_descends (prefixWord ++ tailWord_327841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_327945 : List Nat := [1, 2, 1, 1, 3, 4, 1, 3, 4]
def baseStart_327945 : Nat := 118140960795 + 327945 * 2 ^ 59
def prefixEnd_327945 : Nat := 4983230072969 + 3 ^ 40 * 327945 * 2
def baseEnd_327945 : Nat := 149683033990066353226057

theorem tailTrace_327945 : CollatzResearch.WordTrace tailWord_327945 prefixEnd_327945 149683033990066353226057 := by
  unfold tailWord_327945
  simp only [CollatzResearch.WordTrace]
  refine ⟨11961136796918748392041289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7974091197945832261360859 11961136796918748392041289)
  ·
    refine ⟨8970852597689061294030967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11961136796918748392041289 8970852597689061294030967)
    ·
      refine ⟨13456278896533591941046451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8970852597689061294030967 13456278896533591941046451)
      ·
        refine ⟨20184418344800387911569677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13456278896533591941046451 20184418344800387911569677)
        ·
          refine ⟨7569156879300145466838629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20184418344800387911569677 7569156879300145466838629)
          ·
            refine ⟨1419216914868777275032243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7569156879300145466838629 1419216914868777275032243)
            ·
              refine ⟨2128825372303165912548365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1419216914868777275032243 2128825372303165912548365)
              ·
                refine ⟨798309514613687217205637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2128825372303165912548365 798309514613687217205637)
                ·
                  refine ⟨149683033990066353226057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 798309514613687217205637 149683033990066353226057)
                  ·
                    rfl

theorem cell20_327945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 1, 3, 4].length) (baseStart_327945 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_327945 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_327945 prefixEnd_327945 := by exact prefixLift 327945
  have htrace : WordTrace (prefixWord ++ tailWord_327945) baseStart_327945 baseEnd_327945 := by
    simpa [prefixWord, tailWord_327945, baseEnd_327945] using wordTrace_append hprefix tailTrace_327945
  have hstable : (prefixWord ++ tailWord_327945).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_327945).length < 2 ^ (prefixWord ++ tailWord_327945).sum := by decide
  have hdescent : baseEnd_327945 < baseStart_327945 := by decide
  rcases family_descends (prefixWord ++ tailWord_327945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_327965 : List Nat := [1, 4, 2, 3, 2, 2, 2, 4]
def baseStart_327965 : Nat := 118140960795 + 327965 * 2 ^ 59
def prefixEnd_327965 : Nat := 4983230072969 + 3 ^ 40 * 327965 * 2
def baseEnd_327965 : Nat := 49897387511678390853103

theorem tailTrace_327965 : CollatzResearch.WordTrace tailWord_327965 prefixEnd_327965 49897387511678390853103 := by
  unfold tailWord_327965
  simp only [CollatzResearch.WordTrace]
  refine ⟨11961866256846291807769349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7974577504564194538512899 11961866256846291807769349)
  ·
    refine ⟨2242849923158679713956753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 11961866256846291807769349 2242849923158679713956753)
    ·
      refine ⟨1682137442369009785467565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2242849923158679713956753 1682137442369009785467565)
      ·
        refine ⟨630801540888378669550337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1682137442369009785467565 630801540888378669550337)
        ·
          refine ⟨473101155666284002162753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 630801540888378669550337 473101155666284002162753)
          ·
            refine ⟨354825866749713001622065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 473101155666284002162753 354825866749713001622065)
            ·
              refine ⟨266119400062284751216549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 354825866749713001622065 266119400062284751216549)
              ·
                refine ⟨49897387511678390853103, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 266119400062284751216549 49897387511678390853103)
                ·
                  rfl

theorem cell20_327965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 2, 2, 2, 4].length) (baseStart_327965 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_327965 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_327965 prefixEnd_327965 := by exact prefixLift 327965
  have htrace : WordTrace (prefixWord ++ tailWord_327965) baseStart_327965 baseEnd_327965 := by
    simpa [prefixWord, tailWord_327965, baseEnd_327965] using wordTrace_append hprefix tailTrace_327965
  have hstable : (prefixWord ++ tailWord_327965).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_327965).length < 2 ^ (prefixWord ++ tailWord_327965).sum := by decide
  have hdescent : baseEnd_327965 < baseStart_327965 := by decide
  rcases family_descends (prefixWord ++ tailWord_327965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_327969 : List Nat := [1, 2, 3, 2, 1, 1, 6, 4]
def baseStart_327969 : Nat := 118140960795 + 327969 * 2 ^ 59
def prefixEnd_327969 : Nat := 4983230072969 + 3 ^ 40 * 327969 * 2
def baseEnd_327969 : Nat := 49897996081342978808653

theorem tailTrace_327969 : CollatzResearch.WordTrace tailWord_327969 prefixEnd_327969 49897996081342978808653 := by
  unfold tailWord_327969
  simp only [CollatzResearch.WordTrace]
  refine ⟨11962012148831800490914961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7974674765887866993943307 11962012148831800490914961)
  ·
    refine ⟨8971509111623850368186221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11962012148831800490914961 8971509111623850368186221)
    ·
      refine ⟨3364315916858943888069833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8971509111623850368186221 3364315916858943888069833)
      ·
        refine ⟨2523236937644207916052375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3364315916858943888069833 2523236937644207916052375)
        ·
          refine ⟨3784855406466311874078563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2523236937644207916052375 3784855406466311874078563)
          ·
            refine ⟨5677283109699467811117845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3784855406466311874078563 5677283109699467811117845)
            ·
              refine ⟨266122645767162553646149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 5677283109699467811117845 266122645767162553646149)
              ·
                refine ⟨49897996081342978808653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 266122645767162553646149 49897996081342978808653)
                ·
                  rfl

theorem cell20_327969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 6, 4].length) (baseStart_327969 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_327969 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_327969 prefixEnd_327969 := by exact prefixLift 327969
  have htrace : WordTrace (prefixWord ++ tailWord_327969) baseStart_327969 baseEnd_327969 := by
    simpa [prefixWord, tailWord_327969, baseEnd_327969] using wordTrace_append hprefix tailTrace_327969
  have hstable : (prefixWord ++ tailWord_327969).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_327969).length < 2 ^ (prefixWord ++ tailWord_327969).sum := by decide
  have hdescent : baseEnd_327969 < baseStart_327969 := by decide
  rcases family_descends (prefixWord ++ tailWord_327969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_327986 : List Nat := [3, 2, 1, 1, 6, 1, 6]
def baseStart_327986 : Nat := 118140960795 + 327986 * 2 ^ 59
def prefixEnd_327986 : Nat := 4983230072969 + 3 ^ 40 * 327986 * 2
def baseEnd_327986 : Nat := 16633527500805825873247

theorem tailTrace_327986 : CollatzResearch.WordTrace tailWord_327986 prefixEnd_327986 16633527500805825873247 := by
  unfold tailWord_327986
  simp only [CollatzResearch.WordTrace]
  refine ⟨2990658047442553098570953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7975088126513474929522541 2990658047442553098570953)
  ·
    refine ⟨2242993535581914823928215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2990658047442553098570953 2242993535581914823928215)
    ·
      refine ⟨3364490303372872235892323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2242993535581914823928215 3364490303372872235892323)
      ·
        refine ⟨5046735455059308353838485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3364490303372872235892323 5046735455059308353838485)
        ·
          refine ⟨236565724455905079086179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 5046735455059308353838485 236565724455905079086179)
          ·
            refine ⟨354848586683857618629269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 236565724455905079086179 354848586683857618629269)
            ·
              refine ⟨16633527500805825873247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 354848586683857618629269 16633527500805825873247)
              ·
                rfl

theorem cell20_327986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 6, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 6, 1, 6].length) (baseStart_327986 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_327986 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_327986 prefixEnd_327986 := by exact prefixLift 327986
  have htrace : WordTrace (prefixWord ++ tailWord_327986) baseStart_327986 baseEnd_327986 := by
    simpa [prefixWord, tailWord_327986, baseEnd_327986] using wordTrace_append hprefix tailTrace_327986
  have hstable : (prefixWord ++ tailWord_327986).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_327986).length < 2 ^ (prefixWord ++ tailWord_327986).sum := by decide
  have hdescent : baseEnd_327986 < baseStart_327986 := by decide
  rcases family_descends (prefixWord ++ tailWord_327986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_328114 : List Nat := [3, 2, 1, 1, 1, 1, 3, 6, 2]
def baseStart_328114 : Nat := 118140960795 + 328114 * 2 ^ 59
def prefixEnd_328114 : Nat := 4983230072969 + 3 ^ 40 * 328114 * 2
def baseEnd_328114 : Nat := 149760170195052876592033

theorem tailTrace_328114 : CollatzResearch.WordTrace tailWord_328114 prefixEnd_328114 149760170195052876592033 := by
  unfold tailWord_328114
  simp only [CollatzResearch.WordTrace]
  refine ⟨2991825183326622563735849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7978200488870993503295597 2991825183326622563735849)
  ·
    refine ⟨2243868887494966922801887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2991825183326622563735849 2243868887494966922801887)
    ·
      refine ⟨3365803331242450384202831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2243868887494966922801887 3365803331242450384202831)
      ·
        refine ⟨5048704996863675576304247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3365803331242450384202831 5048704996863675576304247)
        ·
          refine ⟨7573057495295513364456371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5048704996863675576304247 7573057495295513364456371)
          ·
            refine ⟨11359586242943270046684557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7573057495295513364456371 11359586242943270046684557)
            ·
              refine ⟨4259844841103726267506709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11359586242943270046684557 4259844841103726267506709)
              ·
                refine ⟨199680226926737168789377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 4259844841103726267506709 199680226926737168789377)
                ·
                  refine ⟨149760170195052876592033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 199680226926737168789377 149760170195052876592033)
                  ·
                    rfl

theorem cell20_328114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 3, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 3, 6, 2].length) (baseStart_328114 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_328114 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_328114 prefixEnd_328114 := by exact prefixLift 328114
  have htrace : WordTrace (prefixWord ++ tailWord_328114) baseStart_328114 baseEnd_328114 := by
    simpa [prefixWord, tailWord_328114, baseEnd_328114] using wordTrace_append hprefix tailTrace_328114
  have hstable : (prefixWord ++ tailWord_328114).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_328114).length < 2 ^ (prefixWord ++ tailWord_328114).sum := by decide
  have hdescent : baseEnd_328114 < baseStart_328114 := by decide
  rcases family_descends (prefixWord ++ tailWord_328114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_328124 : List Nat := [2, 2, 2, 4, 1, 2, 3, 1, 3]
def baseStart_328124 : Nat := 118140960795 + 328124 * 2 ^ 59
def prefixEnd_328124 : Nat := 4983230072969 + 3 ^ 40 * 328124 * 2
def baseEnd_328124 : Nat := 149764734467537286258659

theorem tailTrace_328124 : CollatzResearch.WordTrace tailWord_328124 prefixEnd_328124 149764734467537286258659 := by
  unfold tailWord_328124
  simp only [CollatzResearch.WordTrace]
  refine ⟨5983832731635130981403713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7978443642180174641871617 5983832731635130981403713)
  ·
    refine ⟨4487874548726348236052785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5983832731635130981403713 4487874548726348236052785)
    ·
      refine ⟨3365905911544761177039589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4487874548726348236052785 3365905911544761177039589)
      ·
        refine ⟨631107358414642720694923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3365905911544761177039589 631107358414642720694923)
        ·
          refine ⟨946661037621964081042385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 631107358414642720694923 946661037621964081042385)
          ·
            refine ⟨709995778216473060781789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 946661037621964081042385 709995778216473060781789)
            ·
              refine ⟨266248416831177397793171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 709995778216473060781789 266248416831177397793171)
              ·
                refine ⟨399372625246766096689757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 266248416831177397793171 399372625246766096689757)
                ·
                  refine ⟨149764734467537286258659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 399372625246766096689757 149764734467537286258659)
                  ·
                    rfl

theorem cell20_328124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 2, 3, 1, 3].length) (baseStart_328124 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_328124 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_328124 prefixEnd_328124 := by exact prefixLift 328124
  have htrace : WordTrace (prefixWord ++ tailWord_328124) baseStart_328124 baseEnd_328124 := by
    simpa [prefixWord, tailWord_328124, baseEnd_328124] using wordTrace_append hprefix tailTrace_328124
  have hstable : (prefixWord ++ tailWord_328124).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_328124).length < 2 ^ (prefixWord ++ tailWord_328124).sum := by decide
  have hdescent : baseEnd_328124 < baseStart_328124 := by decide
  rcases family_descends (prefixWord ++ tailWord_328124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_328135 : List Nat := [1, 1, 4, 1, 1, 4, 2, 2, 4]
def baseStart_328135 : Nat := 118140960795 + 328135 * 2 ^ 59
def prefixEnd_328135 : Nat := 4983230072969 + 3 ^ 40 * 328135 * 2
def baseEnd_328135 : Nat := 149769755167270136891947

theorem tailTrace_328135 : CollatzResearch.WordTrace tailWord_328135 prefixEnd_328135 149769755167270136891947 := by
  unfold tailWord_328135
  simp only [CollatzResearch.WordTrace]
  refine ⟨11968066666230410841457859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7978711110820273894305239 11968066666230410841457859)
  ·
    refine ⟨17952099999345616262186789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11968066666230410841457859 17952099999345616262186789)
    ·
      refine ⟨3366018749877303049160023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 17952099999345616262186789 3366018749877303049160023)
      ·
        refine ⟨5049028124815954573740035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3366018749877303049160023 5049028124815954573740035)
        ·
          refine ⟨7573542187223931860610053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5049028124815954573740035 7573542187223931860610053)
          ·
            refine ⟨1420039160104487223864385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7573542187223931860610053 1420039160104487223864385)
            ·
              refine ⟨1065029370078365417898289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1420039160104487223864385 1065029370078365417898289)
              ·
                refine ⟨798772027558774063423717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1065029370078365417898289 798772027558774063423717)
                ·
                  refine ⟨149769755167270136891947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 798772027558774063423717 149769755167270136891947)
                  ·
                    rfl

theorem cell20_328135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 2, 2, 4].length) (baseStart_328135 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_328135 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_328135 prefixEnd_328135 := by exact prefixLift 328135
  have htrace : WordTrace (prefixWord ++ tailWord_328135) baseStart_328135 baseEnd_328135 := by
    simpa [prefixWord, tailWord_328135, baseEnd_328135] using wordTrace_append hprefix tailTrace_328135
  have hstable : (prefixWord ++ tailWord_328135).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_328135).length < 2 ^ (prefixWord ++ tailWord_328135).sum := by decide
  have hdescent : baseEnd_328135 < baseStart_328135 := by decide
  rcases family_descends (prefixWord ++ tailWord_328135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_328148 : List Nat := [2, 4, 1, 2, 2, 3, 1, 3, 2]
def baseStart_328148 : Nat := 118140960795 + 328148 * 2 ^ 59
def prefixEnd_328148 : Nat := 4983230072969 + 3 ^ 40 * 328148 * 2
def baseEnd_328148 : Nat := 149775688721499869458561

theorem tailTrace_328148 : CollatzResearch.WordTrace tailWord_328148 prefixEnd_328148 149775688721499869458561 := by
  unfold tailWord_328148
  simp only [CollatzResearch.WordTrace]
  refine ⟨5984270407591657030840549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7979027210122209374454065 5984270407591657030840549)
  ·
    refine ⟨1122050701423435693282603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5984270407591657030840549 1122050701423435693282603)
    ·
      refine ⟨1683076052135153539923905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1122050701423435693282603 1683076052135153539923905)
      ·
        refine ⟨1262307039101365154942929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1683076052135153539923905 1262307039101365154942929)
        ·
          refine ⟨946730279326023866207197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1262307039101365154942929 946730279326023866207197)
          ·
            refine ⟨355023854747258949827699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 946730279326023866207197 355023854747258949827699)
            ·
              refine ⟨532535782120888424741549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 355023854747258949827699 532535782120888424741549)
              ·
                refine ⟨199700918295333159278081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 532535782120888424741549 199700918295333159278081)
                ·
                  refine ⟨149775688721499869458561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 199700918295333159278081 149775688721499869458561)
                  ·
                    rfl

theorem cell20_328148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 3, 1, 3, 2].length) (baseStart_328148 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_328148 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_328148 prefixEnd_328148 := by exact prefixLift 328148
  have htrace : WordTrace (prefixWord ++ tailWord_328148) baseStart_328148 baseEnd_328148 := by
    simpa [prefixWord, tailWord_328148, baseEnd_328148] using wordTrace_append hprefix tailTrace_328148
  have hstable : (prefixWord ++ tailWord_328148).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_328148).length < 2 ^ (prefixWord ++ tailWord_328148).sum := by decide
  have hdescent : baseEnd_328148 < baseStart_328148 := by decide
  rcases family_descends (prefixWord ++ tailWord_328148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_328221 : List Nat := [1, 4, 2, 2, 1, 3, 2, 2, 3]
def baseStart_328221 : Nat := 118140960795 + 328221 * 2 ^ 59
def prefixEnd_328221 : Nat := 4983230072969 + 3 ^ 40 * 328221 * 2
def baseEnd_328221 : Nat := 149809007910636060024929

theorem tailTrace_328221 : CollatzResearch.WordTrace tailWord_328221 prefixEnd_328221 149809007910636060024929 := by
  unfold tailWord_328221
  simp only [CollatzResearch.WordTrace]
  refine ⟨11971203343918847529088517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7980802229279231686059011 11971203343918847529088517)
  ·
    refine ⟨2244600626984783911704097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 11971203343918847529088517 2244600626984783911704097)
    ·
      refine ⟨1683450470238587933778073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2244600626984783911704097 1683450470238587933778073)
      ·
        refine ⟨1262587852678940950333555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1683450470238587933778073 1262587852678940950333555)
        ·
          refine ⟨1893881779018411425500333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1262587852678940950333555 1893881779018411425500333)
          ·
            refine ⟨710205667131904284562625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1893881779018411425500333 710205667131904284562625)
            ·
              refine ⟨532654250348928213421969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 710205667131904284562625 532654250348928213421969)
              ·
                refine ⟨399490687761696160066477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 532654250348928213421969 399490687761696160066477)
                ·
                  refine ⟨149809007910636060024929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 399490687761696160066477 149809007910636060024929)
                  ·
                    rfl

theorem cell20_328221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 3, 2, 2, 3].length) (baseStart_328221 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_328221 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_328221 prefixEnd_328221 := by exact prefixLift 328221
  have htrace : WordTrace (prefixWord ++ tailWord_328221) baseStart_328221 baseEnd_328221 := by
    simpa [prefixWord, tailWord_328221, baseEnd_328221] using wordTrace_append hprefix tailTrace_328221
  have hstable : (prefixWord ++ tailWord_328221).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_328221).length < 2 ^ (prefixWord ++ tailWord_328221).sum := by decide
  have hdescent : baseEnd_328221 < baseStart_328221 := by decide
  rcases family_descends (prefixWord ++ tailWord_328221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_328231 : List Nat := [1, 1, 7, 2, 1, 2, 1, 5]
def baseStart_328231 : Nat := 118140960795 + 328231 * 2 ^ 59
def prefixEnd_328231 : Nat := 4983230072969 + 3 ^ 40 * 328231 * 2
def baseEnd_328231 : Nat := 49937857394373489897185

theorem tailTrace_328231 : CollatzResearch.WordTrace tailWord_328231 prefixEnd_328231 49937857394373489897185 := by
  unfold tailWord_328231
  simp only [CollatzResearch.WordTrace]
  refine ⟨11971568073882619236952547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7981045382588412824635031 11971568073882619236952547)
  ·
    refine ⟨17957352110823928855428821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11971568073882619236952547 17957352110823928855428821)
    ·
      refine ⟨420875440097435832549113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 17957352110823928855428821 420875440097435832549113)
      ·
        refine ⟨315656580073076874411835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 420875440097435832549113 315656580073076874411835)
        ·
          refine ⟨473484870109615311617753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 315656580073076874411835 473484870109615311617753)
          ·
            refine ⟨355113652582211483713315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 473484870109615311617753 355113652582211483713315)
            ·
              refine ⟨532670478873317225569973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 355113652582211483713315 532670478873317225569973)
              ·
                refine ⟨49937857394373489897185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 532670478873317225569973 49937857394373489897185)
                ·
                  rfl

theorem cell20_328231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 1, 2, 1, 5].length) (baseStart_328231 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_328231 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_328231 prefixEnd_328231 := by exact prefixLift 328231
  have htrace : WordTrace (prefixWord ++ tailWord_328231) baseStart_328231 baseEnd_328231 := by
    simpa [prefixWord, tailWord_328231, baseEnd_328231] using wordTrace_append hprefix tailTrace_328231
  have hstable : (prefixWord ++ tailWord_328231).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_328231).length < 2 ^ (prefixWord ++ tailWord_328231).sum := by decide
  have hdescent : baseEnd_328231 < baseStart_328231 := by decide
  rcases family_descends (prefixWord ++ tailWord_328231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_328242 : List Nat := [3, 2, 1, 1, 2, 1, 4, 3, 3]
def baseStart_328242 : Nat := 118140960795 + 328242 * 2 ^ 59
def prefixEnd_328242 : Nat := 4983230072969 + 3 ^ 40 * 328242 * 2
def baseEnd_328242 : Nat := 149818592882853320324843

theorem tailTrace_328242 : CollatzResearch.WordTrace tailWord_328242 prefixEnd_328242 149818592882853320324843 := by
  unfold tailWord_328242
  simp only [CollatzResearch.WordTrace]
  refine ⟨2992992319210692028900745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7981312851228512077068653 2992992319210692028900745)
  ·
    refine ⟨2244744239408019021675559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2992992319210692028900745 2244744239408019021675559)
    ·
      refine ⟨3367116359112028532513339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2244744239408019021675559 3367116359112028532513339)
      ·
        refine ⟨5050674538668042798770009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3367116359112028532513339 5050674538668042798770009)
        ·
          refine ⟨3788005904001032099077507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5050674538668042798770009 3788005904001032099077507)
          ·
            refine ⟨5682008856001548148616261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3788005904001032099077507 5682008856001548148616261)
            ·
              refine ⟨1065376660500290277865549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5682008856001548148616261 1065376660500290277865549)
              ·
                refine ⟨399516247687608854199581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1065376660500290277865549 399516247687608854199581)
                ·
                  refine ⟨149818592882853320324843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 399516247687608854199581 149818592882853320324843)
                  ·
                    rfl

theorem cell20_328242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 4, 3, 3].length) (baseStart_328242 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_328242 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_328242 prefixEnd_328242 := by exact prefixLift 328242
  have htrace : WordTrace (prefixWord ++ tailWord_328242) baseStart_328242 baseEnd_328242 := by
    simpa [prefixWord, tailWord_328242, baseEnd_328242] using wordTrace_append hprefix tailTrace_328242
  have hstable : (prefixWord ++ tailWord_328242).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_328242).length < 2 ^ (prefixWord ++ tailWord_328242).sum := by decide
  have hdescent : baseEnd_328242 < baseStart_328242 := by decide
  rcases family_descends (prefixWord ++ tailWord_328242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_328249 : List Nat := [1, 2, 1, 5, 1, 1, 3, 2, 4]
def baseStart_328249 : Nat := 118140960795 + 328249 * 2 ^ 59
def prefixEnd_328249 : Nat := 4983230072969 + 3 ^ 40 * 328249 * 2
def baseEnd_328249 : Nat := 149821787873592407091481

theorem tailTrace_328249 : CollatzResearch.WordTrace tailWord_328249 prefixEnd_328249 149821787873592407091481 := by
  unfold tailWord_328249
  simp only [CollatzResearch.WordTrace]
  refine ⟨11972224587817408311107801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7981483058544938874071867 11972224587817408311107801)
  ·
    refine ⟨8979168440863056233330851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11972224587817408311107801 8979168440863056233330851)
    ·
      refine ⟨13468752661294584349996277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8979168440863056233330851 13468752661294584349996277)
      ·
        refine ⟨1262695561996367282812151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 13468752661294584349996277 1262695561996367282812151)
        ·
          refine ⟨1894043342994550924218227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1262695561996367282812151 1894043342994550924218227)
          ·
            refine ⟨2841065014491826386327341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1894043342994550924218227 2841065014491826386327341)
            ·
              refine ⟨1065399380434434894872753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2841065014491826386327341 1065399380434434894872753)
              ·
                refine ⟨799049535325826171154565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1065399380434434894872753 799049535325826171154565)
                ·
                  refine ⟨149821787873592407091481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 799049535325826171154565 149821787873592407091481)
                  ·
                    rfl

theorem cell20_328249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 3, 2, 4].length) (baseStart_328249 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_328249 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_328249 prefixEnd_328249 := by exact prefixLift 328249
  have htrace : WordTrace (prefixWord ++ tailWord_328249) baseStart_328249 baseEnd_328249 := by
    simpa [prefixWord, tailWord_328249, baseEnd_328249] using wordTrace_append hprefix tailTrace_328249
  have hstable : (prefixWord ++ tailWord_328249).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_328249).length < 2 ^ (prefixWord ++ tailWord_328249).sum := by decide
  have hdescent : baseEnd_328249 < baseStart_328249 := by decide
  rcases family_descends (prefixWord ++ tailWord_328249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_328262 : List Nat := [6, 1, 1, 1, 2, 1, 1, 5, 2]
def baseStart_328262 : Nat := 118140960795 + 328262 * 2 ^ 59
def prefixEnd_328262 : Nat := 4983230072969 + 3 ^ 40 * 328262 * 2
def baseEnd_328262 : Nat := 149827721427822139658095

theorem tailTrace_328262 : CollatzResearch.WordTrace tailWord_328262 prefixEnd_328262 149827721427822139658095 := by
  unfold tailWord_328262
  simp only [CollatzResearch.WordTrace]
  refine ⟨374146835524072235354095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 7981799157846874354220693 374146835524072235354095)
  ·
    refine ⟨561220253286108353031143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 374146835524072235354095 561220253286108353031143)
    ·
      refine ⟨841830379929162529546715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 561220253286108353031143 841830379929162529546715)
      ·
        refine ⟨1262745569893743794320073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 841830379929162529546715 1262745569893743794320073)
        ·
          refine ⟨947059177420307845740055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1262745569893743794320073 947059177420307845740055)
          ·
            refine ⟨1420588766130461768610083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 947059177420307845740055 1420588766130461768610083)
            ·
              refine ⟨2130883149195692652915125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1420588766130461768610083 2130883149195692652915125)
              ·
                refine ⟨199770295237096186210793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2130883149195692652915125 199770295237096186210793)
                ·
                  refine ⟨149827721427822139658095, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 199770295237096186210793 149827721427822139658095)
                  ·
                    rfl

theorem cell20_328262_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 1, 5, 2].length) (baseStart_328262 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_328262 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_328262 prefixEnd_328262 := by exact prefixLift 328262
  have htrace : WordTrace (prefixWord ++ tailWord_328262) baseStart_328262 baseEnd_328262 := by
    simpa [prefixWord, tailWord_328262, baseEnd_328262] using wordTrace_append hprefix tailTrace_328262
  have hstable : (prefixWord ++ tailWord_328262).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_328262).length < 2 ^ (prefixWord ++ tailWord_328262).sum := by decide
  have hdescent : baseEnd_328262 < baseStart_328262 := by decide
  rcases family_descends (prefixWord ++ tailWord_328262) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_328266 : List Nat := [3, 1, 2, 1, 1, 4, 1, 5, 2]
def baseStart_328266 : Nat := 118140960795 + 328266 * 2 ^ 59
def prefixEnd_328266 : Nat := 4983230072969 + 3 ^ 40 * 328266 * 2
def baseEnd_328266 : Nat := 149829547136815903524745

theorem tailTrace_328266 : CollatzResearch.WordTrace tailWord_328266 prefixEnd_328266 149829547136815903524745 := by
  unfold tailWord_328266
  simp only [CollatzResearch.WordTrace]
  refine ⟨2993211157188955053619163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7981896419170546809651101 2993211157188955053619163)
  ·
    refine ⟨4489816735783432580428745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2993211157188955053619163 4489816735783432580428745)
    ·
      refine ⟨3367362551837574435321559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4489816735783432580428745 3367362551837574435321559)
      ·
        refine ⟨5051043827756361652982339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3367362551837574435321559 5051043827756361652982339)
        ·
          refine ⟨7576565741634542479473509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5051043827756361652982339 7576565741634542479473509)
          ·
            refine ⟨1420606076556476714901283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7576565741634542479473509 1420606076556476714901283)
            ·
              refine ⟨2130909114834715072351925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1420606076556476714901283 2130909114834715072351925)
              ·
                refine ⟨199772729515754538032993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2130909114834715072351925 199772729515754538032993)
                ·
                  refine ⟨149829547136815903524745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 199772729515754538032993 149829547136815903524745)
                  ·
                    rfl

theorem cell20_328266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 1, 5, 2].length) (baseStart_328266 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_328266 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_328266 prefixEnd_328266 := by exact prefixLift 328266
  have htrace : WordTrace (prefixWord ++ tailWord_328266) baseStart_328266 baseEnd_328266 := by
    simpa [prefixWord, tailWord_328266, baseEnd_328266] using wordTrace_append hprefix tailTrace_328266
  have hstable : (prefixWord ++ tailWord_328266).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_328266).length < 2 ^ (prefixWord ++ tailWord_328266).sum := by decide
  have hdescent : baseEnd_328266 < baseStart_328266 := by decide
  rcases family_descends (prefixWord ++ tailWord_328266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_328280 : List Nat := [2, 1, 2, 2, 1, 2, 5, 2, 3]
def baseStart_328280 : Nat := 118140960795 + 328280 * 2 ^ 59
def prefixEnd_328280 : Nat := 4983230072969 + 3 ^ 40 * 328280 * 2
def baseEnd_328280 : Nat := 149835937118294077058021

theorem tailTrace_328280 : CollatzResearch.WordTrace tailWord_328280 prefixEnd_328280 149835937118294077058021 := by
  unfold tailWord_328280
  simp only [CollatzResearch.WordTrace]
  refine ⟨5986677625352550302743147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7982236833803400403657529 5986677625352550302743147)
  ·
    refine ⟨8980016438028825454114721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5986677625352550302743147 8980016438028825454114721)
    ·
      refine ⟨6735012328521619090586041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8980016438028825454114721 6735012328521619090586041)
      ·
        refine ⟨5051259246391214317939531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6735012328521619090586041 5051259246391214317939531)
        ·
          refine ⟨7576888869586821476909297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5051259246391214317939531 7576888869586821476909297)
          ·
            refine ⟨5682666652190116107681973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7576888869586821476909297 5682666652190116107681973)
            ·
              refine ⟨532749998642823385095185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 5682666652190116107681973 532749998642823385095185)
              ·
                refine ⟨399562498982117538821389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 532749998642823385095185 399562498982117538821389)
                ·
                  refine ⟨149835937118294077058021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 399562498982117538821389 149835937118294077058021)
                  ·
                    rfl

theorem cell20_328280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 5, 2, 3].length) (baseStart_328280 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_328280 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_328280 prefixEnd_328280 := by exact prefixLift 328280
  have htrace : WordTrace (prefixWord ++ tailWord_328280) baseStart_328280 baseEnd_328280 := by
    simpa [prefixWord, tailWord_328280, baseEnd_328280] using wordTrace_append hprefix tailTrace_328280
  have hstable : (prefixWord ++ tailWord_328280).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_328280).length < 2 ^ (prefixWord ++ tailWord_328280).sum := by decide
  have hdescent : baseEnd_328280 < baseStart_328280 := by decide
  rcases family_descends (prefixWord ++ tailWord_328280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_328338 : List Nat := [3, 2, 3, 1, 2, 2, 3, 2, 2]
def baseStart_328338 : Nat := 118140960795 + 328338 * 2 ^ 59
def prefixEnd_328338 : Nat := 4983230072969 + 3 ^ 40 * 328338 * 2
def baseEnd_328338 : Nat := 149862409898703653124451

theorem tailTrace_328338 : CollatzResearch.WordTrace tailWord_328338 prefixEnd_328338 149862409898703653124451 := by
  unfold tailWord_328338
  simp only [CollatzResearch.WordTrace]
  refine ⟨2993867671123744127774417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7983647122996651007398445 2993867671123744127774417)
  ·
    refine ⟨2245400753342808095830813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2993867671123744127774417 2245400753342808095830813)
    ·
      refine ⟨842025282503553035936555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2245400753342808095830813 842025282503553035936555)
      ·
        refine ⟨1263037923755329553904833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 842025282503553035936555 1263037923755329553904833)
        ·
          refine ⟨947278442816497165428625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1263037923755329553904833 947278442816497165428625)
          ·
            refine ⟨710458832112372874071469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 947278442816497165428625 710458832112372874071469)
            ·
              refine ⟨266422062042139827776801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 710458832112372874071469 266422062042139827776801)
              ·
                refine ⟨199816546531604870832601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 266422062042139827776801 199816546531604870832601)
                ·
                  refine ⟨149862409898703653124451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 199816546531604870832601 149862409898703653124451)
                  ·
                    rfl

theorem cell20_328338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 2, 3, 2, 2].length) (baseStart_328338 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_328338 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_328338 prefixEnd_328338 := by exact prefixLift 328338
  have htrace : WordTrace (prefixWord ++ tailWord_328338) baseStart_328338 baseEnd_328338 := by
    simpa [prefixWord, tailWord_328338, baseEnd_328338] using wordTrace_append hprefix tailTrace_328338
  have hstable : (prefixWord ++ tailWord_328338).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_328338).length < 2 ^ (prefixWord ++ tailWord_328338).sum := by decide
  have hdescent : baseEnd_328338 < baseStart_328338 := by decide
  rcases family_descends (prefixWord ++ tailWord_328338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_328352 : List Nat := [2, 1, 1, 4, 4, 2, 2, 1, 3]
def baseStart_328352 : Nat := 118140960795 + 328352 * 2 ^ 59
def prefixEnd_328352 : Nat := 4983230072969 + 3 ^ 40 * 328352 * 2
def baseEnd_328352 : Nat := 149868799880181826657727

theorem tailTrace_328352 : CollatzResearch.WordTrace tailWord_328352 prefixEnd_328352 149868799880181826657727 := by
  unfold tailWord_328352
  simp only [CollatzResearch.WordTrace]
  refine ⟨5987990653222128451053655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7983987537629504601404873 5987990653222128451053655)
  ·
    refine ⟨8981985979833192676580483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5987990653222128451053655 8981985979833192676580483)
    ·
      refine ⟨13472978969749789014870725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8981985979833192676580483 13472978969749789014870725)
      ·
        refine ⟨2526183556828085440288261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 13472978969749789014870725 2526183556828085440288261)
        ·
          refine ⟨473659416905266020054049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2526183556828085440288261 473659416905266020054049)
          ·
            refine ⟨355244562678949515040537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 473659416905266020054049 355244562678949515040537)
            ·
              refine ⟨266433422009212136280403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 355244562678949515040537 266433422009212136280403)
              ·
                refine ⟨399650133013818204420605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 266433422009212136280403 399650133013818204420605)
                ·
                  refine ⟨149868799880181826657727, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 399650133013818204420605 149868799880181826657727)
                  ·
                    rfl

theorem cell20_328352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 4, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 4, 2, 2, 1, 3].length) (baseStart_328352 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_328352 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_328352 prefixEnd_328352 := by exact prefixLift 328352
  have htrace : WordTrace (prefixWord ++ tailWord_328352) baseStart_328352 baseEnd_328352 := by
    simpa [prefixWord, tailWord_328352, baseEnd_328352] using wordTrace_append hprefix tailTrace_328352
  have hstable : (prefixWord ++ tailWord_328352).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_328352).length < 2 ^ (prefixWord ++ tailWord_328352).sum := by decide
  have hdescent : baseEnd_328352 < baseStart_328352 := by decide
  rcases family_descends (prefixWord ++ tailWord_328352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_328356 : List Nat := [2, 3, 1, 2, 2, 1, 3, 3, 3]
def baseStart_328356 : Nat := 118140960795 + 328356 * 2 ^ 59
def prefixEnd_328356 : Nat := 4983230072969 + 3 ^ 40 * 328356 * 2
def baseEnd_328356 : Nat := 149870625589175590524377

theorem tailTrace_328356 : CollatzResearch.WordTrace tailWord_328356 prefixEnd_328356 149870625589175590524377 := by
  unfold tailWord_328356
  simp only [CollatzResearch.WordTrace]
  refine ⟨5988063599214882792626461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7984084798953177056835281 5988063599214882792626461)
  ·
    refine ⟨2245523849705581047234923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5988063599214882792626461 2245523849705581047234923)
    ·
      refine ⟨3368285774558371570852385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2245523849705581047234923 3368285774558371570852385)
      ·
        refine ⟨2526214330918778678139289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3368285774558371570852385 2526214330918778678139289)
        ·
          refine ⟨1894660748189084008604467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2526214330918778678139289 1894660748189084008604467)
          ·
            refine ⟨2841991122283626012906701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1894660748189084008604467 2841991122283626012906701)
            ·
              refine ⟨1065746670856359754840013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2841991122283626012906701 1065746670856359754840013)
              ·
                refine ⟨399655001571134908065005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1065746670856359754840013 399655001571134908065005)
                ·
                  refine ⟨149870625589175590524377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 399655001571134908065005 149870625589175590524377)
                  ·
                    rfl

theorem cell20_328356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 3, 3, 3].length) (baseStart_328356 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_328356 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_328356 prefixEnd_328356 := by exact prefixLift 328356
  have htrace : WordTrace (prefixWord ++ tailWord_328356) baseStart_328356 baseEnd_328356 := by
    simpa [prefixWord, tailWord_328356, baseEnd_328356] using wordTrace_append hprefix tailTrace_328356
  have hstable : (prefixWord ++ tailWord_328356).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_328356).length < 2 ^ (prefixWord ++ tailWord_328356).sum := by decide
  have hdescent : baseEnd_328356 < baseStart_328356 := by decide
  rcases family_descends (prefixWord ++ tailWord_328356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_328380 : List Nat := [2, 2, 2, 3, 1, 1, 2, 5, 2]
def baseStart_328380 : Nat := 118140960795 + 328380 * 2 ^ 59
def prefixEnd_328380 : Nat := 4983230072969 + 3 ^ 40 * 328380 * 2
def baseEnd_328380 : Nat := 149881579843138173724279

theorem tailTrace_328380 : CollatzResearch.WordTrace tailWord_328380 prefixEnd_328380 149881579843138173724279 := by
  unfold tailWord_328380
  simp only [CollatzResearch.WordTrace]
  refine ⟨5988501275171408842063297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7984668366895211789417729 5988501275171408842063297)
  ·
    refine ⟨4491375956378556631547473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5988501275171408842063297 4491375956378556631547473)
    ·
      refine ⟨3368531967283917473660605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4491375956378556631547473 3368531967283917473660605)
      ·
        refine ⟨1263199487731469052622727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3368531967283917473660605 1263199487731469052622727)
        ·
          refine ⟨1894799231597203578934091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1263199487731469052622727 1894799231597203578934091)
          ·
            refine ⟨2842198847395805368401137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1894799231597203578934091 2842198847395805368401137)
            ·
              refine ⟨2131649135546854026300853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2842198847395805368401137 2131649135546854026300853)
              ·
                refine ⟨199842106457517564965705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2131649135546854026300853 199842106457517564965705)
                ·
                  refine ⟨149881579843138173724279, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 199842106457517564965705 149881579843138173724279)
                  ·
                    rfl

theorem cell20_328380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 2, 5, 2].length) (baseStart_328380 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_328380 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_328380 prefixEnd_328380 := by exact prefixLift 328380
  have htrace : WordTrace (prefixWord ++ tailWord_328380) baseStart_328380 baseEnd_328380 := by
    simpa [prefixWord, tailWord_328380, baseEnd_328380] using wordTrace_append hprefix tailTrace_328380
  have hstable : (prefixWord ++ tailWord_328380).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_328380).length < 2 ^ (prefixWord ++ tailWord_328380).sum := by decide
  have hdescent : baseEnd_328380 < baseStart_328380 := by decide
  rcases family_descends (prefixWord ++ tailWord_328380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_328394 : List Nat := [3, 1, 2, 1, 4, 1, 1, 4, 3]
def baseStart_328394 : Nat := 118140960795 + 328394 * 2 ^ 59
def prefixEnd_328394 : Nat := 4983230072969 + 3 ^ 40 * 328394 * 2
def baseEnd_328394 : Nat := 149887969824616347257555

theorem tailTrace_328394 : CollatzResearch.WordTrace tailWord_328394 prefixEnd_328394 149887969824616347257555 := by
  unfold tailWord_328394
  simp only [CollatzResearch.WordTrace]
  refine ⟨2994378293073024518784059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7985008781528065383424157 2994378293073024518784059)
  ·
    refine ⟨4491567439609536778176089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2994378293073024518784059 4491567439609536778176089)
    ·
      refine ⟨3368675579707152583632067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4491567439609536778176089 3368675579707152583632067)
      ·
        refine ⟨5053013369560728875448101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3368675579707152583632067 5053013369560728875448101)
        ·
          refine ⟨947440006792636664146519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5053013369560728875448101 947440006792636664146519)
          ·
            refine ⟨1421160010188954996219779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 947440006792636664146519 1421160010188954996219779)
            ·
              refine ⟨2131740015283432494329669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1421160010188954996219779 2131740015283432494329669)
              ·
                refine ⟨399701252865643592686813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2131740015283432494329669 399701252865643592686813)
                ·
                  refine ⟨149887969824616347257555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 399701252865643592686813 149887969824616347257555)
                  ·
                    rfl

theorem cell20_328394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 1, 4, 3].length) (baseStart_328394 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_328394 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_328394 prefixEnd_328394 := by exact prefixLift 328394
  have htrace : WordTrace (prefixWord ++ tailWord_328394) baseStart_328394 baseEnd_328394 := by
    simpa [prefixWord, tailWord_328394, baseEnd_328394] using wordTrace_append hprefix tailTrace_328394
  have hstable : (prefixWord ++ tailWord_328394).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_328394).length < 2 ^ (prefixWord ++ tailWord_328394).sum := by decide
  have hdescent : baseEnd_328394 < baseStart_328394 := by decide
  rcases family_descends (prefixWord ++ tailWord_328394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_328404 : List Nat := [2, 4, 1, 3, 2, 2, 1, 5]
def baseStart_328404 : Nat := 118140960795 + 328404 * 2 ^ 59
def prefixEnd_328404 : Nat := 4983230072969 + 3 ^ 40 * 328404 * 2
def baseEnd_328404 : Nat := 49964178032366918974727

theorem tailTrace_328404 : CollatzResearch.WordTrace tailWord_328404 prefixEnd_328404 49964178032366918974727 := by
  unfold tailWord_328404
  simp only [CollatzResearch.WordTrace]
  refine ⟨5988938951127934891500133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7985251934837246522000177 5988938951127934891500133)
  ·
    refine ⟨1122926053336487792156275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5988938951127934891500133 1122926053336487792156275)
    ·
      refine ⟨1684389080004731688234413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1122926053336487792156275 1684389080004731688234413)
      ·
        refine ⟨631645905001774383087905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1684389080004731688234413 631645905001774383087905)
        ·
          refine ⟨473734428751330787315929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 631645905001774383087905 473734428751330787315929)
          ·
            refine ⟨355300821563498090486947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 473734428751330787315929 355300821563498090486947)
            ·
              refine ⟨532951232345247135730421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 355300821563498090486947 532951232345247135730421)
              ·
                refine ⟨49964178032366918974727, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 532951232345247135730421 49964178032366918974727)
                ·
                  rfl

theorem cell20_328404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 2, 2, 1, 5].length) (baseStart_328404 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_328404 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_328404 prefixEnd_328404 := by exact prefixLift 328404
  have htrace : WordTrace (prefixWord ++ tailWord_328404) baseStart_328404 baseEnd_328404 := by
    simpa [prefixWord, tailWord_328404, baseEnd_328404] using wordTrace_append hprefix tailTrace_328404
  have hstable : (prefixWord ++ tailWord_328404).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_328404).length < 2 ^ (prefixWord ++ tailWord_328404).sum := by decide
  have hdescent : baseEnd_328404 < baseStart_328404 := by decide
  rcases family_descends (prefixWord ++ tailWord_328404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan20Incremental
