import V185TrunkScan23Chunk0223

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_1324648 : List Nat := [2, 1, 4, 3, 1, 1, 3, 2, 1, 2, 3]
def baseStart_1324648 : Nat := 118140960795 + 1324648 * 2 ^ 59
def prefixEnd_1324648 : Nat := 4983230072969 + 3 ^ 40 * 1324648 * 2
def baseEnd_1324648 : Nat := 680181122017038542308061

theorem tailTrace_1324648 : CollatzResearch.WordTrace tailWord_1324648 prefixEnd_1324648 680181122017038542308061 := by
  unfold tailWord_1324648
  simp only [CollatzResearch.WordTrace]
  refine ⟨24156940852517001356135299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32209254470022668474847065 24156940852517001356135299)
  ·
    refine ⟨36235411278775502034202949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24156940852517001356135299 36235411278775502034202949)
    ·
      refine ⟨6794139614770406631413053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 36235411278775502034202949 6794139614770406631413053)
      ·
        refine ⟨2547802355538902486779895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6794139614770406631413053 2547802355538902486779895)
        ·
          refine ⟨3821703533308353730169843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2547802355538902486779895 3821703533308353730169843)
          ·
            refine ⟨5732555299962530595254765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3821703533308353730169843 5732555299962530595254765)
            ·
              refine ⟨2149708237485948973220537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5732555299962530595254765 2149708237485948973220537)
              ·
                refine ⟨1612281178114461729915403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2149708237485948973220537 1612281178114461729915403)
                ·
                  refine ⟨2418421767171692594873105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1612281178114461729915403 2418421767171692594873105)
                  ·
                    refine ⟨1813816325378769446154829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2418421767171692594873105 1813816325378769446154829)
                    ·
                      refine ⟨680181122017038542308061, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1813816325378769446154829 680181122017038542308061)
                      ·
                        rfl

theorem cell23_1324648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 3, 2, 1, 2, 3].length) (baseStart_1324648 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1324648 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1324648 prefixEnd_1324648 := by exact prefixLift 1324648
  have htrace : WordTrace (prefixWord ++ tailWord_1324648) baseStart_1324648 baseEnd_1324648 := by
    simpa [prefixWord, tailWord_1324648, baseEnd_1324648] using wordTrace_append hprefix tailTrace_1324648
  have hstable : (prefixWord ++ tailWord_1324648).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1324648).length < 2 ^ (prefixWord ++ tailWord_1324648).sum := by decide
  have hdescent : baseEnd_1324648 < baseStart_1324648 := by decide
  rcases family_descends (prefixWord ++ tailWord_1324648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1324657 : List Nat := [1, 2, 2, 2, 1, 1, 1, 3, 1, 4, 5]
def baseStart_1324657 : Nat := 118140960795 + 1324657 * 2 ^ 59
def prefixEnd_1324657 : Nat := 4983230072969 + 3 ^ 40 * 1324657 * 2
def baseEnd_1324657 : Nat := 680185743342929007095519

theorem tailTrace_1324657 : CollatzResearch.WordTrace tailWord_1324657 prefixEnd_1324657 680185743342929007095519 := by
  unfold tailWord_1324657
  simp only [CollatzResearch.WordTrace]
  refine ⟨48314209962001397249348225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32209473308000931499565483 48314209962001397249348225)
  ·
    refine ⟨36235657471501047937011169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48314209962001397249348225 36235657471501047937011169)
    ·
      refine ⟨27176743103625785952758377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36235657471501047937011169 27176743103625785952758377)
      ·
        refine ⟨20382557327719339464568783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27176743103625785952758377 20382557327719339464568783)
        ·
          refine ⟨30573835991579009196853175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20382557327719339464568783 30573835991579009196853175)
          ·
            refine ⟨45860753987368513795279763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30573835991579009196853175 45860753987368513795279763)
            ·
              refine ⟨68791130981052770692919645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45860753987368513795279763 68791130981052770692919645)
              ·
                refine ⟨25796674117894789009844867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 68791130981052770692919645 25796674117894789009844867)
                ·
                  refine ⟨38695011176842183514767301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25796674117894789009844867 38695011176842183514767301)
                  ·
                    refine ⟨7255314595657909409018869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 38695011176842183514767301 7255314595657909409018869)
                    ·
                      refine ⟨680185743342929007095519, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7255314595657909409018869 680185743342929007095519)
                      ·
                        rfl

theorem cell23_1324657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 3, 1, 4, 5].length) (baseStart_1324657 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1324657 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1324657 prefixEnd_1324657 := by exact prefixLift 1324657
  have htrace : WordTrace (prefixWord ++ tailWord_1324657) baseStart_1324657 baseEnd_1324657 := by
    simpa [prefixWord, tailWord_1324657, baseEnd_1324657] using wordTrace_append hprefix tailTrace_1324657
  have hstable : (prefixWord ++ tailWord_1324657).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1324657).length < 2 ^ (prefixWord ++ tailWord_1324657).sum := by decide
  have hdescent : baseEnd_1324657 < baseStart_1324657 := by decide
  rcases family_descends (prefixWord ++ tailWord_1324657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1324661 : List Nat := [1, 3, 4, 2, 1, 1, 1, 1, 3, 3, 3]
def baseStart_1324661 : Nat := 118140960795 + 1324661 * 2 ^ 59
def prefixEnd_1324661 : Nat := 4983230072969 + 3 ^ 40 * 1324661 * 2
def baseEnd_1324661 : Nat := 680187797265546991445501

theorem tailTrace_1324661 : CollatzResearch.WordTrace tailWord_1324661 prefixEnd_1324661 680187797265546991445501 := by
  unfold tailWord_1324661
  simp only [CollatzResearch.WordTrace]
  refine ⟨48314355853986905932493837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32209570569324603954995891 48314355853986905932493837)
  ·
    refine ⟨18117883445245089724685189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 48314355853986905932493837 18117883445245089724685189)
    ·
      refine ⟨3397103145983454323378473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 18117883445245089724685189 3397103145983454323378473)
      ·
        refine ⟨2547827359487590742533855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3397103145983454323378473 2547827359487590742533855)
        ·
          refine ⟨3821741039231386113800783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2547827359487590742533855 3821741039231386113800783)
          ·
            refine ⟨5732611558847079170701175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3821741039231386113800783 5732611558847079170701175)
            ·
              refine ⟨8598917338270618756051763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5732611558847079170701175 8598917338270618756051763)
              ·
                refine ⟨12898376007405928134077645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8598917338270618756051763 12898376007405928134077645)
                ·
                  refine ⟨4836891002777223050279117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12898376007405928134077645 4836891002777223050279117)
                  ·
                    refine ⟨1813834126041458643854669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4836891002777223050279117 1813834126041458643854669)
                    ·
                      refine ⟨680187797265546991445501, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1813834126041458643854669 680187797265546991445501)
                      ·
                        rfl

theorem cell23_1324661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 1, 1, 3, 3, 3].length) (baseStart_1324661 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1324661 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1324661 prefixEnd_1324661 := by exact prefixLift 1324661
  have htrace : WordTrace (prefixWord ++ tailWord_1324661) baseStart_1324661 baseEnd_1324661 := by
    simpa [prefixWord, tailWord_1324661, baseEnd_1324661] using wordTrace_append hprefix tailTrace_1324661
  have hstable : (prefixWord ++ tailWord_1324661).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1324661).length < 2 ^ (prefixWord ++ tailWord_1324661).sum := by decide
  have hdescent : baseEnd_1324661 < baseStart_1324661 := by decide
  rcases family_descends (prefixWord ++ tailWord_1324661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1324791 : List Nat := [1, 1, 3, 1, 1, 1, 4, 1, 4, 4, 2]
def baseStart_1324791 : Nat := 118140960795 + 1324791 * 2 ^ 59
def prefixEnd_1324791 : Nat := 4983230072969 + 3 ^ 40 * 1324791 * 2
def baseEnd_1324791 : Nat := 680254549750631482819903

theorem tailTrace_1324791 : CollatzResearch.WordTrace tailWord_1324791 prefixEnd_1324791 680254549750631482819903 := by
  unfold tailWord_1324791
  simp only [CollatzResearch.WordTrace]
  refine ⟨48319097343515938134726227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32212731562343958756484151 48319097343515938134726227)
  ·
    refine ⟨72478646015273907202089341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48319097343515938134726227 72478646015273907202089341)
    ·
      refine ⟨27179492255727715200783503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 72478646015273907202089341 27179492255727715200783503)
      ·
        refine ⟨40769238383591572801175255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27179492255727715200783503 40769238383591572801175255)
        ·
          refine ⟨61153857575387359201762883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40769238383591572801175255 61153857575387359201762883)
          ·
            refine ⟨91730786363081038802644325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61153857575387359201762883 91730786363081038802644325)
            ·
              refine ⟨17199522443077694775495811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 91730786363081038802644325 17199522443077694775495811)
              ·
                refine ⟨25799283664616542163243717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17199522443077694775495811 25799283664616542163243717)
                ·
                  refine ⟨4837365687115601655608197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 25799283664616542163243717 4837365687115601655608197)
                  ·
                    refine ⟨907006066334175310426537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4837365687115601655608197 907006066334175310426537)
                    ·
                      refine ⟨680254549750631482819903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 907006066334175310426537 680254549750631482819903)
                      ·
                        rfl

theorem cell23_1324791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 4, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 4, 1, 4, 4, 2].length) (baseStart_1324791 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1324791 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1324791 prefixEnd_1324791 := by exact prefixLift 1324791
  have htrace : WordTrace (prefixWord ++ tailWord_1324791) baseStart_1324791 baseEnd_1324791 := by
    simpa [prefixWord, tailWord_1324791, baseEnd_1324791] using wordTrace_append hprefix tailTrace_1324791
  have hstable : (prefixWord ++ tailWord_1324791).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1324791).length < 2 ^ (prefixWord ++ tailWord_1324791).sum := by decide
  have hdescent : baseEnd_1324791 < baseStart_1324791 := by decide
  rcases family_descends (prefixWord ++ tailWord_1324791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1324798 : List Nat := [4, 2, 2, 1, 3, 1, 1, 1, 1, 2, 5]
def baseStart_1324798 : Nat := 118140960795 + 1324798 * 2 ^ 59
def prefixEnd_1324798 : Nat := 4983230072969 + 3 ^ 40 * 1324798 * 2
def baseEnd_1324798 : Nat := 680258144115212955432371

theorem tailTrace_1324798 : CollatzResearch.WordTrace tailWord_1324798 prefixEnd_1324798 680258144115212955432371 := by
  unfold tailWord_1324798
  simp only [CollatzResearch.WordTrace]
  refine ⟨6039919081811322291278881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 32212901769660385553487365 6039919081811322291278881)
  ·
    refine ⟨4529939311358491718459161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6039919081811322291278881 4529939311358491718459161)
    ·
      refine ⟨3397454483518868788844371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4529939311358491718459161 3397454483518868788844371)
      ·
        refine ⟨5096181725278303183266557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3397454483518868788844371 5096181725278303183266557)
        ·
          refine ⟨1911068146979363693724959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5096181725278303183266557 1911068146979363693724959)
          ·
            refine ⟨2866602220469045540587439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1911068146979363693724959 2866602220469045540587439)
            ·
              refine ⟨4299903330703568310881159, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2866602220469045540587439 4299903330703568310881159)
              ·
                refine ⟨6449854996055352466321739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4299903330703568310881159 6449854996055352466321739)
                ·
                  refine ⟨9674782494083028699482609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6449854996055352466321739 9674782494083028699482609)
                  ·
                    refine ⟨7256086870562271524611957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9674782494083028699482609 7256086870562271524611957)
                    ·
                      refine ⟨680258144115212955432371, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7256086870562271524611957 680258144115212955432371)
                      ·
                        rfl

theorem cell23_1324798_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 3, 1, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 3, 1, 1, 1, 1, 2, 5].length) (baseStart_1324798 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1324798 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1324798 prefixEnd_1324798 := by exact prefixLift 1324798
  have htrace : WordTrace (prefixWord ++ tailWord_1324798) baseStart_1324798 baseEnd_1324798 := by
    simpa [prefixWord, tailWord_1324798, baseEnd_1324798] using wordTrace_append hprefix tailTrace_1324798
  have hstable : (prefixWord ++ tailWord_1324798).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1324798).length < 2 ^ (prefixWord ++ tailWord_1324798).sum := by decide
  have hdescent : baseEnd_1324798 < baseStart_1324798 := by decide
  rcases family_descends (prefixWord ++ tailWord_1324798) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1324828 : List Nat := [2, 2, 3, 1, 1, 2, 4, 1, 2, 2, 3]
def baseStart_1324828 : Nat := 118140960795 + 1324828 * 2 ^ 59
def prefixEnd_1324828 : Nat := 4983230072969 + 3 ^ 40 * 1324828 * 2
def baseEnd_1324828 : Nat := 680273548534847838057233

theorem tailTrace_1324828 : CollatzResearch.WordTrace tailWord_1324828 prefixEnd_1324828 680273548534847838057233 := by
  unfold tailWord_1324828
  simp only [CollatzResearch.WordTrace]
  refine ⟨24160223422190946726911569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32213631229587928969215425 24160223422190946726911569)
  ·
    refine ⟨18120167566643210045183677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24160223422190946726911569 18120167566643210045183677)
    ·
      refine ⟨6795062837491203766943879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18120167566643210045183677 6795062837491203766943879)
      ·
        refine ⟨10192594256236805650415819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6795062837491203766943879 10192594256236805650415819)
        ·
          refine ⟨15288891384355208475623729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10192594256236805650415819 15288891384355208475623729)
          ·
            refine ⟨11466668538266406356717797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15288891384355208475623729 11466668538266406356717797)
            ·
              refine ⟨2150000350924951191884587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11466668538266406356717797 2150000350924951191884587)
              ·
                refine ⟨3225000526387426787826881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2150000350924951191884587 3225000526387426787826881)
                ·
                  refine ⟨2418750394790570090870161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3225000526387426787826881 2418750394790570090870161)
                  ·
                    refine ⟨1814062796092927568152621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2418750394790570090870161 1814062796092927568152621)
                    ·
                      refine ⟨680273548534847838057233, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1814062796092927568152621 680273548534847838057233)
                      ·
                        rfl

theorem cell23_1324828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 4, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 4, 1, 2, 2, 3].length) (baseStart_1324828 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1324828 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1324828 prefixEnd_1324828 := by exact prefixLift 1324828
  have htrace : WordTrace (prefixWord ++ tailWord_1324828) baseStart_1324828 baseEnd_1324828 := by
    simpa [prefixWord, tailWord_1324828, baseEnd_1324828] using wordTrace_append hprefix tailTrace_1324828
  have hstable : (prefixWord ++ tailWord_1324828).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1324828).length < 2 ^ (prefixWord ++ tailWord_1324828).sum := by decide
  have hdescent : baseEnd_1324828 < baseStart_1324828 := by decide
  rcases family_descends (prefixWord ++ tailWord_1324828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1324852 : List Nat := [2, 5, 1, 1, 2, 2, 1, 4, 1, 4]
def baseStart_1324852 : Nat := 118140960795 + 1324852 * 2 ^ 59
def prefixEnd_1324852 : Nat := 4983230072969 + 3 ^ 40 * 1324852 * 2
def baseEnd_1324852 : Nat := 226761957356851914719041

theorem tailTrace_1324852 : CollatzResearch.WordTrace tailWord_1324852 prefixEnd_1324852 226761957356851914719041 := by
  unfold tailWord_1324852
  simp only [CollatzResearch.WordTrace]
  refine ⟨24160661098147472776348405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32214214797529963701797873 24160661098147472776348405)
  ·
    refine ⟨2265061977951325572782663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 24160661098147472776348405 2265061977951325572782663)
    ·
      refine ⟨3397592966926988359173995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2265061977951325572782663 3397592966926988359173995)
      ·
        refine ⟨5096389450390482538760993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3397592966926988359173995 5096389450390482538760993)
        ·
          refine ⟨3822292087792861904070745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5096389450390482538760993 3822292087792861904070745)
          ·
            refine ⟨2866719065844646428053059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3822292087792861904070745 2866719065844646428053059)
            ·
              refine ⟨4300078598766969642079589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2866719065844646428053059 4300078598766969642079589)
              ·
                refine ⟨806264737268806807889923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4300078598766969642079589 806264737268806807889923)
                ·
                  refine ⟨1209397105903210211834885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 806264737268806807889923 1209397105903210211834885)
                  ·
                    refine ⟨226761957356851914719041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1209397105903210211834885 226761957356851914719041)
                    ·
                      rfl

theorem cell23_1324852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 2, 1, 4, 1, 4].length) (baseStart_1324852 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1324852 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1324852 prefixEnd_1324852 := by exact prefixLift 1324852
  have htrace : WordTrace (prefixWord ++ tailWord_1324852) baseStart_1324852 baseEnd_1324852 := by
    simpa [prefixWord, tailWord_1324852, baseEnd_1324852] using wordTrace_append hprefix tailTrace_1324852
  have hstable : (prefixWord ++ tailWord_1324852).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1324852).length < 2 ^ (prefixWord ++ tailWord_1324852).sum := by decide
  have hdescent : baseEnd_1324852 < baseStart_1324852 := by decide
  rcases family_descends (prefixWord ++ tailWord_1324852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1324885 : List Nat := [1, 3, 2, 2, 2, 2, 3, 1, 2, 3, 2]
def baseStart_1324885 : Nat := 118140960795 + 1324885 * 2 ^ 59
def prefixEnd_1324885 : Nat := 4983230072969 + 3 ^ 40 * 1324885 * 2
def baseEnd_1324885 : Nat := 680302816932154115044471

theorem tailTrace_1324885 : CollatzResearch.WordTrace tailWord_1324885 prefixEnd_1324885 680302816932154115044471 := by
  unfold tailWord_1324885
  simp only [CollatzResearch.WordTrace]
  refine ⟨48322525805175392188648109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32215017203450261459098739 48322525805175392188648109)
  ·
    refine ⟨18120947176940772070743041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 48322525805175392188648109 18120947176940772070743041)
    ·
      refine ⟨13590710382705579053057281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18120947176940772070743041 13590710382705579053057281)
      ·
        refine ⟨10193032787029184289792961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13590710382705579053057281 10193032787029184289792961)
        ·
          refine ⟨7644774590271888217344721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10193032787029184289792961 7644774590271888217344721)
          ·
            refine ⟨5733580942703916163008541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7644774590271888217344721 5733580942703916163008541)
            ·
              refine ⟨2150092853513968561128203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5733580942703916163008541 2150092853513968561128203)
              ·
                refine ⟨3225139280270952841692305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2150092853513968561128203 3225139280270952841692305)
                ·
                  refine ⟨2418854460203214631269229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3225139280270952841692305 2418854460203214631269229)
                  ·
                    refine ⟨907070422576205486725961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2418854460203214631269229 907070422576205486725961)
                    ·
                      refine ⟨680302816932154115044471, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 907070422576205486725961 680302816932154115044471)
                      ·
                        rfl

theorem cell23_1324885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 3, 1, 2, 3, 2].length) (baseStart_1324885 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1324885 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1324885 prefixEnd_1324885 := by exact prefixLift 1324885
  have htrace : WordTrace (prefixWord ++ tailWord_1324885) baseStart_1324885 baseEnd_1324885 := by
    simpa [prefixWord, tailWord_1324885, baseEnd_1324885] using wordTrace_append hprefix tailTrace_1324885
  have hstable : (prefixWord ++ tailWord_1324885).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1324885).length < 2 ^ (prefixWord ++ tailWord_1324885).sum := by decide
  have hdescent : baseEnd_1324885 < baseStart_1324885 := by decide
  rcases family_descends (prefixWord ++ tailWord_1324885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1324895 : List Nat := [1, 1, 2, 3, 1, 6, 2, 1, 1, 5]
def baseStart_1324895 : Nat := 118140960795 + 1324895 * 2 ^ 59
def prefixEnd_1324895 : Nat := 4983230072969 + 3 ^ 40 * 1324895 * 2
def baseEnd_1324895 : Nat := 226769317246233025306475

theorem tailTrace_1324895 : CollatzResearch.WordTrace tailWord_1324895 prefixEnd_1324895 226769317246233025306475 := by
  unfold tailWord_1324895
  simp only [CollatzResearch.WordTrace]
  refine ⟨48322890535139163896512139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32215260356759442597674759 48322890535139163896512139)
  ·
    refine ⟨72484335802708745844768209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48322890535139163896512139 72484335802708745844768209)
    ·
      refine ⟨54363251852031559383576157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 72484335802708745844768209 54363251852031559383576157)
      ·
        refine ⟨20386219444511834768841059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 54363251852031559383576157 20386219444511834768841059)
        ·
          refine ⟨30579329166767752153261589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20386219444511834768841059 30579329166767752153261589)
          ·
            refine ⟨1433406054692238382184137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 30579329166767752153261589 1433406054692238382184137)
            ·
              refine ⟨1075054541019178786638103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1433406054692238382184137 1075054541019178786638103)
              ·
                refine ⟨1612581811528768179957155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1075054541019178786638103 1612581811528768179957155)
                ·
                  refine ⟨2418872717293152269935733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1612581811528768179957155 2418872717293152269935733)
                  ·
                    refine ⟨226769317246233025306475, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2418872717293152269935733 226769317246233025306475)
                    ·
                      rfl

theorem cell23_1324895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 6, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 6, 2, 1, 1, 5].length) (baseStart_1324895 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1324895 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1324895 prefixEnd_1324895 := by exact prefixLift 1324895
  have htrace : WordTrace (prefixWord ++ tailWord_1324895) baseStart_1324895 baseEnd_1324895 := by
    simpa [prefixWord, tailWord_1324895, baseEnd_1324895] using wordTrace_append hprefix tailTrace_1324895
  have hstable : (prefixWord ++ tailWord_1324895).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1324895).length < 2 ^ (prefixWord ++ tailWord_1324895).sum := by decide
  have hdescent : baseEnd_1324895 < baseStart_1324895 := by decide
  rcases family_descends (prefixWord ++ tailWord_1324895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1324901 : List Nat := [1, 3, 1, 3, 1, 1, 1, 5, 1, 1, 5]
def baseStart_1324901 : Nat := 118140960795 + 1324901 * 2 ^ 59
def prefixEnd_1324901 : Nat := 4983230072969 + 3 ^ 40 * 1324901 * 2
def baseEnd_1324901 : Nat := 680311032622626052444397

theorem tailTrace_1324901 : CollatzResearch.WordTrace tailWord_1324901 prefixEnd_1324901 680311032622626052444397 := by
  unfold tailWord_1324901
  simp only [CollatzResearch.WordTrace]
  refine ⟨48323109373117426921230557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32215406248744951280820371 48323109373117426921230557)
  ·
    refine ⟨18121166014919035095461459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 48323109373117426921230557 18121166014919035095461459)
    ·
      refine ⟨27181749022378552643192189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18121166014919035095461459 27181749022378552643192189)
      ·
        refine ⟨10193155883391957241197071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27181749022378552643192189 10193155883391957241197071)
        ·
          refine ⟨15289733825087935861795607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10193155883391957241197071 15289733825087935861795607)
          ·
            refine ⟨22934600737631903792693411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15289733825087935861795607 22934600737631903792693411)
            ·
              refine ⟨34401901106447855689040117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22934600737631903792693411 34401901106447855689040117)
              ·
                refine ⟨3225178228729486470847511, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 34401901106447855689040117 3225178228729486470847511)
                ·
                  refine ⟨4837767343094229706271267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3225178228729486470847511 4837767343094229706271267)
                  ·
                    refine ⟨7256651014641344559406901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4837767343094229706271267 7256651014641344559406901)
                    ·
                      refine ⟨680311032622626052444397, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7256651014641344559406901 680311032622626052444397)
                      ·
                        rfl

theorem cell23_1324901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 1, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 1, 5, 1, 1, 5].length) (baseStart_1324901 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1324901 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1324901 prefixEnd_1324901 := by exact prefixLift 1324901
  have htrace : WordTrace (prefixWord ++ tailWord_1324901) baseStart_1324901 baseEnd_1324901 := by
    simpa [prefixWord, tailWord_1324901, baseEnd_1324901] using wordTrace_append hprefix tailTrace_1324901
  have hstable : (prefixWord ++ tailWord_1324901).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1324901).length < 2 ^ (prefixWord ++ tailWord_1324901).sum := by decide
  have hdescent : baseEnd_1324901 < baseStart_1324901 := by decide
  rcases family_descends (prefixWord ++ tailWord_1324901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1324908 : List Nat := [2, 2, 1, 1, 4, 3, 1, 1, 4, 4]
def baseStart_1324908 : Nat := 118140960795 + 1324908 * 2 ^ 59
def prefixEnd_1324908 : Nat := 4983230072969 + 3 ^ 40 * 1324908 * 2
def baseEnd_1324908 : Nat := 226771542329069175018955

theorem tailTrace_1324908 : CollatzResearch.WordTrace tailWord_1324908 prefixEnd_1324908 226771542329069175018955 := by
  unfold tailWord_1324908
  simp only [CollatzResearch.WordTrace]
  refine ⟨24161682342046033558367689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32215576456061378077823585 24161682342046033558367689)
  ·
    refine ⟨18121261756534525168775767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24161682342046033558367689 18121261756534525168775767)
    ·
      refine ⟨27181892634801787753163651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18121261756534525168775767 27181892634801787753163651)
      ·
        refine ⟨40772838952202681629745477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27181892634801787753163651 40772838952202681629745477)
        ·
          refine ⟨7644907303538002805577277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 40772838952202681629745477 7644907303538002805577277)
          ·
            refine ⟨2866840238826751052091479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7644907303538002805577277 2866840238826751052091479)
            ·
              refine ⟨4300260358240126578137219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2866840238826751052091479 4300260358240126578137219)
              ·
                refine ⟨6450390537360189867205829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4300260358240126578137219 6450390537360189867205829)
                ·
                  refine ⟨1209448225755035600101093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6450390537360189867205829 1209448225755035600101093)
                  ·
                    refine ⟨226771542329069175018955, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1209448225755035600101093 226771542329069175018955)
                    ·
                      rfl

theorem cell23_1324908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 4, 4].length) (baseStart_1324908 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1324908 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1324908 prefixEnd_1324908 := by exact prefixLift 1324908
  have htrace : WordTrace (prefixWord ++ tailWord_1324908) baseStart_1324908 baseEnd_1324908 := by
    simpa [prefixWord, tailWord_1324908, baseEnd_1324908] using wordTrace_append hprefix tailTrace_1324908
  have hstable : (prefixWord ++ tailWord_1324908).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1324908).length < 2 ^ (prefixWord ++ tailWord_1324908).sum := by decide
  have hdescent : baseEnd_1324908 < baseStart_1324908 := by decide
  rcases family_descends (prefixWord ++ tailWord_1324908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1324938 : List Nat := [3, 1, 2, 4, 2, 1, 1, 9]
def baseStart_1324938 : Nat := 118140960795 + 1324938 * 2 ^ 59
def prefixEnd_1324938 : Nat := 4983230072969 + 3 ^ 40 * 1324938 * 2
def baseEnd_1324938 : Nat := 25197408570623792877101

theorem tailTrace_1324938 : CollatzResearch.WordTrace tailWord_1324938 prefixEnd_1324938 25197408570623792877101 := by
  unfold tailWord_1324938
  simp only [CollatzResearch.WordTrace]
  refine ⟨12081114718495845560081867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32216305915988921493551645 12081114718495845560081867)
  ·
    refine ⟨18121672077743768340122801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12081114718495845560081867 18121672077743768340122801)
    ·
      refine ⟨13591254058307826255092101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18121672077743768340122801 13591254058307826255092101)
      ·
        refine ⟨2548360135932717422829769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 13591254058307826255092101 2548360135932717422829769)
        ·
          refine ⟨1911270101949538067122327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2548360135932717422829769 1911270101949538067122327)
          ·
            refine ⟨2866905152924307100683491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1911270101949538067122327 2866905152924307100683491)
            ·
              refine ⟨4300357729386460651025237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2866905152924307100683491 4300357729386460651025237)
              ·
                refine ⟨25197408570623792877101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 4300357729386460651025237 25197408570623792877101)
                ·
                  rfl

theorem cell23_1324938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 2, 1, 1, 9].length) (baseStart_1324938 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1324938 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1324938 prefixEnd_1324938 := by exact prefixLift 1324938
  have htrace : WordTrace (prefixWord ++ tailWord_1324938) baseStart_1324938 baseEnd_1324938 := by
    simpa [prefixWord, tailWord_1324938, baseEnd_1324938] using wordTrace_append hprefix tailTrace_1324938
  have hstable : (prefixWord ++ tailWord_1324938).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1324938).length < 2 ^ (prefixWord ++ tailWord_1324938).sum := by decide
  have hdescent : baseEnd_1324938 < baseStart_1324938 := by decide
  rcases family_descends (prefixWord ++ tailWord_1324938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1324991 : List Nat := [1, 1, 2, 2, 2, 1, 3, 1, 4, 1, 5]
def baseStart_1324991 : Nat := 118140960795 + 1324991 * 2 ^ 59
def prefixEnd_1324991 : Nat := 4983230072969 + 3 ^ 40 * 1324991 * 2
def baseEnd_1324991 : Nat := 680357245881530700318983

theorem tailTrace_1324991 : CollatzResearch.WordTrace tailWord_1324991 prefixEnd_1324991 680357245881530700318983 := by
  unfold tailWord_1324991
  simp only [CollatzResearch.WordTrace]
  refine ⟨48326391942791372292006827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32217594628527581528004551 48326391942791372292006827)
  ·
    refine ⟨72489587914187058438010241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48326391942791372292006827 72489587914187058438010241)
    ·
      refine ⟨54367190935640293828507681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 72489587914187058438010241 54367190935640293828507681)
      ·
        refine ⟨40775393201730220371380761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54367190935640293828507681 40775393201730220371380761)
        ·
          refine ⟨30581544901297665278535571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40775393201730220371380761 30581544901297665278535571)
          ·
            refine ⟨45872317351946497917803357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30581544901297665278535571 45872317351946497917803357)
            ·
              refine ⟨17202119006979936719176259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 45872317351946497917803357 17202119006979936719176259)
              ·
                refine ⟨25803178510469905078764389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17202119006979936719176259 25803178510469905078764389)
                ·
                  refine ⟨4838095970713107202268323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 25803178510469905078764389 4838095970713107202268323)
                  ·
                    refine ⟨7257143956069660803402485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4838095970713107202268323 7257143956069660803402485)
                    ·
                      refine ⟨680357245881530700318983, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7257143956069660803402485 680357245881530700318983)
                      ·
                        rfl

theorem cell23_1324991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 3, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 3, 1, 4, 1, 5].length) (baseStart_1324991 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1324991 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1324991 prefixEnd_1324991 := by exact prefixLift 1324991
  have htrace : WordTrace (prefixWord ++ tailWord_1324991) baseStart_1324991 baseEnd_1324991 := by
    simpa [prefixWord, tailWord_1324991, baseEnd_1324991] using wordTrace_append hprefix tailTrace_1324991
  have hstable : (prefixWord ++ tailWord_1324991).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1324991).length < 2 ^ (prefixWord ++ tailWord_1324991).sum := by decide
  have hdescent : baseEnd_1324991 < baseStart_1324991 := by decide
  rcases family_descends (prefixWord ++ tailWord_1324991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1325001 : List Nat := [1, 2, 1, 1, 2, 1, 2, 4, 1, 4, 4]
def baseStart_1325001 : Nat := 118140960795 + 1325001 * 2 ^ 59
def prefixEnd_1325001 : Nat := 4983230072969 + 3 ^ 40 * 1325001 * 2
def baseEnd_1325001 : Nat := 680362380688075661193937

theorem tailTrace_1325001 : CollatzResearch.WordTrace tailWord_1325001 prefixEnd_1325001 680362380688075661193937 := by
  unfold tailWord_1325001
  simp only [CollatzResearch.WordTrace]
  refine ⟨48326756672755143999870857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32217837781836762666580571 48326756672755143999870857)
  ·
    refine ⟨36245067504566357999903143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48326756672755143999870857 36245067504566357999903143)
    ·
      refine ⟨54367601256849536999854715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36245067504566357999903143 54367601256849536999854715)
      ·
        refine ⟨81551401885274305499782073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54367601256849536999854715 81551401885274305499782073)
        ·
          refine ⟨61163551413955729124836555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 81551401885274305499782073 61163551413955729124836555)
          ·
            refine ⟨91745327120933593687254833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61163551413955729124836555 91745327120933593687254833)
            ·
              refine ⟨68808995340700195265441125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 91745327120933593687254833 68808995340700195265441125)
              ·
                refine ⟨12901686626381286612270211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 68808995340700195265441125 12901686626381286612270211)
                ·
                  refine ⟨19352529939571929918405317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12901686626381286612270211 19352529939571929918405317)
                  ·
                    refine ⟨3628599363669736859700997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19352529939571929918405317 3628599363669736859700997)
                    ·
                      refine ⟨680362380688075661193937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3628599363669736859700997 680362380688075661193937)
                      ·
                        rfl

theorem cell23_1325001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 4, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 4, 1, 4, 4].length) (baseStart_1325001 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1325001 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1325001 prefixEnd_1325001 := by exact prefixLift 1325001
  have htrace : WordTrace (prefixWord ++ tailWord_1325001) baseStart_1325001 baseEnd_1325001 := by
    simpa [prefixWord, tailWord_1325001, baseEnd_1325001] using wordTrace_append hprefix tailTrace_1325001
  have hstable : (prefixWord ++ tailWord_1325001).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1325001).length < 2 ^ (prefixWord ++ tailWord_1325001).sum := by decide
  have hdescent : baseEnd_1325001 < baseStart_1325001 := by decide
  rcases family_descends (prefixWord ++ tailWord_1325001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1325051 : List Nat := [1, 1, 1, 1, 1, 3, 4, 2, 1, 1, 7]
def baseStart_1325051 : Nat := 118140960795 + 1325051 * 2 ^ 59
def prefixEnd_1325051 : Nat := 4983230072969 + 3 ^ 40 * 1325051 * 2
def baseEnd_1325051 : Nat := 680388054720800465568707

theorem tailTrace_1325051 : CollatzResearch.WordTrace tailWord_1325051 prefixEnd_1325051 680388054720800465568707 := by
  unfold tailWord_1325051
  simp only [CollatzResearch.WordTrace]
  refine ⟨48328580322574002539191007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32219053548382668359460671 48328580322574002539191007)
  ·
    refine ⟨72492870483861003808786511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48328580322574002539191007 72492870483861003808786511)
    ·
      refine ⟨108739305725791505713179767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72492870483861003808786511 108739305725791505713179767)
      ·
        refine ⟨163108958588687258569769651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 108739305725791505713179767 163108958588687258569769651)
        ·
          refine ⟨244663437883030887854654477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 163108958588687258569769651 244663437883030887854654477)
          ·
            refine ⟨91748789206136582945495429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 244663437883030887854654477 91748789206136582945495429)
            ·
              refine ⟨17202897976150609302280393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 91748789206136582945495429 17202897976150609302280393)
              ·
                refine ⟨12902173482112956976710295, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17202897976150609302280393 12902173482112956976710295)
                ·
                  refine ⟨19353260223169435465065443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12902173482112956976710295 19353260223169435465065443)
                  ·
                    refine ⟨29029890334754153197598165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19353260223169435465065443 29029890334754153197598165)
                    ·
                      refine ⟨680388054720800465568707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 29029890334754153197598165 680388054720800465568707)
                      ·
                        rfl

theorem cell23_1325051_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 4, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 4, 2, 1, 1, 7].length) (baseStart_1325051 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1325051 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1325051 prefixEnd_1325051 := by exact prefixLift 1325051
  have htrace : WordTrace (prefixWord ++ tailWord_1325051) baseStart_1325051 baseEnd_1325051 := by
    simpa [prefixWord, tailWord_1325051, baseEnd_1325051] using wordTrace_append hprefix tailTrace_1325051
  have hstable : (prefixWord ++ tailWord_1325051).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1325051).length < 2 ^ (prefixWord ++ tailWord_1325051).sum := by decide
  have hdescent : baseEnd_1325051 < baseStart_1325051 := by decide
  rcases family_descends (prefixWord ++ tailWord_1325051) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1325105 : List Nat := [1, 2, 2, 3, 1, 3, 2, 2, 3, 4]
def baseStart_1325105 : Nat := 118140960795 + 1325105 * 2 ^ 59
def prefixEnd_1325105 : Nat := 4983230072969 + 3 ^ 40 * 1325105 * 2
def baseEnd_1325105 : Nat := 226805260892047751431153

theorem tailTrace_1325105 : CollatzResearch.WordTrace tailWord_1325105 prefixEnd_1325105 226805260892047751431153 := by
  unfold tailWord_1325105
  simp only [CollatzResearch.WordTrace]
  refine ⟨48330549864378369761656769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32220366576252246507771179 48330549864378369761656769)
  ·
    refine ⟨36247912398283777321242577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48330549864378369761656769 36247912398283777321242577)
    ·
      refine ⟨27185934298712832990931933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36247912398283777321242577 27185934298712832990931933)
      ·
        refine ⟨10194725362017312371599475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27185934298712832990931933 10194725362017312371599475)
        ·
          refine ⟨15292088043025968557399213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10194725362017312371599475 15292088043025968557399213)
          ·
            refine ⟨5734533016134738209024705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15292088043025968557399213 5734533016134738209024705)
            ·
              refine ⟨4300899762101053656768529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5734533016134738209024705 4300899762101053656768529)
              ·
                refine ⟨3225674821575790242576397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4300899762101053656768529 3225674821575790242576397)
                ·
                  refine ⟨1209628058090921340966149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3225674821575790242576397 1209628058090921340966149)
                  ·
                    refine ⟨226805260892047751431153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1209628058090921340966149 226805260892047751431153)
                    ·
                      rfl

theorem cell23_1325105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 2, 2, 3, 4].length) (baseStart_1325105 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1325105 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1325105 prefixEnd_1325105 := by exact prefixLift 1325105
  have htrace : WordTrace (prefixWord ++ tailWord_1325105) baseStart_1325105 baseEnd_1325105 := by
    simpa [prefixWord, tailWord_1325105, baseEnd_1325105] using wordTrace_append hprefix tailTrace_1325105
  have hstable : (prefixWord ++ tailWord_1325105).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1325105).length < 2 ^ (prefixWord ++ tailWord_1325105).sum := by decide
  have hdescent : baseEnd_1325105 < baseStart_1325105 := by decide
  rcases family_descends (prefixWord ++ tailWord_1325105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1325152 : List Nat := [2, 1, 1, 3, 2, 5, 2, 1, 6]
def baseStart_1325152 : Nat := 118140960795 + 1325152 * 2 ^ 59
def prefixEnd_1325152 : Nat := 4983230072969 + 3 ^ 40 * 1325152 * 2
def baseEnd_1325152 : Nat := 75604435140767174489527

theorem tailTrace_1325152 : CollatzResearch.WordTrace tailWord_1325152 prefixEnd_1325152 75604435140767174489527 := by
  unfold tailWord_1325152
  simp only [CollatzResearch.WordTrace]
  refine ⟨24166132047604048394308855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32221509396805397859078473 24166132047604048394308855)
  ·
    refine ⟨36249198071406072591463283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24166132047604048394308855 36249198071406072591463283)
    ·
      refine ⟨54373797107109108887194925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36249198071406072591463283 54373797107109108887194925)
      ·
        refine ⟨20390173915165915832698097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 54373797107109108887194925 20390173915165915832698097)
        ·
          refine ⟨15292630436374436874523573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20390173915165915832698097 15292630436374436874523573)
          ·
            refine ⟨1433684103410103456986585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 15292630436374436874523573 1433684103410103456986585)
            ·
              refine ⟨1075263077557577592739939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1433684103410103456986585 1075263077557577592739939)
              ·
                refine ⟨1612894616336366389109909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1075263077557577592739939 1612894616336366389109909)
                ·
                  refine ⟨75604435140767174489527, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1612894616336366389109909 75604435140767174489527)
                  ·
                    rfl

theorem cell23_1325152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 5, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 5, 2, 1, 6].length) (baseStart_1325152 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1325152 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1325152 prefixEnd_1325152 := by exact prefixLift 1325152
  have htrace : WordTrace (prefixWord ++ tailWord_1325152) baseStart_1325152 baseEnd_1325152 := by
    simpa [prefixWord, tailWord_1325152, baseEnd_1325152] using wordTrace_append hprefix tailTrace_1325152
  have hstable : (prefixWord ++ tailWord_1325152).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1325152).length < 2 ^ (prefixWord ++ tailWord_1325152).sum := by decide
  have hdescent : baseEnd_1325152 < baseStart_1325152 := by decide
  rcases family_descends (prefixWord ++ tailWord_1325152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1325155 : List Nat := [1, 1, 1, 5, 1, 1, 2, 1, 3, 5, 2]
def baseStart_1325155 : Nat := 118140960795 + 1325155 * 2 ^ 59
def prefixEnd_1325155 : Nat := 4983230072969 + 3 ^ 40 * 1325155 * 2
def baseEnd_1325155 : Nat := 680441456708868058668229

theorem tailTrace_1325155 : CollatzResearch.WordTrace tailWord_1325155 prefixEnd_1325155 680441456708868058668229 := by
  unfold tailWord_1325155
  simp only [CollatzResearch.WordTrace]
  refine ⟨48332373514197228300976919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32221582342798152200651279 48332373514197228300976919)
  ·
    refine ⟨72498560271295842451465379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48332373514197228300976919 72498560271295842451465379)
    ·
      refine ⟨108747840406943763677198069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72498560271295842451465379 108747840406943763677198069)
      ·
        refine ⟨10195110038150977844737319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 108747840406943763677198069 10195110038150977844737319)
        ·
          refine ⟨15292665057226466767105979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10195110038150977844737319 15292665057226466767105979)
          ·
            refine ⟨22938997585839700150658969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15292665057226466767105979 22938997585839700150658969)
            ·
              refine ⟨17204248189379775112994227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22938997585839700150658969 17204248189379775112994227)
              ·
                refine ⟨25806372284069662669491341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17204248189379775112994227 25806372284069662669491341)
                ·
                  refine ⟨9677389606526123501059253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25806372284069662669491341 9677389606526123501059253)
                  ·
                    refine ⟨907255275611824078224305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9677389606526123501059253 907255275611824078224305)
                    ·
                      refine ⟨680441456708868058668229, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 907255275611824078224305 680441456708868058668229)
                      ·
                        rfl

theorem cell23_1325155_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 2, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 2, 1, 3, 5, 2].length) (baseStart_1325155 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1325155 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1325155 prefixEnd_1325155 := by exact prefixLift 1325155
  have htrace : WordTrace (prefixWord ++ tailWord_1325155) baseStart_1325155 baseEnd_1325155 := by
    simpa [prefixWord, tailWord_1325155, baseEnd_1325155] using wordTrace_append hprefix tailTrace_1325155
  have hstable : (prefixWord ++ tailWord_1325155).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1325155).length < 2 ^ (prefixWord ++ tailWord_1325155).sum := by decide
  have hdescent : baseEnd_1325155 < baseStart_1325155 := by decide
  rcases family_descends (prefixWord ++ tailWord_1325155) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1325165 : List Nat := [1, 5, 1, 1, 2, 1, 3, 1, 3, 5]
def baseStart_1325165 : Nat := 118140960795 + 1325165 * 2 ^ 59
def prefixEnd_1325165 : Nat := 4983230072969 + 3 ^ 40 * 1325165 * 2
def baseEnd_1325165 : Nat := 226815530505137673181061

theorem tailTrace_1325165 : CollatzResearch.WordTrace tailWord_1325165 prefixEnd_1325165 226815530505137673181061 := by
  unfold tailWord_1325165
  simp only [CollatzResearch.WordTrace]
  refine ⟨48332738244161000008840949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32221825496107333339227299 48332738244161000008840949)
  ·
    refine ⟨4531194210390093750828839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 48332738244161000008840949 4531194210390093750828839)
    ·
      refine ⟨6796791315585140626243259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4531194210390093750828839 6796791315585140626243259)
      ·
        refine ⟨10195186973377710939364889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6796791315585140626243259 10195186973377710939364889)
        ·
          refine ⟨7646390230033283204523667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10195186973377710939364889 7646390230033283204523667)
          ·
            refine ⟨11469585345049924806785501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7646390230033283204523667 11469585345049924806785501)
            ·
              refine ⟨4301094504393721802544563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11469585345049924806785501 4301094504393721802544563)
              ·
                refine ⟨6451641756590582703816845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4301094504393721802544563 6451641756590582703816845)
                ·
                  refine ⟨2419365658721468513931317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6451641756590582703816845 2419365658721468513931317)
                  ·
                    refine ⟨226815530505137673181061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2419365658721468513931317 226815530505137673181061)
                    ·
                      rfl

theorem cell23_1325165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 3, 1, 3, 5].length) (baseStart_1325165 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1325165 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1325165 prefixEnd_1325165 := by exact prefixLift 1325165
  have htrace : WordTrace (prefixWord ++ tailWord_1325165) baseStart_1325165 baseEnd_1325165 := by
    simpa [prefixWord, tailWord_1325165, baseEnd_1325165] using wordTrace_append hprefix tailTrace_1325165
  have hstable : (prefixWord ++ tailWord_1325165).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1325165).length < 2 ^ (prefixWord ++ tailWord_1325165).sum := by decide
  have hdescent : baseEnd_1325165 < baseStart_1325165 := by decide
  rcases family_descends (prefixWord ++ tailWord_1325165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1325205 : List Nat := [1, 3, 2, 1, 1, 1, 3, 1, 5, 2, 3]
def baseStart_1325205 : Nat := 118140960795 + 1325205 * 2 ^ 59
def prefixEnd_1325205 : Nat := 4983230072969 + 3 ^ 40 * 1325205 * 2
def baseEnd_1325205 : Nat := 680467130741592863042999

theorem tailTrace_1325205 : CollatzResearch.WordTrace tailWord_1325205 prefixEnd_1325205 680467130741592863042999 := by
  unfold tailWord_1325205
  simp only [CollatzResearch.WordTrace]
  refine ⟨48334197164016086840297069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32222798109344057893531379 48334197164016086840297069)
  ·
    refine ⟨18125323936506032565111401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 48334197164016086840297069 18125323936506032565111401)
    ·
      refine ⟨13593992952379524423833551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18125323936506032565111401 13593992952379524423833551)
      ·
        refine ⟨20390989428569286635750327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13593992952379524423833551 20390989428569286635750327)
        ·
          refine ⟨30586484142853929953625491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20390989428569286635750327 30586484142853929953625491)
          ·
            refine ⟨45879726214280894930438237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30586484142853929953625491 45879726214280894930438237)
            ·
              refine ⟨17204897330355335598914339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 45879726214280894930438237 17204897330355335598914339)
              ·
                refine ⟨25807345995533003398371509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17204897330355335598914339 25807345995533003398371509)
                ·
                  refine ⟨2419438687081219068597329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 25807345995533003398371509 2419438687081219068597329)
                  ·
                    refine ⟨1814579015310914301447997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2419438687081219068597329 1814579015310914301447997)
                    ·
                      refine ⟨680467130741592863042999, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1814579015310914301447997 680467130741592863042999)
                      ·
                        rfl

theorem cell23_1325205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 3, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 3, 1, 5, 2, 3].length) (baseStart_1325205 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1325205 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1325205 prefixEnd_1325205 := by exact prefixLift 1325205
  have htrace : WordTrace (prefixWord ++ tailWord_1325205) baseStart_1325205 baseEnd_1325205 := by
    simpa [prefixWord, tailWord_1325205, baseEnd_1325205] using wordTrace_append hprefix tailTrace_1325205
  have hstable : (prefixWord ++ tailWord_1325205).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1325205).length < 2 ^ (prefixWord ++ tailWord_1325205).sum := by decide
  have hdescent : baseEnd_1325205 < baseStart_1325205 := by decide
  rcases family_descends (prefixWord ++ tailWord_1325205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1325212 : List Nat := [2, 2, 3, 2, 1, 1, 1, 5, 2, 4]
def baseStart_1325212 : Nat := 118140960795 + 1325212 * 2 ^ 59
def prefixEnd_1325212 : Nat := 4983230072969 + 3 ^ 40 * 1325212 * 2
def baseEnd_1325212 : Nat := 226823575035391445218489

theorem tailTrace_1325212 : CollatzResearch.WordTrace tailWord_1325212 prefixEnd_1325212 226823575035391445218489 := by
  unfold tailWord_1325212
  simp only [CollatzResearch.WordTrace]
  refine ⟨24167226237495363517900945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32222968316660484690534593 24167226237495363517900945)
  ·
    refine ⟨18125419678121522638425709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24167226237495363517900945 18125419678121522638425709)
    ·
      refine ⟨6797032379295570989409641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18125419678121522638425709 6797032379295570989409641)
      ·
        refine ⟨5097774284471678242057231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6797032379295570989409641 5097774284471678242057231)
        ·
          refine ⟨7646661426707517363085847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5097774284471678242057231 7646661426707517363085847)
          ·
            refine ⟨11469992140061276044628771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7646661426707517363085847 11469992140061276044628771)
            ·
              refine ⟨17204988210091914066943157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11469992140061276044628771 17204988210091914066943157)
              ·
                refine ⟨1612967644696116943775921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 17204988210091914066943157 1612967644696116943775921)
                ·
                  refine ⟨1209725733522087707831941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1612967644696116943775921 1209725733522087707831941)
                  ·
                    refine ⟨226823575035391445218489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1209725733522087707831941 226823575035391445218489)
                    ·
                      rfl

theorem cell23_1325212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 1, 5, 2, 4].length) (baseStart_1325212 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1325212 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1325212 prefixEnd_1325212 := by exact prefixLift 1325212
  have htrace : WordTrace (prefixWord ++ tailWord_1325212) baseStart_1325212 baseEnd_1325212 := by
    simpa [prefixWord, tailWord_1325212, baseEnd_1325212] using wordTrace_append hprefix tailTrace_1325212
  have hstable : (prefixWord ++ tailWord_1325212).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1325212).length < 2 ^ (prefixWord ++ tailWord_1325212).sum := by decide
  have hdescent : baseEnd_1325212 < baseStart_1325212 := by decide
  rcases family_descends (prefixWord ++ tailWord_1325212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1325223 : List Nat := [1, 1, 6, 2, 3, 1, 1, 1, 2, 3, 2]
def baseStart_1325223 : Nat := 118140960795 + 1325223 * 2 ^ 59
def prefixEnd_1325223 : Nat := 4983230072969 + 3 ^ 40 * 1325223 * 2
def baseEnd_1325223 : Nat := 680476373393373792617917

theorem tailTrace_1325223 : CollatzResearch.WordTrace tailWord_1325223 prefixEnd_1325223 680476373393373792617917 := by
  unfold tailWord_1325223
  simp only [CollatzResearch.WordTrace]
  refine ⟨48334853677950875914452323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32223235785300583942968215 48334853677950875914452323)
  ·
    refine ⟨72502280516926313871678485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48334853677950875914452323 72502280516926313871678485)
    ·
      refine ⟨3398544399230920962734929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 72502280516926313871678485 3398544399230920962734929)
      ·
        refine ⟨2548908299423190722051197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3398544399230920962734929 2548908299423190722051197)
        ·
          refine ⟨955840612283696520769199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2548908299423190722051197 955840612283696520769199)
          ·
            refine ⟨1433760918425544781153799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 955840612283696520769199 1433760918425544781153799)
            ·
              refine ⟨2150641377638317171730699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1433760918425544781153799 2150641377638317171730699)
              ·
                refine ⟨3225962066457475757596049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2150641377638317171730699 3225962066457475757596049)
                ·
                  refine ⟨2419471549843106818197037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3225962066457475757596049 2419471549843106818197037)
                  ·
                    refine ⟨907301831191165056823889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2419471549843106818197037 907301831191165056823889)
                    ·
                      refine ⟨680476373393373792617917, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 907301831191165056823889 680476373393373792617917)
                      ·
                        rfl

theorem cell23_1325223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 3, 1, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 3, 1, 1, 1, 2, 3, 2].length) (baseStart_1325223 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1325223 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1325223 prefixEnd_1325223 := by exact prefixLift 1325223
  have htrace : WordTrace (prefixWord ++ tailWord_1325223) baseStart_1325223 baseEnd_1325223 := by
    simpa [prefixWord, tailWord_1325223, baseEnd_1325223] using wordTrace_append hprefix tailTrace_1325223
  have hstable : (prefixWord ++ tailWord_1325223).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1325223).length < 2 ^ (prefixWord ++ tailWord_1325223).sum := by decide
  have hdescent : baseEnd_1325223 < baseStart_1325223 := by decide
  rcases family_descends (prefixWord ++ tailWord_1325223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1325228 : List Nat := [2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 6]
def baseStart_1325228 : Nat := 118140960795 + 1325228 * 2 ^ 59
def prefixEnd_1325228 : Nat := 4983230072969 + 3 ^ 40 * 1325228 * 2
def baseEnd_1325228 : Nat := 680478940796646273055393

theorem tailTrace_1325228 : CollatzResearch.WordTrace tailWord_1325228 prefixEnd_1325228 680478940796646273055393 := by
  unfold tailWord_1325228
  simp only [CollatzResearch.WordTrace]
  refine ⟨24167518021466380884192169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32223357361955174512256225 24167518021466380884192169)
  ·
    refine ⟨18125638516099785663144127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24167518021466380884192169 18125638516099785663144127)
    ·
      refine ⟨27188457774149678494716191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18125638516099785663144127 27188457774149678494716191)
      ·
        refine ⟨40782686661224517742074287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27188457774149678494716191 40782686661224517742074287)
        ·
          refine ⟨61174029991836776613111431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40782686661224517742074287 61174029991836776613111431)
          ·
            refine ⟨91761044987755164919667147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61174029991836776613111431 91761044987755164919667147)
            ·
              refine ⟨137641567481632747379500721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 91761044987755164919667147 137641567481632747379500721)
              ·
                refine ⟨103231175611224560534625541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 137641567481632747379500721 103231175611224560534625541)
                ·
                  refine ⟨19355845427104605100242289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 103231175611224560534625541 19355845427104605100242289)
                  ·
                    refine ⟨14516884070328453825181717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19355845427104605100242289 14516884070328453825181717)
                    ·
                      refine ⟨680478940796646273055393, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 14516884070328453825181717 680478940796646273055393)
                      ·
                        rfl

theorem cell23_1325228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 6].length) (baseStart_1325228 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1325228 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1325228 prefixEnd_1325228 := by exact prefixLift 1325228
  have htrace : WordTrace (prefixWord ++ tailWord_1325228) baseStart_1325228 baseEnd_1325228 := by
    simpa [prefixWord, tailWord_1325228, baseEnd_1325228] using wordTrace_append hprefix tailTrace_1325228
  have hstable : (prefixWord ++ tailWord_1325228).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1325228).length < 2 ^ (prefixWord ++ tailWord_1325228).sum := by decide
  have hdescent : baseEnd_1325228 < baseStart_1325228 := by decide
  rcases family_descends (prefixWord ++ tailWord_1325228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1325230 : List Nat := [4, 1, 4, 2, 1, 1, 2, 3, 1, 1, 3]
def baseStart_1325230 : Nat := 118140960795 + 1325230 * 2 ^ 59
def prefixEnd_1325230 : Nat := 4983230072969 + 3 ^ 40 * 1325230 * 2
def baseEnd_1325230 : Nat := 680479967757955265230385

theorem tailTrace_1325230 : CollatzResearch.WordTrace tailWord_1325230 prefixEnd_1325230 680479967757955265230385 := by
  unfold tailWord_1325230
  simp only [CollatzResearch.WordTrace]
  refine ⟨6041888623615689513744643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 32223405992617010739971429 6041888623615689513744643)
  ·
    refine ⟨9062832935423534270616965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6041888623615689513744643 9062832935423534270616965)
    ·
      refine ⟨1699281175391912675740681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 9062832935423534270616965 1699281175391912675740681)
      ·
        refine ⟨1274460881543934506805511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1699281175391912675740681 1274460881543934506805511)
        ·
          refine ⟨1911691322315901760208267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1274460881543934506805511 1911691322315901760208267)
          ·
            refine ⟨2867536983473852640312401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1911691322315901760208267 2867536983473852640312401)
            ·
              refine ⟨2150652737605389480234301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2867536983473852640312401 2150652737605389480234301)
              ·
                refine ⟨806494776602021055087863, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2150652737605389480234301 806494776602021055087863)
                ·
                  refine ⟨1209742164903031582631795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 806494776602021055087863 1209742164903031582631795)
                  ·
                    refine ⟨1814613247354547373947693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1209742164903031582631795 1814613247354547373947693)
                    ·
                      refine ⟨680479967757955265230385, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1814613247354547373947693 680479967757955265230385)
                      ·
                        rfl

theorem cell23_1325230_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 1, 1, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 1, 1, 2, 3, 1, 1, 3].length) (baseStart_1325230 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1325230 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1325230 prefixEnd_1325230 := by exact prefixLift 1325230
  have htrace : WordTrace (prefixWord ++ tailWord_1325230) baseStart_1325230 baseEnd_1325230 := by
    simpa [prefixWord, tailWord_1325230, baseEnd_1325230] using wordTrace_append hprefix tailTrace_1325230
  have hstable : (prefixWord ++ tailWord_1325230).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1325230).length < 2 ^ (prefixWord ++ tailWord_1325230).sum := by decide
  have hdescent : baseEnd_1325230 < baseStart_1325230 := by decide
  rcases family_descends (prefixWord ++ tailWord_1325230) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1325239 : List Nat := [1, 1, 3, 1, 4, 2, 4, 1, 1, 2, 3]
def baseStart_1325239 : Nat := 118140960795 + 1325239 * 2 ^ 59
def prefixEnd_1325239 : Nat := 4983230072969 + 3 ^ 40 * 1325239 * 2
def baseEnd_1325239 : Nat := 680484589083845730017843

theorem tailTrace_1325239 : CollatzResearch.WordTrace tailWord_1325239 prefixEnd_1325239 680484589083845730017843 := by
  unfold tailWord_1325239
  simp only [CollatzResearch.WordTrace]
  refine ⟨48335437245892910647034771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32223624830595273764689847 48335437245892910647034771)
  ·
    refine ⟨72503155868839365970552157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48335437245892910647034771 72503155868839365970552157)
    ·
      refine ⟨27188683450814762238957059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 72503155868839365970552157 27188683450814762238957059)
      ·
        refine ⟨40783025176222143358435589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27188683450814762238957059 40783025176222143358435589)
        ·
          refine ⟨7646817220541651879706673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 40783025176222143358435589 7646817220541651879706673)
          ·
            refine ⟨5735112915406238909780005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7646817220541651879706673 5735112915406238909780005)
            ·
              refine ⟨1075333671638669795583751, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5735112915406238909780005 1075333671638669795583751)
              ·
                refine ⟨1613000507458004693375627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1075333671638669795583751 1613000507458004693375627)
                ·
                  refine ⟨2419500761187007040063441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1613000507458004693375627 2419500761187007040063441)
                  ·
                    refine ⟨1814625570890255280047581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2419500761187007040063441 1814625570890255280047581)
                    ·
                      refine ⟨680484589083845730017843, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1814625570890255280047581 680484589083845730017843)
                      ·
                        rfl

theorem cell23_1325239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 4, 1, 1, 2, 3].length) (baseStart_1325239 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1325239 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1325239 prefixEnd_1325239 := by exact prefixLift 1325239
  have htrace : WordTrace (prefixWord ++ tailWord_1325239) baseStart_1325239 baseEnd_1325239 := by
    simpa [prefixWord, tailWord_1325239, baseEnd_1325239] using wordTrace_append hprefix tailTrace_1325239
  have hstable : (prefixWord ++ tailWord_1325239).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1325239).length < 2 ^ (prefixWord ++ tailWord_1325239).sum := by decide
  have hdescent : baseEnd_1325239 < baseStart_1325239 := by decide
  rcases family_descends (prefixWord ++ tailWord_1325239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1325246 : List Nat := [4, 2, 1, 1, 4, 2, 1, 2, 2, 4]
def baseStart_1325246 : Nat := 118140960795 + 1325246 * 2 ^ 59
def prefixEnd_1325246 : Nat := 4983230072969 + 3 ^ 40 * 1325246 * 2
def baseEnd_1325246 : Nat := 226829394482809067543437

theorem tailTrace_1325246 : CollatzResearch.WordTrace tailWord_1325246 prefixEnd_1325246 226829394482809067543437 := by
  unfold tailWord_1325246
  simp only [CollatzResearch.WordTrace]
  refine ⟨6041961569608443855317449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 32223795037911700561693061 6041961569608443855317449)
  ·
    refine ⟨4531471177206332891488087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6041961569608443855317449 4531471177206332891488087)
    ·
      refine ⟨6797206765809499337232131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4531471177206332891488087 6797206765809499337232131)
      ·
        refine ⟨10195810148714249005848197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6797206765809499337232131 10195810148714249005848197)
        ·
          refine ⟨1911714402883921688596537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10195810148714249005848197 1911714402883921688596537)
          ·
            refine ⟨1433785802162941266447403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1911714402883921688596537 1433785802162941266447403)
            ·
              refine ⟨2150678703244411899671105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1433785802162941266447403 2150678703244411899671105)
              ·
                refine ⟨1613009027433308924753329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2150678703244411899671105 1613009027433308924753329)
                ·
                  refine ⟨1209756770574981693564997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1613009027433308924753329 1209756770574981693564997)
                  ·
                    refine ⟨226829394482809067543437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1209756770574981693564997 226829394482809067543437)
                    ·
                      rfl

theorem cell23_1325246_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 4, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 4, 2, 1, 2, 2, 4].length) (baseStart_1325246 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1325246 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1325246 prefixEnd_1325246 := by exact prefixLift 1325246
  have htrace : WordTrace (prefixWord ++ tailWord_1325246) baseStart_1325246 baseEnd_1325246 := by
    simpa [prefixWord, tailWord_1325246, baseEnd_1325246] using wordTrace_append hprefix tailTrace_1325246
  have hstable : (prefixWord ++ tailWord_1325246).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1325246).length < 2 ^ (prefixWord ++ tailWord_1325246).sum := by decide
  have hdescent : baseEnd_1325246 < baseStart_1325246 := by decide
  rcases family_descends (prefixWord ++ tailWord_1325246) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1325276 : List Nat := [2, 2, 5, 2, 1, 2, 2, 7]
def baseStart_1325276 : Nat := 118140960795 + 1325276 * 2 ^ 59
def prefixEnd_1325276 : Nat := 4983230072969 + 3 ^ 40 * 1325276 * 2
def baseEnd_1325276 : Nat := 25203836587706003157599

theorem tailTrace_1325276 : CollatzResearch.WordTrace tailWord_1325276 prefixEnd_1325276 25203836587706003157599 := by
  unfold tailWord_1325276
  simp only [CollatzResearch.WordTrace]
  refine ⟨24168393373379432983065841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32224524497839243977421121 24168393373379432983065841)
  ·
    refine ⟨18126295030034574737299381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24168393373379432983065841 18126295030034574737299381)
    ·
      refine ⟨1699340159065741381621817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 18126295030034574737299381 1699340159065741381621817)
      ·
        refine ⟨1274505119299306036216363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1699340159065741381621817 1274505119299306036216363)
        ·
          refine ⟨1911757678948959054324545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1274505119299306036216363 1911757678948959054324545)
          ·
            refine ⟨1433818259211719290743409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1911757678948959054324545 1433818259211719290743409)
            ·
              refine ⟨1075363694408789468057557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1433818259211719290743409 1075363694408789468057557)
              ·
                refine ⟨25203836587706003157599, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1075363694408789468057557 25203836587706003157599)
                ·
                  rfl

theorem cell23_1325276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 1, 2, 2, 7].length) (baseStart_1325276 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1325276 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1325276 prefixEnd_1325276 := by exact prefixLift 1325276
  have htrace : WordTrace (prefixWord ++ tailWord_1325276) baseStart_1325276 baseEnd_1325276 := by
    simpa [prefixWord, tailWord_1325276, baseEnd_1325276] using wordTrace_append hprefix tailTrace_1325276
  have hstable : (prefixWord ++ tailWord_1325276).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1325276).length < 2 ^ (prefixWord ++ tailWord_1325276).sum := by decide
  have hdescent : baseEnd_1325276 < baseStart_1325276 := by decide
  rcases family_descends (prefixWord ++ tailWord_1325276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1325292 : List Nat := [2, 2, 1, 1, 2, 3, 2, 1, 3, 4, 2]
def baseStart_1325292 : Nat := 118140960795 + 1325292 * 2 ^ 59
def prefixEnd_1325292 : Nat := 4983230072969 + 3 ^ 40 * 1325292 * 2
def baseEnd_1325292 : Nat := 680511803558534022655099

theorem tailTrace_1325292 : CollatzResearch.WordTrace tailWord_1325292 prefixEnd_1325292 680511803558534022655099 := by
  unfold tailWord_1325292
  simp only [CollatzResearch.WordTrace]
  refine ⟨24168685157350450349357065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32224913543133933799142753 24168685157350450349357065)
  ·
    refine ⟨18126513868012837762017799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24168685157350450349357065 18126513868012837762017799)
    ·
      refine ⟨27189770802019256643026699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18126513868012837762017799 27189770802019256643026699)
      ·
        refine ⟨40784656203028884964540049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27189770802019256643026699 40784656203028884964540049)
        ·
          refine ⟨30588492152271663723405037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40784656203028884964540049 30588492152271663723405037)
          ·
            refine ⟨11470684557101873896276889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30588492152271663723405037 11470684557101873896276889)
            ·
              refine ⟨8603013417826405422207667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11470684557101873896276889 8603013417826405422207667)
              ·
                refine ⟨12904520126739608133311501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8603013417826405422207667 12904520126739608133311501)
                ·
                  refine ⟨4839195047527353049991813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12904520126739608133311501 4839195047527353049991813)
                  ·
                    refine ⟨907349071411378696873465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4839195047527353049991813 907349071411378696873465)
                    ·
                      refine ⟨680511803558534022655099, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 907349071411378696873465 680511803558534022655099)
                      ·
                        rfl

theorem cell23_1325292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 4, 2].length) (baseStart_1325292 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1325292 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1325292 prefixEnd_1325292 := by exact prefixLift 1325292
  have htrace : WordTrace (prefixWord ++ tailWord_1325292) baseStart_1325292 baseEnd_1325292 := by
    simpa [prefixWord, tailWord_1325292, baseEnd_1325292] using wordTrace_append hprefix tailTrace_1325292
  have hstable : (prefixWord ++ tailWord_1325292).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1325292).length < 2 ^ (prefixWord ++ tailWord_1325292).sum := by decide
  have hdescent : baseEnd_1325292 < baseStart_1325292 := by decide
  rcases family_descends (prefixWord ++ tailWord_1325292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1325295 : List Nat := [1, 1, 2, 1, 6, 1, 1, 1, 1, 3, 5]
def baseStart_1325295 : Nat := 118140960795 + 1325295 * 2 ^ 59
def prefixEnd_1325295 : Nat := 4983230072969 + 3 ^ 40 * 1325295 * 2
def baseEnd_1325295 : Nat := 680513344000497510917585

theorem tailTrace_1325295 : CollatzResearch.WordTrace tailWord_1325295 prefixEnd_1325295 680513344000497510917585 := by
  unfold tailWord_1325295
  simp only [CollatzResearch.WordTrace]
  refine ⟨48337479733690032211073339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32224986489126688140715559 48337479733690032211073339)
  ·
    refine ⟨72506219600535048316610009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48337479733690032211073339 72506219600535048316610009)
    ·
      refine ⟨54379664700401286237457507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 72506219600535048316610009 54379664700401286237457507)
      ·
        refine ⟨81569497050601929356186261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54379664700401286237457507 81569497050601929356186261)
        ·
          refine ⟨3823570174246965438571231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 81569497050601929356186261 3823570174246965438571231)
          ·
            refine ⟨5735355261370448157856847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3823570174246965438571231 5735355261370448157856847)
            ·
              refine ⟨8603032892055672236785271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5735355261370448157856847 8603032892055672236785271)
              ·
                refine ⟨12904549338083508355177907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8603032892055672236785271 12904549338083508355177907)
                ·
                  refine ⟨19356824007125262532766861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12904549338083508355177907 19356824007125262532766861)
                  ·
                    refine ⟨7258809002671973449787573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19356824007125262532766861 7258809002671973449787573)
                    ·
                      refine ⟨680513344000497510917585, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7258809002671973449787573 680513344000497510917585)
                      ·
                        rfl

theorem cell23_1325295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 1, 1, 1, 3, 5].length) (baseStart_1325295 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1325295 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1325295 prefixEnd_1325295 := by exact prefixLift 1325295
  have htrace : WordTrace (prefixWord ++ tailWord_1325295) baseStart_1325295 baseEnd_1325295 := by
    simpa [prefixWord, tailWord_1325295, baseEnd_1325295] using wordTrace_append hprefix tailTrace_1325295
  have hstable : (prefixWord ++ tailWord_1325295).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1325295).length < 2 ^ (prefixWord ++ tailWord_1325295).sum := by decide
  have hdescent : baseEnd_1325295 < baseStart_1325295 := by decide
  rcases family_descends (prefixWord ++ tailWord_1325295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1325305 : List Nat := [1, 2, 1, 3, 1, 1, 2, 4, 2, 2, 4]
def baseStart_1325305 : Nat := 118140960795 + 1325305 * 2 ^ 59
def prefixEnd_1325305 : Nat := 4983230072969 + 3 ^ 40 * 1325305 * 2
def baseEnd_1325305 : Nat := 680518478807042471792539

theorem tailTrace_1325305 : CollatzResearch.WordTrace tailWord_1325305 prefixEnd_1325305 680518478807042471792539 := by
  unfold tailWord_1325305
  simp only [CollatzResearch.WordTrace]
  refine ⟨48337844463653803918937369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32225229642435869279291579 48337844463653803918937369)
  ·
    refine ⟨36253383347740352939203027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48337844463653803918937369 36253383347740352939203027)
    ·
      refine ⟨54380075021610529408804541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36253383347740352939203027 54380075021610529408804541)
      ·
        refine ⟨20392528133103948528301703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 54380075021610529408804541 20392528133103948528301703)
        ·
          refine ⟨30588792199655922792452555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20392528133103948528301703 30588792199655922792452555)
          ·
            refine ⟨45883188299483884188678833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30588792199655922792452555 45883188299483884188678833)
            ·
              refine ⟨34412391224612913141509125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 45883188299483884188678833 34412391224612913141509125)
              ·
                refine ⟨6452323354614921214032961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 34412391224612913141509125 6452323354614921214032961)
                ·
                  refine ⟨4839242515961190910524721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6452323354614921214032961 4839242515961190910524721)
                  ·
                    refine ⟨3629431886970893182893541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4839242515961190910524721 3629431886970893182893541)
                    ·
                      refine ⟨680518478807042471792539, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3629431886970893182893541 680518478807042471792539)
                      ·
                        rfl

theorem cell23_1325305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 2, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 2, 4, 2, 2, 4].length) (baseStart_1325305 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1325305 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1325305 prefixEnd_1325305 := by exact prefixLift 1325305
  have htrace : WordTrace (prefixWord ++ tailWord_1325305) baseStart_1325305 baseEnd_1325305 := by
    simpa [prefixWord, tailWord_1325305, baseEnd_1325305] using wordTrace_append hprefix tailTrace_1325305
  have hstable : (prefixWord ++ tailWord_1325305).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1325305).length < 2 ^ (prefixWord ++ tailWord_1325305).sum := by decide
  have hdescent : baseEnd_1325305 < baseStart_1325305 := by decide
  rcases family_descends (prefixWord ++ tailWord_1325305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1325326 : List Nat := [4, 1, 1, 2, 1, 2, 3, 3, 2, 2, 2]
def baseStart_1325326 : Nat := 118140960795 + 1325326 * 2 ^ 59
def prefixEnd_1325326 : Nat := 4983230072969 + 3 ^ 40 * 1325326 * 2
def baseEnd_1325326 : Nat := 680529261900786889629943

theorem tailTrace_1325326 : CollatzResearch.WordTrace tailWord_1325326 prefixEnd_1325326 680529261900786889629943 := by
  unfold tailWord_1325326
  simp only [CollatzResearch.WordTrace]
  refine ⟨6042326299572215563181479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 32225740264385149670301221 6042326299572215563181479)
  ·
    refine ⟨9063489449358323344772219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6042326299572215563181479 9063489449358323344772219)
    ·
      refine ⟨13595234174037485017158329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9063489449358323344772219 13595234174037485017158329)
      ·
        refine ⟨10196425630528113762868747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13595234174037485017158329 10196425630528113762868747)
        ·
          refine ⟨15294638445792170644303121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10196425630528113762868747 15294638445792170644303121)
          ·
            refine ⟨11470978834344127983227341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15294638445792170644303121 11470978834344127983227341)
            ·
              refine ⟨4301617062879047993710253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11470978834344127983227341 4301617062879047993710253)
              ·
                refine ⟨1613106398579642997641345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4301617062879047993710253 1613106398579642997641345)
                ·
                  refine ⟨1209829798934732248231009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1613106398579642997641345 1209829798934732248231009)
                  ·
                    refine ⟨907372349201049186173257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1209829798934732248231009 907372349201049186173257)
                    ·
                      refine ⟨680529261900786889629943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 907372349201049186173257 680529261900786889629943)
                      ·
                        rfl

theorem cell23_1325326_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 3, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 3, 3, 2, 2, 2].length) (baseStart_1325326 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1325326 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1325326 prefixEnd_1325326 := by exact prefixLift 1325326
  have htrace : WordTrace (prefixWord ++ tailWord_1325326) baseStart_1325326 baseEnd_1325326 := by
    simpa [prefixWord, tailWord_1325326, baseEnd_1325326] using wordTrace_append hprefix tailTrace_1325326
  have hstable : (prefixWord ++ tailWord_1325326).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1325326).length < 2 ^ (prefixWord ++ tailWord_1325326).sum := by decide
  have hdescent : baseEnd_1325326 < baseStart_1325326 := by decide
  rcases family_descends (prefixWord ++ tailWord_1325326) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1325345 : List Nat := [1, 2, 3, 2, 1, 1, 2, 3, 1, 7]
def baseStart_1325345 : Nat := 118140960795 + 1325345 * 2 ^ 59
def prefixEnd_1325345 : Nat := 4983230072969 + 3 ^ 40 * 1325345 * 2
def baseEnd_1325345 : Nat := 226846339344407438430785

theorem tailTrace_1325345 : CollatzResearch.WordTrace tailWord_1325345 prefixEnd_1325345 226846339344407438430785 := by
  unfold tailWord_1325345
  simp only [CollatzResearch.WordTrace]
  refine ⟨48339303383508890750393489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32226202255672593833595659 48339303383508890750393489)
  ·
    refine ⟨36254477537631668062795117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48339303383508890750393489 36254477537631668062795117)
    ·
      refine ⟨13595429076611875523548169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 36254477537631668062795117 13595429076611875523548169)
      ·
        refine ⟨10196571807458906642661127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13595429076611875523548169 10196571807458906642661127)
        ·
          refine ⟨15294857711188359963991691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10196571807458906642661127 15294857711188359963991691)
          ·
            refine ⟨22942286566782539945987537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15294857711188359963991691 22942286566782539945987537)
            ·
              refine ⟨17206714925086904959490653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22942286566782539945987537 17206714925086904959490653)
              ·
                refine ⟨6452518096907589359808995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17206714925086904959490653 6452518096907589359808995)
                ·
                  refine ⟨9678777145361384039713493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6452518096907589359808995 9678777145361384039713493)
                  ·
                    refine ⟨226846339344407438430785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 9678777145361384039713493 226846339344407438430785)
                    ·
                      rfl

theorem cell23_1325345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 2, 3, 1, 7].length) (baseStart_1325345 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1325345 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1325345 prefixEnd_1325345 := by exact prefixLift 1325345
  have htrace : WordTrace (prefixWord ++ tailWord_1325345) baseStart_1325345 baseEnd_1325345 := by
    simpa [prefixWord, tailWord_1325345, baseEnd_1325345] using wordTrace_append hprefix tailTrace_1325345
  have hstable : (prefixWord ++ tailWord_1325345).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1325345).length < 2 ^ (prefixWord ++ tailWord_1325345).sum := by decide
  have hdescent : baseEnd_1325345 < baseStart_1325345 := by decide
  rcases family_descends (prefixWord ++ tailWord_1325345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1325369 : List Nat := [1, 2, 1, 6, 1, 1, 1, 1, 2, 5, 2]
def baseStart_1325369 : Nat := 118140960795 + 1325369 * 2 ^ 59
def prefixEnd_1325369 : Nat := 4983230072969 + 3 ^ 40 * 1325369 * 2
def baseEnd_1325369 : Nat := 680551341568930221392245

theorem tailTrace_1325369 : CollatzResearch.WordTrace tailWord_1325369 prefixEnd_1325369 680551341568930221392245 := by
  unfold tailWord_1325369
  simp only [CollatzResearch.WordTrace]
  refine ⟨48340178735421942849267161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32226785823614628566178107 48340178735421942849267161)
  ·
    refine ⟨36255134051566457136950371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48340178735421942849267161 36255134051566457136950371)
    ·
      refine ⟨54382701077349685705425557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36255134051566457136950371 54382701077349685705425557)
      ·
        refine ⟨2549189113000766517441823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 54382701077349685705425557 2549189113000766517441823)
        ·
          refine ⟨3823783669501149776162735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2549189113000766517441823 3823783669501149776162735)
          ·
            refine ⟨5735675504251724664244103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3823783669501149776162735 5735675504251724664244103)
            ·
              refine ⟨8603513256377586996366155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5735675504251724664244103 8603513256377586996366155)
              ·
                refine ⟨12905269884566380494549233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8603513256377586996366155 12905269884566380494549233)
                ·
                  refine ⟨9678952413424785370911925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12905269884566380494549233 9678952413424785370911925)
                  ·
                    refine ⟨907401788758573628522993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9678952413424785370911925 907401788758573628522993)
                    ·
                      refine ⟨680551341568930221392245, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 907401788758573628522993 680551341568930221392245)
                      ·
                        rfl

theorem cell23_1325369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 1, 1, 2, 5, 2].length) (baseStart_1325369 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1325369 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1325369 prefixEnd_1325369 := by exact prefixLift 1325369
  have htrace : WordTrace (prefixWord ++ tailWord_1325369) baseStart_1325369 baseEnd_1325369 := by
    simpa [prefixWord, tailWord_1325369, baseEnd_1325369] using wordTrace_append hprefix tailTrace_1325369
  have hstable : (prefixWord ++ tailWord_1325369).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1325369).length < 2 ^ (prefixWord ++ tailWord_1325369).sum := by decide
  have hdescent : baseEnd_1325369 < baseStart_1325369 := by decide
  rcases family_descends (prefixWord ++ tailWord_1325369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1325392 : List Nat := [2, 1, 1, 1, 1, 6, 1, 1, 5, 4]
def baseStart_1325392 : Nat := 118140960795 + 1325392 * 2 ^ 59
def prefixEnd_1325392 : Nat := 4983230072969 + 3 ^ 40 * 1325392 * 2
def baseEnd_1325392 : Nat := 226854383874661210468213

theorem tailTrace_1325392 : CollatzResearch.WordTrace tailWord_1325392 prefixEnd_1325392 226854383874661210468213 := by
  unfold tailWord_1325392
  simp only [CollatzResearch.WordTrace]
  refine ⟨24170508807169308888677215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32227345076225745184902953 24170508807169308888677215)
  ·
    refine ⟨36255763210753963333015823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24170508807169308888677215 36255763210753963333015823)
    ·
      refine ⟨54383644816130944999523735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36255763210753963333015823 54383644816130944999523735)
      ·
        refine ⟨81575467224196417499285603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54383644816130944999523735 81575467224196417499285603)
        ·
          refine ⟨122363200836294626248928405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 81575467224196417499285603 122363200836294626248928405)
          ·
            refine ⟨5735775039201310605418519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 122363200836294626248928405 5735775039201310605418519)
            ·
              refine ⟨8603662558801965908127779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5735775039201310605418519 8603662558801965908127779)
              ·
                refine ⟨12905493838202948862191669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8603662558801965908127779 12905493838202948862191669)
                ·
                  refine ⟨1209890047331526455830469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 12905493838202948862191669 1209890047331526455830469)
                  ·
                    refine ⟨226854383874661210468213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1209890047331526455830469 226854383874661210468213)
                    ·
                      rfl

theorem cell23_1325392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 1, 1, 5, 4].length) (baseStart_1325392 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1325392 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1325392 prefixEnd_1325392 := by exact prefixLift 1325392
  have htrace : WordTrace (prefixWord ++ tailWord_1325392) baseStart_1325392 baseEnd_1325392 := by
    simpa [prefixWord, tailWord_1325392, baseEnd_1325392] using wordTrace_append hprefix tailTrace_1325392
  have hstable : (prefixWord ++ tailWord_1325392).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1325392).length < 2 ^ (prefixWord ++ tailWord_1325392).sum := by decide
  have hdescent : baseEnd_1325392 < baseStart_1325392 := by decide
  rcases family_descends (prefixWord ++ tailWord_1325392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1325395 : List Nat := [1, 1, 1, 2, 1, 1, 4, 1, 1, 6, 4]
def baseStart_1325395 : Nat := 118140960795 + 1325395 * 2 ^ 59
def prefixEnd_1325395 : Nat := 4983230072969 + 3 ^ 40 * 1325395 * 2
def baseEnd_1325395 : Nat := 680564692065947119667125

theorem tailTrace_1325395 : CollatzResearch.WordTrace tailWord_1325395 prefixEnd_1325395 680564692065947119667125 := by
  unfold tailWord_1325395
  simp only [CollatzResearch.WordTrace]
  refine ⟨48341127033327749289713639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32227418022218499526475759 48341127033327749289713639)
  ·
    refine ⟨72511690549991623934570459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48341127033327749289713639 72511690549991623934570459)
    ·
      refine ⟨108767535824987435901855689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72511690549991623934570459 108767535824987435901855689)
      ·
        refine ⟨81575651868740576926391767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 108767535824987435901855689 81575651868740576926391767)
        ·
          refine ⟨122363477803110865389587651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 81575651868740576926391767 122363477803110865389587651)
          ·
            refine ⟨183545216704666298084381477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 122363477803110865389587651 183545216704666298084381477)
            ·
              refine ⟨34414728132124930890821527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 183545216704666298084381477 34414728132124930890821527)
              ·
                refine ⟨51622092198187396336232291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34414728132124930890821527 51622092198187396336232291)
                ·
                  refine ⟨77433138297281094504348437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 51622092198187396336232291 77433138297281094504348437)
                  ·
                    refine ⟨3629678357685051304891333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 77433138297281094504348437 3629678357685051304891333)
                    ·
                      refine ⟨680564692065947119667125, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3629678357685051304891333 680564692065947119667125)
                      ·
                        rfl

theorem cell23_1325395_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 4, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 4, 1, 1, 6, 4].length) (baseStart_1325395 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1325395 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1325395 prefixEnd_1325395 := by exact prefixLift 1325395
  have htrace : WordTrace (prefixWord ++ tailWord_1325395) baseStart_1325395 baseEnd_1325395 := by
    simpa [prefixWord, tailWord_1325395, baseEnd_1325395] using wordTrace_append hprefix tailTrace_1325395
  have hstable : (prefixWord ++ tailWord_1325395).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1325395).length < 2 ^ (prefixWord ++ tailWord_1325395).sum := by decide
  have hdescent : baseEnd_1325395 < baseStart_1325395 := by decide
  rcases family_descends (prefixWord ++ tailWord_1325395) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1325426 : List Nat := [3, 2, 1, 2, 1, 3, 2, 4, 1, 4]
def baseStart_1325426 : Nat := 118140960795 + 1325426 * 2 ^ 59
def prefixEnd_1325426 : Nat := 4983230072969 + 3 ^ 40 * 1325426 * 2
def baseEnd_1325426 : Nat := 226860203322078832793161

theorem tailTrace_1325426 : CollatzResearch.WordTrace tailWord_1325426 prefixEnd_1325426 226860203322078832793161 := by
  unfold tailWord_1325426
  simp only [CollatzResearch.WordTrace]
  refine ⟨12085564424053860396023033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32228171797476961056061421 12085564424053860396023033)
  ·
    refine ⟨9064173318040395297017275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12085564424053860396023033 9064173318040395297017275)
    ·
      refine ⟨13596259977060592945525913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9064173318040395297017275 13596259977060592945525913)
      ·
        refine ⟨10197194982795444709144435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13596259977060592945525913 10197194982795444709144435)
        ·
          refine ⟨15295792474193167063716653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10197194982795444709144435 15295792474193167063716653)
          ·
            refine ⟨5735922177822437648893745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15295792474193167063716653 5735922177822437648893745)
            ·
              refine ⟨4301941633366828236670309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5735922177822437648893745 4301941633366828236670309)
              ·
                refine ⟨806614056256280294375683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4301941633366828236670309 806614056256280294375683)
                ·
                  refine ⟨1209921084384420441563525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 806614056256280294375683 1209921084384420441563525)
                  ·
                    refine ⟨226860203322078832793161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1209921084384420441563525 226860203322078832793161)
                    ·
                      rfl

theorem cell23_1325426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 2, 4, 1, 4].length) (baseStart_1325426 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1325426 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1325426 prefixEnd_1325426 := by exact prefixLift 1325426
  have htrace : WordTrace (prefixWord ++ tailWord_1325426) baseStart_1325426 baseEnd_1325426 := by
    simpa [prefixWord, tailWord_1325426, baseEnd_1325426] using wordTrace_append hprefix tailTrace_1325426
  have hstable : (prefixWord ++ tailWord_1325426).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1325426).length < 2 ^ (prefixWord ++ tailWord_1325426).sum := by decide
  have hdescent : baseEnd_1325426 < baseStart_1325426 := by decide
  rcases family_descends (prefixWord ++ tailWord_1325426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1325460 : List Nat := [2, 4, 2, 1, 3, 2, 1, 3, 1, 4]
def baseStart_1325460 : Nat := 118140960795 + 1325460 * 2 ^ 59
def prefixEnd_1325460 : Nat := 4983230072969 + 3 ^ 40 * 1325460 * 2
def baseEnd_1325460 : Nat := 226866022769496455118109

theorem tailTrace_1325460 : CollatzResearch.WordTrace tailWord_1325460 prefixEnd_1325460 226866022769496455118109 := by
  unfold tailWord_1325460
  simp only [CollatzResearch.WordTrace]
  refine ⟨24171748889046132695414917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32228998518728176927219889 24171748889046132695414917)
  ·
    refine ⟨4532202916696149880390297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 24171748889046132695414917 4532202916696149880390297)
    ·
      refine ⟨3399152187522112410292723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4532202916696149880390297 3399152187522112410292723)
      ·
        refine ⟨5098728281283168615439085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3399152187522112410292723 5098728281283168615439085)
        ·
          refine ⟨1912023105481188230789657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5098728281283168615439085 1912023105481188230789657)
          ·
            refine ⟨1434017329110891173092243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1912023105481188230789657 1434017329110891173092243)
            ·
              refine ⟨2151025993666336759638365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1434017329110891173092243 2151025993666336759638365)
              ·
                refine ⟨806634747624876284864387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2151025993666336759638365 806634747624876284864387)
                ·
                  refine ⟨1209952121437314427296581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 806634747624876284864387 1209952121437314427296581)
                  ·
                    refine ⟨226866022769496455118109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1209952121437314427296581 226866022769496455118109)
                    ·
                      rfl

theorem cell23_1325460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 3, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 3, 2, 1, 3, 1, 4].length) (baseStart_1325460 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1325460 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1325460 prefixEnd_1325460 := by exact prefixLift 1325460
  have htrace : WordTrace (prefixWord ++ tailWord_1325460) baseStart_1325460 baseEnd_1325460 := by
    simpa [prefixWord, tailWord_1325460, baseEnd_1325460] using wordTrace_append hprefix tailTrace_1325460
  have hstable : (prefixWord ++ tailWord_1325460).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1325460).length < 2 ^ (prefixWord ++ tailWord_1325460).sum := by decide
  have hdescent : baseEnd_1325460 < baseStart_1325460 := by decide
  rcases family_descends (prefixWord ++ tailWord_1325460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1325512 : List Nat := [2, 1, 3, 1, 3, 2, 2, 9]
def baseStart_1325512 : Nat := 118140960795 + 1325512 * 2 ^ 59
def prefixEnd_1325512 : Nat := 4983230072969 + 3 ^ 40 * 1325512 * 2
def baseEnd_1325512 : Nat := 25208324788982339329781

theorem tailTrace_1325512 : CollatzResearch.WordTrace tailWord_1325512 prefixEnd_1325512 25208324788982339329781 := by
  unfold tailWord_1325512
  simp only [CollatzResearch.WordTrace]
  refine ⟨24172697186951939135861395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32230262915935918847815193 24172697186951939135861395)
  ·
    refine ⟨36259045780427908703792093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24172697186951939135861395 36259045780427908703792093)
    ·
      refine ⟨13597142167660465763922035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 36259045780427908703792093 13597142167660465763922035)
      ·
        refine ⟨20395713251490698645883053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13597142167660465763922035 20395713251490698645883053)
        ·
          refine ⟨7648392469309011992206145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20395713251490698645883053 7648392469309011992206145)
          ·
            refine ⟨5736294351981758994154609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7648392469309011992206145 5736294351981758994154609)
            ·
              refine ⟨4302220763986319245615957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5736294351981758994154609 4302220763986319245615957)
              ·
                refine ⟨25208324788982339329781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 4302220763986319245615957 25208324788982339329781)
                ·
                  rfl

theorem cell23_1325512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 2, 9].length) (baseStart_1325512 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1325512 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1325512 prefixEnd_1325512 := by exact prefixLift 1325512
  have htrace : WordTrace (prefixWord ++ tailWord_1325512) baseStart_1325512 baseEnd_1325512 := by
    simpa [prefixWord, tailWord_1325512, baseEnd_1325512] using wordTrace_append hprefix tailTrace_1325512
  have hstable : (prefixWord ++ tailWord_1325512).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1325512).length < 2 ^ (prefixWord ++ tailWord_1325512).sum := by decide
  have hdescent : baseEnd_1325512 < baseStart_1325512 := by decide
  rcases family_descends (prefixWord ++ tailWord_1325512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1325574 : List Nat := [6, 2, 1, 1, 1, 3, 2, 1, 1, 1, 4]
def baseStart_1325574 : Nat := 118140960795 + 1325574 * 2 ^ 59
def prefixEnd_1325574 : Nat := 4983230072969 + 3 ^ 40 * 1325574 * 2
def baseEnd_1325574 : Nat := 680656605103101919328803

theorem tailTrace_1325574 : CollatzResearch.WordTrace tailWord_1325574 prefixEnd_1325574 680656605103101919328803 := by
  unfold tailWord_1325574
  simp only [CollatzResearch.WordTrace]
  refine ⟨1510864240614976964389993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 32231770466452841906986517 1510864240614976964389993)
  ·
    refine ⟨1133148180461232723292495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1510864240614976964389993 1133148180461232723292495)
    ·
      refine ⟨1699722270691849084938743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1133148180461232723292495 1699722270691849084938743)
      ·
        refine ⟨2549583406037773627408115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1699722270691849084938743 2549583406037773627408115)
        ·
          refine ⟨3824375109056660441112173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2549583406037773627408115 3824375109056660441112173)
          ·
            refine ⟨1434140665896247665417065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3824375109056660441112173 1434140665896247665417065)
            ·
              refine ⟨1075605499422185749062799, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1434140665896247665417065 1075605499422185749062799)
              ·
                refine ⟨1613408249133278623594199, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1075605499422185749062799 1613408249133278623594199)
                ·
                  refine ⟨2420112373699917935391299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1613408249133278623594199 2420112373699917935391299)
                  ·
                    refine ⟨3630168560549876903086949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2420112373699917935391299 3630168560549876903086949)
                    ·
                      refine ⟨680656605103101919328803, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3630168560549876903086949 680656605103101919328803)
                      ·
                        rfl

theorem cell23_1325574_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 3, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 3, 2, 1, 1, 1, 4].length) (baseStart_1325574 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1325574 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1325574 prefixEnd_1325574 := by exact prefixLift 1325574
  have htrace : WordTrace (prefixWord ++ tailWord_1325574) baseStart_1325574 baseEnd_1325574 := by
    simpa [prefixWord, tailWord_1325574, baseEnd_1325574] using wordTrace_append hprefix tailTrace_1325574
  have hstable : (prefixWord ++ tailWord_1325574).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1325574).length < 2 ^ (prefixWord ++ tailWord_1325574).sum := by decide
  have hdescent : baseEnd_1325574 < baseStart_1325574 := by decide
  rcases family_descends (prefixWord ++ tailWord_1325574) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1325607 : List Nat := [1, 1, 7, 2, 2, 1, 1, 1, 1, 3, 3]
def baseStart_1325607 : Nat := 118140960795 + 1325607 * 2 ^ 59
def prefixEnd_1325607 : Nat := 4983230072969 + 3 ^ 40 * 1325607 * 2
def baseEnd_1325607 : Nat := 680673549964700290216151

theorem tailTrace_1325607 : CollatzResearch.WordTrace tailWord_1325607 prefixEnd_1325607 680673549964700290216151 := by
  unfold tailWord_1325607
  simp only [CollatzResearch.WordTrace]
  refine ⟨48348859308559709496431075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32232572872373139664287383 48348859308559709496431075)
  ·
    refine ⟨72523288962839564244646613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48348859308559709496431075 72523288962839564244646613)
    ·
      refine ⟨1699764585066552286983905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 72523288962839564244646613 1699764585066552286983905)
      ·
        refine ⟨1274823438799914215237929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1699764585066552286983905 1274823438799914215237929)
        ·
          refine ⟨956117579099935661428447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1274823438799914215237929 956117579099935661428447)
          ·
            refine ⟨1434176368649903492142671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 956117579099935661428447 1434176368649903492142671)
            ·
              refine ⟨2151264552974855238214007, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1434176368649903492142671 2151264552974855238214007)
              ·
                refine ⟨3226896829462282857321011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2151264552974855238214007 3226896829462282857321011)
                ·
                  refine ⟨4840345244193424285981517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3226896829462282857321011 4840345244193424285981517)
                  ·
                    refine ⟨1815129466572534107243069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4840345244193424285981517 1815129466572534107243069)
                    ·
                      refine ⟨680673549964700290216151, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1815129466572534107243069 680673549964700290216151)
                      ·
                        rfl

theorem cell23_1325607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 2, 1, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 2, 1, 1, 1, 1, 3, 3].length) (baseStart_1325607 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1325607 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1325607 prefixEnd_1325607 := by exact prefixLift 1325607
  have htrace : WordTrace (prefixWord ++ tailWord_1325607) baseStart_1325607 baseEnd_1325607 := by
    simpa [prefixWord, tailWord_1325607, baseEnd_1325607] using wordTrace_append hprefix tailTrace_1325607
  have hstable : (prefixWord ++ tailWord_1325607).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1325607).length < 2 ^ (prefixWord ++ tailWord_1325607).sum := by decide
  have hdescent : baseEnd_1325607 < baseStart_1325607 := by decide
  rcases family_descends (prefixWord ++ tailWord_1325607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1325612 : List Nat := [2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 9]
def baseStart_1325612 : Nat := 118140960795 + 1325612 * 2 ^ 59
def prefixEnd_1325612 : Nat := 4983230072969 + 3 ^ 40 * 1325612 * 2
def baseEnd_1325612 : Nat := 680676117367972770653627

theorem tailTrace_1325612 : CollatzResearch.WordTrace tailWord_1325612 prefixEnd_1325612 680676117367972770653627 := by
  unfold tailWord_1325612
  simp only [CollatzResearch.WordTrace]
  refine ⟨24174520836770797675181545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32232694449027730233575393 24174520836770797675181545)
  ·
    refine ⟨18130890627578098256386159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24174520836770797675181545 18130890627578098256386159)
    ·
      refine ⟨27196335941367147384579239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18130890627578098256386159 27196335941367147384579239)
      ·
        refine ⟨40794503912050721076868859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27196335941367147384579239 40794503912050721076868859)
        ·
          refine ⟨61191755868076081615303289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40794503912050721076868859 61191755868076081615303289)
          ·
            refine ⟨45893816901057061211477467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 61191755868076081615303289 45893816901057061211477467)
            ·
              refine ⟨68840725351585591817216201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45893816901057061211477467 68840725351585591817216201)
              ·
                refine ⟨51630544013689193862912151, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 68840725351585591817216201 51630544013689193862912151)
                ·
                  refine ⟨77445816020533790794368227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 51630544013689193862912151 77445816020533790794368227)
                  ·
                    refine ⟨116168724030800686191552341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 77445816020533790794368227 116168724030800686191552341)
                    ·
                      refine ⟨680676117367972770653627, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 116168724030800686191552341 680676117367972770653627)
                      ·
                        rfl

theorem cell23_1325612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 9].length) (baseStart_1325612 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1325612 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1325612 prefixEnd_1325612 := by exact prefixLift 1325612
  have htrace : WordTrace (prefixWord ++ tailWord_1325612) baseStart_1325612 baseEnd_1325612 := by
    simpa [prefixWord, tailWord_1325612, baseEnd_1325612] using wordTrace_append hprefix tailTrace_1325612
  have hstable : (prefixWord ++ tailWord_1325612).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1325612).length < 2 ^ (prefixWord ++ tailWord_1325612).sum := by decide
  have hdescent : baseEnd_1325612 < baseStart_1325612 := by decide
  rcases family_descends (prefixWord ++ tailWord_1325612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1325649 : List Nat := [1, 2, 2, 1, 3, 3, 1, 1, 4, 5]
def baseStart_1325649 : Nat := 118140960795 + 1325649 * 2 ^ 59
def prefixEnd_1325649 : Nat := 4983230072969 + 3 ^ 40 * 1325649 * 2
def baseEnd_1325649 : Nat := 226898372050729708630319

theorem tailTrace_1325649 : CollatzResearch.WordTrace tailWord_1325649 prefixEnd_1325649 226898372050729708630319 := by
  unfold tailWord_1325649
  simp only [CollatzResearch.WordTrace]
  refine ⟨48350391174407550669460001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32233594116271700446306667 48350391174407550669460001)
  ·
    refine ⟨36262793380805663002095001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48350391174407550669460001 36262793380805663002095001)
    ·
      refine ⟨27197095035604247251571251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36262793380805663002095001 27197095035604247251571251)
      ·
        refine ⟨40795642553406370877356877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27197095035604247251571251 40795642553406370877356877)
        ·
          refine ⟨15298365957527389079008829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 40795642553406370877356877 15298365957527389079008829)
          ·
            refine ⟨5736887234072770904628311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15298365957527389079008829 5736887234072770904628311)
            ·
              refine ⟨8605330851109156356942467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5736887234072770904628311 8605330851109156356942467)
              ·
                refine ⟨12907996276663734535413701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8605330851109156356942467 12907996276663734535413701)
                ·
                  refine ⟨2420249301874450225390069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12907996276663734535413701 2420249301874450225390069)
                  ·
                    refine ⟨226898372050729708630319, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2420249301874450225390069 226898372050729708630319)
                    ·
                      rfl

theorem cell23_1325649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 1, 1, 4, 5].length) (baseStart_1325649 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1325649 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1325649 prefixEnd_1325649 := by exact prefixLift 1325649
  have htrace : WordTrace (prefixWord ++ tailWord_1325649) baseStart_1325649 baseEnd_1325649 := by
    simpa [prefixWord, tailWord_1325649, baseEnd_1325649] using wordTrace_append hprefix tailTrace_1325649
  have hstable : (prefixWord ++ tailWord_1325649).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1325649).length < 2 ^ (prefixWord ++ tailWord_1325649).sum := by decide
  have hdescent : baseEnd_1325649 < baseStart_1325649 := by decide
  rcases family_descends (prefixWord ++ tailWord_1325649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1325770 : List Nat := [3, 1, 2, 1, 4, 2, 2, 1, 3, 1, 3]
def baseStart_1325770 : Nat := 118140960795 + 1325770 * 2 ^ 59
def prefixEnd_1325770 : Nat := 4983230072969 + 3 ^ 40 * 1325770 * 2
def baseEnd_1325770 : Nat := 680757247311383152477901

theorem tailTrace_1325770 : CollatzResearch.WordTrace tailWord_1325770 prefixEnd_1325770 680757247311383152477901 := by
  unfold tailWord_1325770
  simp only [CollatzResearch.WordTrace]
  refine ⟨12088701101742297083653691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32236536271312792223076509 12088701101742297083653691)
  ·
    refine ⟨18133051652613445625480537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12088701101742297083653691 18133051652613445625480537)
    ·
      refine ⟨13599788739460084219110403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18133051652613445625480537 13599788739460084219110403)
      ·
        refine ⟨20399683109190126328665605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13599788739460084219110403 20399683109190126328665605)
        ·
          refine ⟨3824940582973148686624801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 20399683109190126328665605 3824940582973148686624801)
          ·
            refine ⟨2868705437229861514968601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3824940582973148686624801 2868705437229861514968601)
            ·
              refine ⟨2151529077922396136226451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2868705437229861514968601 2151529077922396136226451)
              ·
                refine ⟨3227293616883594204339677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2151529077922396136226451 3227293616883594204339677)
                ·
                  refine ⟨1210235106331347826627379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3227293616883594204339677 1210235106331347826627379)
                  ·
                    refine ⟨1815352659497021739941069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1210235106331347826627379 1815352659497021739941069)
                    ·
                      refine ⟨680757247311383152477901, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1815352659497021739941069 680757247311383152477901)
                      ·
                        rfl

theorem cell23_1325770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 2, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 2, 2, 1, 3, 1, 3].length) (baseStart_1325770 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1325770 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1325770 prefixEnd_1325770 := by exact prefixLift 1325770
  have htrace : WordTrace (prefixWord ++ tailWord_1325770) baseStart_1325770 baseEnd_1325770 := by
    simpa [prefixWord, tailWord_1325770, baseEnd_1325770] using wordTrace_append hprefix tailTrace_1325770
  have hstable : (prefixWord ++ tailWord_1325770).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1325770).length < 2 ^ (prefixWord ++ tailWord_1325770).sum := by decide
  have hdescent : baseEnd_1325770 < baseStart_1325770 := by decide
  rcases family_descends (prefixWord ++ tailWord_1325770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1325793 : List Nat := [1, 2, 3, 1, 4, 1, 1, 4, 1, 1, 4]
def baseStart_1325793 : Nat := 118140960795 + 1325793 * 2 ^ 59
def prefixEnd_1325793 : Nat := 4983230072969 + 3 ^ 40 * 1325793 * 2
def baseEnd_1325793 : Nat := 680769057366436562490295

theorem tailTrace_1325793 : CollatzResearch.WordTrace tailWord_1325793 prefixEnd_1325793 680769057366436562490295 := by
  unfold tailWord_1325793
  simp only [CollatzResearch.WordTrace]
  refine ⟨48355643285885863262702033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32237095523923908841801355 48355643285885863262702033)
  ·
    refine ⟨36266732464414397447026525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48355643285885863262702033 36266732464414397447026525)
    ·
      refine ⟨13600024674155399042634947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 36266732464414397447026525 13600024674155399042634947)
      ·
        refine ⟨20400037011233098563952421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13600024674155399042634947 20400037011233098563952421)
        ·
          refine ⟨3825006939606205980741079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 20400037011233098563952421 3825006939606205980741079)
          ·
            refine ⟨5737510409409308971111619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3825006939606205980741079 5737510409409308971111619)
            ·
              refine ⟨8606265614113963456667429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5737510409409308971111619 8606265614113963456667429)
              ·
                refine ⟨1613674802646368148125143, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8606265614113963456667429 1613674802646368148125143)
                ·
                  refine ⟨2420512203969552222187715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1613674802646368148125143 2420512203969552222187715)
                  ·
                    refine ⟨3630768305954328333281573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2420512203969552222187715 3630768305954328333281573)
                    ·
                      refine ⟨680769057366436562490295, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3630768305954328333281573 680769057366436562490295)
                      ·
                        rfl

theorem cell23_1325793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 1, 4, 1, 1, 4].length) (baseStart_1325793 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1325793 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1325793 prefixEnd_1325793 := by exact prefixLift 1325793
  have htrace : WordTrace (prefixWord ++ tailWord_1325793) baseStart_1325793 baseEnd_1325793 := by
    simpa [prefixWord, tailWord_1325793, baseEnd_1325793] using wordTrace_append hprefix tailTrace_1325793
  have hstable : (prefixWord ++ tailWord_1325793).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1325793).length < 2 ^ (prefixWord ++ tailWord_1325793).sum := by decide
  have hdescent : baseEnd_1325793 < baseStart_1325793 := by decide
  rcases family_descends (prefixWord ++ tailWord_1325793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1325847 : List Nat := [1, 1, 3, 4, 3, 2, 1, 2, 1, 2, 3]
def baseStart_1325847 : Nat := 118140960795 + 1325847 * 2 ^ 59
def prefixEnd_1325847 : Nat := 4983230072969 + 3 ^ 40 * 1325847 * 2
def baseEnd_1325847 : Nat := 680796785321779351215047

theorem tailTrace_1325847 : CollatzResearch.WordTrace tailWord_1325847 prefixEnd_1325847 680796785321779351215047 := by
  unfold tailWord_1325847
  simp only [CollatzResearch.WordTrace]
  refine ⟨48357612827690230485167795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32238408551793486990111863 48357612827690230485167795)
  ·
    refine ⟨72536419241535345727751693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48357612827690230485167795 72536419241535345727751693)
    ·
      refine ⟨27201157215575754647906885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 72536419241535345727751693 27201157215575754647906885)
      ·
        refine ⟨5100216977920453996482541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 27201157215575754647906885 5100216977920453996482541)
        ·
          refine ⟨1912581366720170248680953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5100216977920453996482541 1912581366720170248680953)
          ·
            refine ⟨1434436025040127686510715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1912581366720170248680953 1434436025040127686510715)
            ·
              refine ⟨2151654037560191529766073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1434436025040127686510715 2151654037560191529766073)
              ·
                refine ⟨1613740528170143647324555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2151654037560191529766073 1613740528170143647324555)
                ·
                  refine ⟨2420610792255215470986833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1613740528170143647324555 2420610792255215470986833)
                  ·
                    refine ⟨1815458094191411603240125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2420610792255215470986833 1815458094191411603240125)
                    ·
                      refine ⟨680796785321779351215047, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1815458094191411603240125 680796785321779351215047)
                      ·
                        rfl

theorem cell23_1325847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 3, 2, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 3, 2, 1, 2, 1, 2, 3].length) (baseStart_1325847 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1325847 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1325847 prefixEnd_1325847 := by exact prefixLift 1325847
  have htrace : WordTrace (prefixWord ++ tailWord_1325847) baseStart_1325847 baseEnd_1325847 := by
    simpa [prefixWord, tailWord_1325847, baseEnd_1325847] using wordTrace_append hprefix tailTrace_1325847
  have hstable : (prefixWord ++ tailWord_1325847).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1325847).length < 2 ^ (prefixWord ++ tailWord_1325847).sum := by decide
  have hdescent : baseEnd_1325847 < baseStart_1325847 := by decide
  rcases family_descends (prefixWord ++ tailWord_1325847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1325860 : List Nat := [2, 3, 1, 3, 3, 1, 1, 2, 1, 3, 3]
def baseStart_1325860 : Nat := 118140960795 + 1325860 * 2 ^ 59
def prefixEnd_1325860 : Nat := 4983230072969 + 3 ^ 40 * 1325860 * 2
def baseEnd_1325860 : Nat := 680803460570287800352487

theorem tailTrace_1325860 : CollatzResearch.WordTrace tailWord_1325860 prefixEnd_1325860 680803460570287800352487 := by
  unfold tailWord_1325860
  simp only [CollatzResearch.WordTrace]
  refine ⟨24179043488321566852695517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32238724651095422470260689 24179043488321566852695517)
  ·
    refine ⟨9067141308120587569760819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24179043488321566852695517 9067141308120587569760819)
    ·
      refine ⟨13600711962180881354641229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9067141308120587569760819 13600711962180881354641229)
      ·
        refine ⟨5100266985817830507990461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13600711962180881354641229 5100266985817830507990461)
        ·
          refine ⟨1912600119681686440496423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5100266985817830507990461 1912600119681686440496423)
          ·
            refine ⟨2868900179522529660744635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1912600119681686440496423 2868900179522529660744635)
            ·
              refine ⟨4303350269283794491116953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2868900179522529660744635 4303350269283794491116953)
              ·
                refine ⟨3227512701962845868337715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4303350269283794491116953 3227512701962845868337715)
                ·
                  refine ⟨4841269052944268802506573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3227512701962845868337715 4841269052944268802506573)
                  ·
                    refine ⟨1815475894854100800939965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4841269052944268802506573 1815475894854100800939965)
                    ·
                      refine ⟨680803460570287800352487, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1815475894854100800939965 680803460570287800352487)
                      ·
                        rfl

theorem cell23_1325860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 3, 1, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 3, 1, 1, 2, 1, 3, 3].length) (baseStart_1325860 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1325860 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1325860 prefixEnd_1325860 := by exact prefixLift 1325860
  have htrace : WordTrace (prefixWord ++ tailWord_1325860) baseStart_1325860 baseEnd_1325860 := by
    simpa [prefixWord, tailWord_1325860, baseEnd_1325860] using wordTrace_append hprefix tailTrace_1325860
  have hstable : (prefixWord ++ tailWord_1325860).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1325860).length < 2 ^ (prefixWord ++ tailWord_1325860).sum := by decide
  have hdescent : baseEnd_1325860 < baseStart_1325860 := by decide
  rcases family_descends (prefixWord ++ tailWord_1325860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1325877 : List Nat := [1, 3, 3, 1, 3, 2, 2, 2, 2, 1, 3]
def baseStart_1325877 : Nat := 118140960795 + 1325877 * 2 ^ 59
def prefixEnd_1325877 : Nat := 4983230072969 + 3 ^ 40 * 1325877 * 2
def baseEnd_1325877 : Nat := 680812189741414233839909

theorem tailTrace_1325877 : CollatzResearch.WordTrace tailWord_1325877 prefixEnd_1325877 680812189741414233839909 := by
  unfold tailWord_1325877
  simp only [CollatzResearch.WordTrace]
  refine ⟨48358707017581545608759885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32239138011721030405839923 48358707017581545608759885)
  ·
    refine ⟨18134515131593079603284957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 48358707017581545608759885 18134515131593079603284957)
    ·
      refine ⟨6800443174347404851231859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18134515131593079603284957 6800443174347404851231859)
      ·
        refine ⟨10200664761521107276847789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6800443174347404851231859 10200664761521107276847789)
        ·
          refine ⟨3825249285570415228817921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10200664761521107276847789 3825249285570415228817921)
          ·
            refine ⟨2868936964177811421613441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3825249285570415228817921 2868936964177811421613441)
            ·
              refine ⟨2151702723133358566210081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2868936964177811421613441 2151702723133358566210081)
              ·
                refine ⟨1613777042350018924657561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2151702723133358566210081 1613777042350018924657561)
                ·
                  refine ⟨1210332781762514193493171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1613777042350018924657561 1210332781762514193493171)
                  ·
                    refine ⟨1815499172643771290239757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1210332781762514193493171 1815499172643771290239757)
                    ·
                      refine ⟨680812189741414233839909, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1815499172643771290239757 680812189741414233839909)
                      ·
                        rfl

theorem cell23_1325877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 2, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 2, 2, 2, 2, 1, 3].length) (baseStart_1325877 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1325877 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1325877 prefixEnd_1325877 := by exact prefixLift 1325877
  have htrace : WordTrace (prefixWord ++ tailWord_1325877) baseStart_1325877 baseEnd_1325877 := by
    simpa [prefixWord, tailWord_1325877, baseEnd_1325877] using wordTrace_append hprefix tailTrace_1325877
  have hstable : (prefixWord ++ tailWord_1325877).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1325877).length < 2 ^ (prefixWord ++ tailWord_1325877).sum := by decide
  have hdescent : baseEnd_1325877 < baseStart_1325877 := by decide
  rcases family_descends (prefixWord ++ tailWord_1325877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1325894 : List Nat := [6, 1, 1, 2, 2, 1, 2, 1, 1, 3, 3]
def baseStart_1325894 : Nat := 118140960795 + 1325894 * 2 ^ 59
def prefixEnd_1325894 : Nat := 4983230072969 + 3 ^ 40 * 1325894 * 2
def baseEnd_1325894 : Nat := 680820918912540667327331

theorem tailTrace_1325894 : CollatzResearch.WordTrace tailWord_1325894 prefixEnd_1325894 680820918912540667327331 := by
  unfold tailWord_1325894
  simp only [CollatzResearch.WordTrace]
  refine ⟨1511228970578748672254023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 32239551372346638341419157 1511228970578748672254023)
  ·
    refine ⟨2266843455868123008381035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1511228970578748672254023 2266843455868123008381035)
    ·
      refine ⟨3400265183802184512571553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2266843455868123008381035 3400265183802184512571553)
      ·
        refine ⟨2550198887851638384428665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3400265183802184512571553 2550198887851638384428665)
        ·
          refine ⟨1912649165888728788321499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2550198887851638384428665 1912649165888728788321499)
          ·
            refine ⟨2868973748833093182482249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1912649165888728788321499 2868973748833093182482249)
            ·
              refine ⟨2151730311624819886861687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2868973748833093182482249 2151730311624819886861687)
              ·
                refine ⟨3227595467437229830292531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2151730311624819886861687 3227595467437229830292531)
                ·
                  refine ⟨4841393201155844745438797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3227595467437229830292531 4841393201155844745438797)
                  ·
                    refine ⟨1815522450433441779539549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4841393201155844745438797 1815522450433441779539549)
                    ·
                      refine ⟨680820918912540667327331, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1815522450433441779539549 680820918912540667327331)
                      ·
                        rfl

theorem cell23_1325894_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 2, 1, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 2, 1, 2, 1, 1, 3, 3].length) (baseStart_1325894 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1325894 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1325894 prefixEnd_1325894 := by exact prefixLift 1325894
  have htrace : WordTrace (prefixWord ++ tailWord_1325894) baseStart_1325894 baseEnd_1325894 := by
    simpa [prefixWord, tailWord_1325894, baseEnd_1325894] using wordTrace_append hprefix tailTrace_1325894
  have hstable : (prefixWord ++ tailWord_1325894).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1325894).length < 2 ^ (prefixWord ++ tailWord_1325894).sum := by decide
  have hdescent : baseEnd_1325894 < baseStart_1325894 := by decide
  rcases family_descends (prefixWord ++ tailWord_1325894) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1325900 : List Nat := [2, 2, 1, 3, 3, 1, 1, 3, 1, 4, 2]
def baseStart_1325900 : Nat := 118140960795 + 1325900 * 2 ^ 59
def prefixEnd_1325900 : Nat := 4983230072969 + 3 ^ 40 * 1325900 * 2
def baseEnd_1325900 : Nat := 680823999796467643852303

theorem tailTrace_1325900 : CollatzResearch.WordTrace tailWord_1325900 prefixEnd_1325900 680823999796467643852303 := by
  unfold tailWord_1325900
  simp only [CollatzResearch.WordTrace]
  refine ⟨24179772948249110268423577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32239697264332147024564769 24179772948249110268423577)
  ·
    refine ⟨18134829711186832701317683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24179772948249110268423577 18134829711186832701317683)
    ·
      refine ⟨27202244566780249051976525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18134829711186832701317683 27202244566780249051976525)
      ·
        refine ⟨10200841712542593394491197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27202244566780249051976525 10200841712542593394491197)
        ·
          refine ⟨3825315642203472522934199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10200841712542593394491197 3825315642203472522934199)
          ·
            refine ⟨5737973463305208784401299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3825315642203472522934199 5737973463305208784401299)
            ·
              refine ⟨8606960194957813176601949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5737973463305208784401299 8606960194957813176601949)
              ·
                refine ⟨3227610073109179941225731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8606960194957813176601949 3227610073109179941225731)
                ·
                  refine ⟨4841415109663769911838597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3227610073109179941225731 4841415109663769911838597)
                  ·
                    refine ⟨907765333061956858469737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4841415109663769911838597 907765333061956858469737)
                    ·
                      refine ⟨680823999796467643852303, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 907765333061956858469737 680823999796467643852303)
                      ·
                        rfl

theorem cell23_1325900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 1, 3, 1, 4, 2].length) (baseStart_1325900 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1325900 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1325900 prefixEnd_1325900 := by exact prefixLift 1325900
  have htrace : WordTrace (prefixWord ++ tailWord_1325900) baseStart_1325900 baseEnd_1325900 := by
    simpa [prefixWord, tailWord_1325900, baseEnd_1325900] using wordTrace_append hprefix tailTrace_1325900
  have hstable : (prefixWord ++ tailWord_1325900).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1325900).length < 2 ^ (prefixWord ++ tailWord_1325900).sum := by decide
  have hdescent : baseEnd_1325900 < baseStart_1325900 := by decide
  rcases family_descends (prefixWord ++ tailWord_1325900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1325934 : List Nat := [4, 1, 2, 3, 2, 1, 1, 1, 4, 2, 2]
def baseStart_1325934 : Nat := 118140960795 + 1325934 * 2 ^ 59
def prefixEnd_1325934 : Nat := 4983230072969 + 3 ^ 40 * 1325934 * 2
def baseEnd_1325934 : Nat := 680841458138720510827147

theorem tailTrace_1325934 : CollatzResearch.WordTrace tailWord_1325934 prefixEnd_1325934 680841458138720510827147 := by
  unfold tailWord_1325934
  simp only [CollatzResearch.WordTrace]
  refine ⟨6045098247296880542948107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 32240523985583362895723237 6045098247296880542948107)
  ·
    refine ⟨9067647370945320814422161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6045098247296880542948107 9067647370945320814422161)
    ·
      refine ⟨6800735528208990610816621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9067647370945320814422161 6800735528208990610816621)
      ·
        refine ⟨2550275823078371479056233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6800735528208990610816621 2550275823078371479056233)
        ·
          refine ⟨1912706867308778609292175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2550275823078371479056233 1912706867308778609292175)
          ·
            refine ⟨2869060300963167913938263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1912706867308778609292175 2869060300963167913938263)
            ·
              refine ⟨4303590451444751870907395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2869060300963167913938263 4303590451444751870907395)
              ·
                refine ⟨6455385677167127806361093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4303590451444751870907395 6455385677167127806361093)
                ·
                  refine ⟨1210384814468836463692705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6455385677167127806361093 1210384814468836463692705)
                  ·
                    refine ⟨907788610851627347769529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1210384814468836463692705 907788610851627347769529)
                    ·
                      refine ⟨680841458138720510827147, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 907788610851627347769529 680841458138720510827147)
                      ·
                        rfl

theorem cell23_1325934_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 2, 1, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 2, 1, 1, 1, 4, 2, 2].length) (baseStart_1325934 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1325934 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1325934 prefixEnd_1325934 := by exact prefixLift 1325934
  have htrace : WordTrace (prefixWord ++ tailWord_1325934) baseStart_1325934 baseEnd_1325934 := by
    simpa [prefixWord, tailWord_1325934, baseEnd_1325934] using wordTrace_append hprefix tailTrace_1325934
  have hstable : (prefixWord ++ tailWord_1325934).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1325934).length < 2 ^ (prefixWord ++ tailWord_1325934).sum := by decide
  have hdescent : baseEnd_1325934 < baseStart_1325934 := by decide
  rcases family_descends (prefixWord ++ tailWord_1325934) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1325943 : List Nat := [1, 1, 3, 1, 1, 2, 1, 3, 1, 7, 2]
def baseStart_1325943 : Nat := 118140960795 + 1325943 * 2 ^ 59
def prefixEnd_1325943 : Nat := 4983230072969 + 3 ^ 40 * 1325943 * 2
def baseEnd_1325943 : Nat := 680846079464610975614605

theorem tailTrace_1325943 : CollatzResearch.WordTrace tailWord_1325943 prefixEnd_1325943 680846079464610975614605 := by
  unfold tailWord_1325943
  simp only [CollatzResearch.WordTrace]
  refine ⟨48361114235342438880662483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32240742823561625920441655 48361114235342438880662483)
  ·
    refine ⟨72541671353013658320993725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48361114235342438880662483 72541671353013658320993725)
    ·
      refine ⟨27203126757380121870372647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 72541671353013658320993725 27203126757380121870372647)
      ·
        refine ⟨40804690136070182805558971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27203126757380121870372647 40804690136070182805558971)
        ·
          refine ⟨61207035204105274208338457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40804690136070182805558971 61207035204105274208338457)
          ·
            refine ⟨45905276403078955656253843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 61207035204105274208338457 45905276403078955656253843)
            ·
              refine ⟨68857914604618433484380765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45905276403078955656253843 68857914604618433484380765)
              ·
                refine ⟨25821717976731912556642787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 68857914604618433484380765 25821717976731912556642787)
                ·
                  refine ⟨38732576965097868834964181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25821717976731912556642787 38732576965097868834964181)
                  ·
                    refine ⟨907794772619481300819473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 38732576965097868834964181 907794772619481300819473)
                    ·
                      refine ⟨680846079464610975614605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 907794772619481300819473 680846079464610975614605)
                      ·
                        rfl

theorem cell23_1325943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 3, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 3, 1, 7, 2].length) (baseStart_1325943 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1325943 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1325943 prefixEnd_1325943 := by exact prefixLift 1325943
  have htrace : WordTrace (prefixWord ++ tailWord_1325943) baseStart_1325943 baseEnd_1325943 := by
    simpa [prefixWord, tailWord_1325943, baseEnd_1325943] using wordTrace_append hprefix tailTrace_1325943
  have hstable : (prefixWord ++ tailWord_1325943).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1325943).length < 2 ^ (prefixWord ++ tailWord_1325943).sum := by decide
  have hdescent : baseEnd_1325943 < baseStart_1325943 := by decide
  rcases family_descends (prefixWord ++ tailWord_1325943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1325946 : List Nat := [3, 1, 1, 1, 1, 1, 3, 3, 1, 1, 7]
def baseStart_1325946 : Nat := 118140960795 + 1325946 * 2 ^ 59
def prefixEnd_1325946 : Nat := 4983230072969 + 3 ^ 40 * 1325946 * 2
def baseEnd_1325946 : Nat := 680847619906574463877091

theorem tailTrace_1325946 : CollatzResearch.WordTrace tailWord_1325946 prefixEnd_1325946 680847619906574463877091 := by
  unfold tailWord_1325946
  simp only [CollatzResearch.WordTrace]
  refine ⟨12090305913582892598255423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32240815769554380262014461 12090305913582892598255423)
  ·
    refine ⟨18135458870374338897383135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12090305913582892598255423 18135458870374338897383135)
    ·
      refine ⟨27203188305561508346074703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18135458870374338897383135 27203188305561508346074703)
      ·
        refine ⟨40804782458342262519112055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27203188305561508346074703 40804782458342262519112055)
        ·
          refine ⟨61207173687513393778668083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40804782458342262519112055 61207173687513393778668083)
          ·
            refine ⟨91810760531270090668002125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61207173687513393778668083 91810760531270090668002125)
            ·
              refine ⟨34429035199226284000500797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 91810760531270090668002125 34429035199226284000500797)
              ·
                refine ⟨12910888199709856500187799, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 34429035199226284000500797 12910888199709856500187799)
                ·
                  refine ⟨19366332299564784750281699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12910888199709856500187799 19366332299564784750281699)
                  ·
                    refine ⟨29049498449347177125422549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19366332299564784750281699 29049498449347177125422549)
                    ·
                      refine ⟨680847619906574463877091, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 29049498449347177125422549 680847619906574463877091)
                      ·
                        rfl

theorem cell23_1325946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 3, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 3, 3, 1, 1, 7].length) (baseStart_1325946 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1325946 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1325946 prefixEnd_1325946 := by exact prefixLift 1325946
  have htrace : WordTrace (prefixWord ++ tailWord_1325946) baseStart_1325946 baseEnd_1325946 := by
    simpa [prefixWord, tailWord_1325946, baseEnd_1325946] using wordTrace_append hprefix tailTrace_1325946
  have hstable : (prefixWord ++ tailWord_1325946).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1325946).length < 2 ^ (prefixWord ++ tailWord_1325946).sum := by decide
  have hdescent : baseEnd_1325946 < baseStart_1325946 := by decide
  rcases family_descends (prefixWord ++ tailWord_1325946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1325973 : List Nat := [1, 3, 2, 1, 1, 4, 2, 1, 1, 3, 4]
def baseStart_1325973 : Nat := 118140960795 + 1325973 * 2 ^ 59
def prefixEnd_1325973 : Nat := 4983230072969 + 3 ^ 40 * 1325973 * 2
def baseEnd_1325973 : Nat := 680861483884245858239467

theorem tailTrace_1325973 : CollatzResearch.WordTrace tailWord_1325973 prefixEnd_1325973 680861483884245858239467 := by
  unfold tailWord_1325973
  simp only [CollatzResearch.WordTrace]
  refine ⟨48362208425233754004254573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32241472283489169336169715 48362208425233754004254573)
  ·
    refine ⟨18135828159462657751595465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 48362208425233754004254573 18135828159462657751595465)
    ·
      refine ⟨13601871119596993313696599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18135828159462657751595465 13601871119596993313696599)
      ·
        refine ⟨20402806679395489970544899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13601871119596993313696599 20402806679395489970544899)
        ·
          refine ⟨30604210019093234955817349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20402806679395489970544899 30604210019093234955817349)
          ·
            refine ⟨5738289378579981554215753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 30604210019093234955817349 5738289378579981554215753)
            ·
              refine ⟨4303717033934986165661815, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5738289378579981554215753 4303717033934986165661815)
              ·
                refine ⟨6455575550902479248492723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4303717033934986165661815 6455575550902479248492723)
                ·
                  refine ⟨9683363326353718872739085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6455575550902479248492723 9683363326353718872739085)
                  ·
                    refine ⟨3631261247382644577277157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9683363326353718872739085 3631261247382644577277157)
                    ·
                      refine ⟨680861483884245858239467, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3631261247382644577277157 680861483884245858239467)
                      ·
                        rfl

theorem cell23_1325973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 2, 1, 1, 3, 4].length) (baseStart_1325973 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1325973 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1325973 prefixEnd_1325973 := by exact prefixLift 1325973
  have htrace : WordTrace (prefixWord ++ tailWord_1325973) baseStart_1325973 baseEnd_1325973 := by
    simpa [prefixWord, tailWord_1325973, baseEnd_1325973] using wordTrace_append hprefix tailTrace_1325973
  have hstable : (prefixWord ++ tailWord_1325973).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1325973).length < 2 ^ (prefixWord ++ tailWord_1325973).sum := by decide
  have hdescent : baseEnd_1325973 < baseStart_1325973 := by decide
  rcases family_descends (prefixWord ++ tailWord_1325973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1325997 : List Nat := [1, 5, 2, 3, 1, 1, 1, 1, 1, 2, 5]
def baseStart_1325997 : Nat := 118140960795 + 1325997 * 2 ^ 59
def prefixEnd_1325997 : Nat := 4983230072969 + 3 ^ 40 * 1325997 * 2
def baseEnd_1325997 : Nat := 680873807419953764339357

theorem tailTrace_1325997 : CollatzResearch.WordTrace tailWord_1325997 prefixEnd_1325997 680873807419953764339357 := by
  unfold tailWord_1325997
  simp only [CollatzResearch.WordTrace]
  refine ⟨48363083777146806103128245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32242055851431204068752163 48363083777146806103128245)
  ·
    refine ⟨4534039104107513072168273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 48363083777146806103128245 4534039104107513072168273)
    ·
      refine ⟨3400529328080634804126205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4534039104107513072168273 3400529328080634804126205)
      ·
        refine ⟨1275198498030238051547327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3400529328080634804126205 1275198498030238051547327)
        ·
          refine ⟨1912797747045357077320991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1275198498030238051547327 1912797747045357077320991)
          ·
            refine ⟨2869196620568035615981487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1912797747045357077320991 2869196620568035615981487)
            ·
              refine ⟨4303794930852053423972231, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2869196620568035615981487 4303794930852053423972231)
              ·
                refine ⟨6455692396278080135958347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4303794930852053423972231 6455692396278080135958347)
                ·
                  refine ⟨9683538594417120203937521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6455692396278080135958347 9683538594417120203937521)
                  ·
                    refine ⟨7262653945812840152953141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9683538594417120203937521 7262653945812840152953141)
                    ·
                      refine ⟨680873807419953764339357, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7262653945812840152953141 680873807419953764339357)
                      ·
                        rfl

theorem cell23_1325997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 1, 1, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 1, 1, 1, 1, 1, 2, 5].length) (baseStart_1325997 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1325997 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1325997 prefixEnd_1325997 := by exact prefixLift 1325997
  have htrace : WordTrace (prefixWord ++ tailWord_1325997) baseStart_1325997 baseEnd_1325997 := by
    simpa [prefixWord, tailWord_1325997, baseEnd_1325997] using wordTrace_append hprefix tailTrace_1325997
  have hstable : (prefixWord ++ tailWord_1325997).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1325997).length < 2 ^ (prefixWord ++ tailWord_1325997).sum := by decide
  have hdescent : baseEnd_1325997 < baseStart_1325997 := by decide
  rcases family_descends (prefixWord ++ tailWord_1325997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1326023 : List Nat := [1, 1, 4, 1, 1, 2, 2, 1, 2, 5, 3]
def baseStart_1326023 : Nat := 118140960795 + 1326023 * 2 ^ 59
def prefixEnd_1326023 : Nat := 4983230072969 + 3 ^ 40 * 1326023 * 2
def baseEnd_1326023 : Nat := 680887157916970662614237

theorem tailTrace_1326023 : CollatzResearch.WordTrace tailWord_1326023 prefixEnd_1326023 680887157916970662614237 := by
  unfold tailWord_1326023
  simp only [CollatzResearch.WordTrace]
  refine ⟨48364032075052612543574723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32242688050035075029049815 48364032075052612543574723)
  ·
    refine ⟨72546048112578918815362085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48364032075052612543574723 72546048112578918815362085)
    ·
      refine ⟨13602384021108547277880391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 72546048112578918815362085 13602384021108547277880391)
      ·
        refine ⟨20403576031662820916820587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13602384021108547277880391 20403576031662820916820587)
        ·
          refine ⟨30605364047494231375230881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20403576031662820916820587 30605364047494231375230881)
          ·
            refine ⟨22954023035620673531423161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30605364047494231375230881 22954023035620673531423161)
            ·
              refine ⟨17215517276715505148567371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22954023035620673531423161 17215517276715505148567371)
              ·
                refine ⟨25823275915073257722851057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17215517276715505148567371 25823275915073257722851057)
                ·
                  refine ⟨19367456936304943292138293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25823275915073257722851057 19367456936304943292138293)
                  ·
                    refine ⟨1815699087778588433637965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 19367456936304943292138293 1815699087778588433637965)
                    ·
                      refine ⟨680887157916970662614237, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1815699087778588433637965 680887157916970662614237)
                      ·
                        rfl

theorem cell23_1326023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 2, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 2, 1, 2, 5, 3].length) (baseStart_1326023 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1326023 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1326023 prefixEnd_1326023 := by exact prefixLift 1326023
  have htrace : WordTrace (prefixWord ++ tailWord_1326023) baseStart_1326023 baseEnd_1326023 := by
    simpa [prefixWord, tailWord_1326023, baseEnd_1326023] using wordTrace_append hprefix tailTrace_1326023
  have hstable : (prefixWord ++ tailWord_1326023).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1326023).length < 2 ^ (prefixWord ++ tailWord_1326023).sum := by decide
  have hdescent : baseEnd_1326023 < baseStart_1326023 := by decide
  rcases family_descends (prefixWord ++ tailWord_1326023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1326068 : List Nat := [2, 6, 2, 1, 1, 1, 1, 2, 3, 4]
def baseStart_1326068 : Nat := 118140960795 + 1326068 * 2 ^ 59
def prefixEnd_1326068 : Nat := 4983230072969 + 3 ^ 40 * 1326068 * 2
def baseEnd_1326068 : Nat := 226970088182140995517177

theorem tailTrace_1326068 : CollatzResearch.WordTrace tailWord_1326068 prefixEnd_1326068 226970088182140995517177 := by
  unfold tailWord_1326068
  simp only [CollatzResearch.WordTrace]
  refine ⟨24182836679944792614481429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32243782239926390152641905 24182836679944792614481429)
  ·
    refine ⟨1133570469372412153803817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 24182836679944792614481429 1133570469372412153803817)
    ·
      refine ⟨850177852029309115352863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1133570469372412153803817 850177852029309115352863)
      ·
        refine ⟨1275266778043963673029295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 850177852029309115352863 1275266778043963673029295)
        ·
          refine ⟨1912900167065945509543943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1275266778043963673029295 1912900167065945509543943)
          ·
            refine ⟨2869350250598918264315915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1912900167065945509543943 2869350250598918264315915)
            ·
              refine ⟨4304025375898377396473873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2869350250598918264315915 4304025375898377396473873)
              ·
                refine ⟨3228019031923783047355405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4304025375898377396473873 3228019031923783047355405)
                ·
                  refine ⟨1210507136971418642758277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3228019031923783047355405 1210507136971418642758277)
                  ·
                    refine ⟨226970088182140995517177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1210507136971418642758277 226970088182140995517177)
                    ·
                      rfl

theorem cell23_1326068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 1, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 1, 1, 1, 2, 3, 4].length) (baseStart_1326068 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1326068 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1326068 prefixEnd_1326068 := by exact prefixLift 1326068
  have htrace : WordTrace (prefixWord ++ tailWord_1326068) baseStart_1326068 baseEnd_1326068 := by
    simpa [prefixWord, tailWord_1326068, baseEnd_1326068] using wordTrace_append hprefix tailTrace_1326068
  have hstable : (prefixWord ++ tailWord_1326068).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1326068).length < 2 ^ (prefixWord ++ tailWord_1326068).sum := by decide
  have hdescent : baseEnd_1326068 < baseStart_1326068 := by decide
  rcases family_descends (prefixWord ++ tailWord_1326068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1326090 : List Nat := [3, 1, 2, 2, 3, 1, 2, 2, 1, 6]
def baseStart_1326090 : Nat := 118140960795 + 1326090 * 2 ^ 59
def prefixEnd_1326090 : Nat := 4983230072969 + 3 ^ 40 * 1326090 * 2
def baseEnd_1326090 : Nat := 226973853706940633492143

theorem tailTrace_1326090 : CollatzResearch.WordTrace tailWord_1326090 prefixEnd_1326090 226973853706940633492143 := by
  unfold tailWord_1326090
  simp only [CollatzResearch.WordTrace]
  refine ⟨12091618941452470746565931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32244317177206588657509149 12091618941452470746565931)
  ·
    refine ⟨18137428412178706119848897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12091618941452470746565931 18137428412178706119848897)
    ·
      refine ⟨13603071309134029589886673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18137428412178706119848897 13603071309134029589886673)
      ·
        refine ⟨10202303481850522192415005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13603071309134029589886673 10202303481850522192415005)
        ·
          refine ⟨3825863805693945822155627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10202303481850522192415005 3825863805693945822155627)
          ·
            refine ⟨5738795708540918733233441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3825863805693945822155627 5738795708540918733233441)
            ·
              refine ⟨4304096781405689049925081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5738795708540918733233441 4304096781405689049925081)
              ·
                refine ⟨3228072586054266787443811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4304096781405689049925081 3228072586054266787443811)
                ·
                  refine ⟨4842108879081400181165717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3228072586054266787443811 4842108879081400181165717)
                  ·
                    refine ⟨226973853706940633492143, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4842108879081400181165717 226973853706940633492143)
                    ·
                      rfl

theorem cell23_1326090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 2, 2, 1, 6].length) (baseStart_1326090 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1326090 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1326090 prefixEnd_1326090 := by exact prefixLift 1326090
  have htrace : WordTrace (prefixWord ++ tailWord_1326090) baseStart_1326090 baseEnd_1326090 := by
    simpa [prefixWord, tailWord_1326090, baseEnd_1326090] using wordTrace_append hprefix tailTrace_1326090
  have hstable : (prefixWord ++ tailWord_1326090).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1326090).length < 2 ^ (prefixWord ++ tailWord_1326090).sum := by decide
  have hdescent : baseEnd_1326090 < baseStart_1326090 := by decide
  rcases family_descends (prefixWord ++ tailWord_1326090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1326094 : List Nat := [4, 1, 1, 2, 2, 4, 2, 1, 1, 5]
def baseStart_1326094 : Nat := 118140960795 + 1326094 * 2 ^ 59
def prefixEnd_1326094 : Nat := 4983230072969 + 3 ^ 40 * 1326094 * 2
def baseEnd_1326094 : Nat := 226974538347813294942137

theorem tailTrace_1326094 : CollatzResearch.WordTrace tailWord_1326094 prefixEnd_1326094 226974538347813294942137 := by
  unfold tailWord_1326094
  simp only [CollatzResearch.WordTrace]
  refine ⟨6045827707224423958676167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 32244414438530261112939557 6045827707224423958676167)
  ·
    refine ⟨9068741560836635938014251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6045827707224423958676167 9068741560836635938014251)
    ·
      refine ⟨13603112341254953907021377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9068741560836635938014251 13603112341254953907021377)
      ·
        refine ⟨10202334255941215430266033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13603112341254953907021377 10202334255941215430266033)
        ·
          refine ⟨7651750691955911572699525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10202334255941215430266033 7651750691955911572699525)
          ·
            refine ⟨1434703254741733419881161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7651750691955911572699525 1434703254741733419881161)
            ·
              refine ⟨1076027441056300064910871, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1434703254741733419881161 1076027441056300064910871)
              ·
                refine ⟨1614041161584450097366307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1076027441056300064910871 1614041161584450097366307)
                ·
                  refine ⟨2421061742376675146049461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1614041161584450097366307 2421061742376675146049461)
                  ·
                    refine ⟨226974538347813294942137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2421061742376675146049461 226974538347813294942137)
                    ·
                      rfl

theorem cell23_1326094_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 4, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 4, 2, 1, 1, 5].length) (baseStart_1326094 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1326094 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1326094 prefixEnd_1326094 := by exact prefixLift 1326094
  have htrace : WordTrace (prefixWord ++ tailWord_1326094) baseStart_1326094 baseEnd_1326094 := by
    simpa [prefixWord, tailWord_1326094, baseEnd_1326094] using wordTrace_append hprefix tailTrace_1326094
  have hstable : (prefixWord ++ tailWord_1326094).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1326094).length < 2 ^ (prefixWord ++ tailWord_1326094).sum := by decide
  have hdescent : baseEnd_1326094 < baseStart_1326094 := by decide
  rcases family_descends (prefixWord ++ tailWord_1326094) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1326098 : List Nat := [3, 2, 5, 1, 2, 1, 1, 2, 6]
def baseStart_1326098 : Nat := 118140960795 + 1326098 * 2 ^ 59
def prefixEnd_1326098 : Nat := 4983230072969 + 3 ^ 40 * 1326098 * 2
def baseEnd_1326098 : Nat := 75658407662895318797377

theorem tailTrace_1326098 : CollatzResearch.WordTrace tailWord_1326098 prefixEnd_1326098 75658407662895318797377 := by
  unfold tailWord_1326098
  simp only [CollatzResearch.WordTrace]
  refine ⟨12091691887445225088138737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32244511699853933568369965 12091691887445225088138737)
  ·
    refine ⟨9068768915583918816104053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12091691887445225088138737 9068768915583918816104053)
    ·
      refine ⟨850197085835992389009755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 9068768915583918816104053 850197085835992389009755)
      ·
        refine ⟨1275295628753988583514633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 850197085835992389009755 1275295628753988583514633)
        ·
          refine ⟨956471721565491437635975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1275295628753988583514633 956471721565491437635975)
          ·
            refine ⟨1434707582348237156453963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 956471721565491437635975 1434707582348237156453963)
            ·
              refine ⟨2152061373522355734680945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1434707582348237156453963 2152061373522355734680945)
              ·
                refine ⟨1614046030141766801010709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2152061373522355734680945 1614046030141766801010709)
                ·
                  refine ⟨75658407662895318797377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1614046030141766801010709 75658407662895318797377)
                  ·
                    rfl

theorem cell23_1326098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 2, 1, 1, 2, 6].length) (baseStart_1326098 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1326098 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1326098 prefixEnd_1326098 := by exact prefixLift 1326098
  have htrace : WordTrace (prefixWord ++ tailWord_1326098) baseStart_1326098 baseEnd_1326098 := by
    simpa [prefixWord, tailWord_1326098, baseEnd_1326098] using wordTrace_append hprefix tailTrace_1326098
  have hstable : (prefixWord ++ tailWord_1326098).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1326098).length < 2 ^ (prefixWord ++ tailWord_1326098).sum := by decide
  have hdescent : baseEnd_1326098 < baseStart_1326098 := by decide
  rcases family_descends (prefixWord ++ tailWord_1326098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1326114 : List Nat := [3, 3, 1, 1, 1, 3, 1, 3, 3, 2, 2]
def baseStart_1326114 : Nat := 118140960795 + 1326114 * 2 ^ 59
def prefixEnd_1326114 : Nat := 4983230072969 + 3 ^ 40 * 1326114 * 2
def baseEnd_1326114 : Nat := 680933884656529806576319

theorem tailTrace_1326114 : CollatzResearch.WordTrace tailWord_1326114 prefixEnd_1326114 680933884656529806576319 := by
  unfold tailWord_1326114
  simp only [CollatzResearch.WordTrace]
  refine ⟨12091837779430733771284349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32244900745148623390091597 12091837779430733771284349)
  ·
    refine ⟨4534439167286525164231631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12091837779430733771284349 4534439167286525164231631)
    ·
      refine ⟨6801658750929787746347447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4534439167286525164231631 6801658750929787746347447)
      ·
        refine ⟨10202488126394681619521171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6801658750929787746347447 10202488126394681619521171)
        ·
          refine ⟨15303732189592022429281757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10202488126394681619521171 15303732189592022429281757)
          ·
            refine ⟨5738899571097008410980659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15303732189592022429281757 5738899571097008410980659)
            ·
              refine ⟨8608349356645512616470989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5738899571097008410980659 8608349356645512616470989)
              ·
                refine ⟨3228131008742067231176621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8608349356645512616470989 3228131008742067231176621)
                ·
                  refine ⟨1210549128278275211691233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3228131008742067231176621 1210549128278275211691233)
                  ·
                    refine ⟨907911846208706408768425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1210549128278275211691233 907911846208706408768425)
                    ·
                      refine ⟨680933884656529806576319, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 907911846208706408768425 680933884656529806576319)
                      ·
                        rfl

theorem cell23_1326114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 1, 3, 3, 2, 2].length) (baseStart_1326114 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1326114 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1326114 prefixEnd_1326114 := by exact prefixLift 1326114
  have htrace : WordTrace (prefixWord ++ tailWord_1326114) baseStart_1326114 baseEnd_1326114 := by
    simpa [prefixWord, tailWord_1326114, baseEnd_1326114] using wordTrace_append hprefix tailTrace_1326114
  have hstable : (prefixWord ++ tailWord_1326114).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1326114).length < 2 ^ (prefixWord ++ tailWord_1326114).sum := by decide
  have hdescent : baseEnd_1326114 < baseStart_1326114 := by decide
  rcases family_descends (prefixWord ++ tailWord_1326114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1326134 : List Nat := [5, 1, 2, 1, 1, 2, 1, 4, 1, 2, 3]
def baseStart_1326134 : Nat := 118140960795 + 1326134 * 2 ^ 59
def prefixEnd_1326134 : Nat := 4983230072969 + 3 ^ 40 * 1326134 * 2
def baseEnd_1326134 : Nat := 680944154269619728326227

theorem tailTrace_1326134 : CollatzResearch.WordTrace tailWord_1326134 prefixEnd_1326134 680944154269619728326227 := by
  unfold tailWord_1326134
  simp only [CollatzResearch.WordTrace]
  refine ⟨3023005036103154906304091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 32245387051766985667243637 3023005036103154906304091)
  ·
    refine ⟨4534507554154732359456137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3023005036103154906304091 4534507554154732359456137)
    ·
      refine ⟨3400880665616049269592103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4534507554154732359456137 3400880665616049269592103)
      ·
        refine ⟨5101320998424073904388155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3400880665616049269592103 5101320998424073904388155)
        ·
          refine ⟨7651981497636110856582233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5101320998424073904388155 7651981497636110856582233)
          ·
            refine ⟨5738986123227083142436675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7651981497636110856582233 5738986123227083142436675)
            ·
              refine ⟨8608479184840624713655013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5738986123227083142436675 8608479184840624713655013)
              ·
                refine ⟨1614089847157617133810315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8608479184840624713655013 1614089847157617133810315)
                ·
                  refine ⟨2421134770736425700715473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1614089847157617133810315 2421134770736425700715473)
                  ·
                    refine ⟨1815851078052319275536605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2421134770736425700715473 1815851078052319275536605)
                    ·
                      refine ⟨680944154269619728326227, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1815851078052319275536605 680944154269619728326227)
                      ·
                        rfl

theorem cell23_1326134_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 1, 4, 1, 2, 3].length) (baseStart_1326134 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1326134 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1326134 prefixEnd_1326134 := by exact prefixLift 1326134
  have htrace : WordTrace (prefixWord ++ tailWord_1326134) baseStart_1326134 baseEnd_1326134 := by
    simpa [prefixWord, tailWord_1326134, baseEnd_1326134] using wordTrace_append hprefix tailTrace_1326134
  have hstable : (prefixWord ++ tailWord_1326134).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1326134).length < 2 ^ (prefixWord ++ tailWord_1326134).sum := by decide
  have hdescent : baseEnd_1326134 < baseStart_1326134 := by decide
  rcases family_descends (prefixWord ++ tailWord_1326134) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1326137 : List Nat := [1, 2, 1, 5, 2, 3, 2, 7]
def baseStart_1326137 : Nat := 118140960795 + 1326137 * 2 ^ 59
def prefixEnd_1326137 : Nat := 4983230072969 + 3 ^ 40 * 1326137 * 2
def baseEnd_1326137 : Nat := 25220210915243822836619

theorem tailTrace_1326137 : CollatzResearch.WordTrace tailWord_1326137 prefixEnd_1326137 25220210915243822836619 := by
  unfold tailWord_1326137
  simp only [CollatzResearch.WordTrace]
  refine ⟨48368189996639610013224665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32245459997759740008816443 48368189996639610013224665)
  ·
    refine ⟨36276142497479707509918499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48368189996639610013224665 36276142497479707509918499)
    ·
      refine ⟨54414213746219561264877749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36276142497479707509918499 54414213746219561264877749)
      ·
        refine ⟨5101332538708083868582289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 54414213746219561264877749 5101332538708083868582289)
        ·
          refine ⟨3825999404031062901436717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5101332538708083868582289 3825999404031062901436717)
          ·
            refine ⟨1434749776511648588038769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3825999404031062901436717 1434749776511648588038769)
            ·
              refine ⟨1076062332383736441029077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1434749776511648588038769 1076062332383736441029077)
              ·
                refine ⟨25220210915243822836619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1076062332383736441029077 25220210915243822836619)
                ·
                  rfl

theorem cell23_1326137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 3, 2, 7].length) (baseStart_1326137 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1326137 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1326137 prefixEnd_1326137 := by exact prefixLift 1326137
  have htrace : WordTrace (prefixWord ++ tailWord_1326137) baseStart_1326137 baseEnd_1326137 := by
    simpa [prefixWord, tailWord_1326137, baseEnd_1326137] using wordTrace_append hprefix tailTrace_1326137
  have hstable : (prefixWord ++ tailWord_1326137).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1326137).length < 2 ^ (prefixWord ++ tailWord_1326137).sum := by decide
  have hdescent : baseEnd_1326137 < baseStart_1326137 := by decide
  rcases family_descends (prefixWord ++ tailWord_1326137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1326220 : List Nat := [2, 2, 1, 2, 1, 1, 1, 2, 3, 5, 3]
def baseStart_1326220 : Nat := 118140960795 + 1326220 * 2 ^ 59
def prefixEnd_1326220 : Nat := 4983230072969 + 3 ^ 40 * 1326220 * 2
def baseEnd_1326220 : Nat := 680988313605906391850831

theorem tailTrace_1326220 : CollatzResearch.WordTrace tailWord_1326220 prefixEnd_1326220 680988313605906391850831 := by
  unfold tailWord_1326220
  simp only [CollatzResearch.WordTrace]
  refine ⟨24185608627669457594248057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32247478170225943458997409 24185608627669457594248057)
  ·
    refine ⟨18139206470752093195686043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24185608627669457594248057 18139206470752093195686043)
    ·
      refine ⟨27208809706128139793529065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18139206470752093195686043 27208809706128139793529065)
      ·
        refine ⟨20406607279596104845146799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27208809706128139793529065 20406607279596104845146799)
        ·
          refine ⟨30609910919394157267720199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20406607279596104845146799 30609910919394157267720199)
          ·
            refine ⟨45914866379091235901580299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30609910919394157267720199 45914866379091235901580299)
            ·
              refine ⟨68872299568636853852370449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45914866379091235901580299 68872299568636853852370449)
              ·
                refine ⟨51654224676477640389277837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 68872299568636853852370449 51654224676477640389277837)
                ·
                  refine ⟨19370334253679115145979189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 51654224676477640389277837 19370334253679115145979189)
                  ·
                    refine ⟨1815968836282417044935549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 19370334253679115145979189 1815968836282417044935549)
                    ·
                      refine ⟨680988313605906391850831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1815968836282417044935549 680988313605906391850831)
                      ·
                        rfl

theorem cell23_1326220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 2, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 2, 3, 5, 3].length) (baseStart_1326220 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1326220 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1326220 prefixEnd_1326220 := by exact prefixLift 1326220
  have htrace : WordTrace (prefixWord ++ tailWord_1326220) baseStart_1326220 baseEnd_1326220 := by
    simpa [prefixWord, tailWord_1326220, baseEnd_1326220] using wordTrace_append hprefix tailTrace_1326220
  have hstable : (prefixWord ++ tailWord_1326220).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1326220).length < 2 ^ (prefixWord ++ tailWord_1326220).sum := by decide
  have hdescent : baseEnd_1326220 < baseStart_1326220 := by decide
  rcases family_descends (prefixWord ++ tailWord_1326220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1326237 : List Nat := [1, 4, 2, 1, 1, 2, 3, 1, 2, 3, 3]
def baseStart_1326237 : Nat := 118140960795 + 1326237 * 2 ^ 59
def prefixEnd_1326237 : Nat := 4983230072969 + 3 ^ 40 * 1326237 * 2
def baseEnd_1326237 : Nat := 680997042777032825338253

theorem tailTrace_1326237 : CollatzResearch.WordTrace tailWord_1326237 prefixEnd_1326237 680997042777032825338253 := by
  unfold tailWord_1326237
  simp only [CollatzResearch.WordTrace]
  refine ⟨48371837296277327091864965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32247891530851551394576643 48371837296277327091864965)
  ·
    refine ⟨9069719493051998829724681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 48371837296277327091864965 9069719493051998829724681)
    ·
      refine ⟨6802289619788999122293511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9069719493051998829724681 6802289619788999122293511)
      ·
        refine ⟨10203434429683498683440267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6802289619788999122293511 10203434429683498683440267)
        ·
          refine ⟨15305151644525248025160401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10203434429683498683440267 15305151644525248025160401)
          ·
            refine ⟨11478863733393936018870301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15305151644525248025160401 11478863733393936018870301)
            ·
              refine ⟨4304573900022726007076363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11478863733393936018870301 4304573900022726007076363)
              ·
                refine ⟨6456860850034089010614545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4304573900022726007076363 6456860850034089010614545)
                ·
                  refine ⟨4842645637525566757960909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6456860850034089010614545 4842645637525566757960909)
                  ·
                    refine ⟨1815992114072087534235341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4842645637525566757960909 1815992114072087534235341)
                    ·
                      refine ⟨680997042777032825338253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1815992114072087534235341 680997042777032825338253)
                      ·
                        rfl

theorem cell23_1326237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 3, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 3, 1, 2, 3, 3].length) (baseStart_1326237 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1326237 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1326237 prefixEnd_1326237 := by exact prefixLift 1326237
  have htrace : WordTrace (prefixWord ++ tailWord_1326237) baseStart_1326237 baseEnd_1326237 := by
    simpa [prefixWord, tailWord_1326237, baseEnd_1326237] using wordTrace_append hprefix tailTrace_1326237
  have hstable : (prefixWord ++ tailWord_1326237).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1326237).length < 2 ^ (prefixWord ++ tailWord_1326237).sum := by decide
  have hdescent : baseEnd_1326237 < baseStart_1326237 := by decide
  rcases family_descends (prefixWord ++ tailWord_1326237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1326238 : List Nat := [4, 3, 1, 1, 2, 1, 2, 3, 2, 2, 2]
def baseStart_1326238 : Nat := 118140960795 + 1326238 * 2 ^ 59
def prefixEnd_1326238 : Nat := 4983230072969 + 3 ^ 40 * 1326238 * 2
def baseEnd_1326238 : Nat := 680997556257687321425749

theorem tailTrace_1326238 : CollatzResearch.WordTrace tailWord_1326238 prefixEnd_1326238 680997556257687321425749 := by
  unfold tailWord_1326238
  simp only [CollatzResearch.WordTrace]
  refine ⟨6046484221159213032831421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 32247915846182469508434245 6046484221159213032831421)
  ·
    refine ⟨2267431582934704887311783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6046484221159213032831421 2267431582934704887311783)
    ·
      refine ⟨3401147374402057330967675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2267431582934704887311783 3401147374402057330967675)
      ·
        refine ⟨5101721061603085996451513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3401147374402057330967675 5101721061603085996451513)
        ·
          refine ⟨3826290796202314497338635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5101721061603085996451513 3826290796202314497338635)
          ·
            refine ⟨5739436194303471746007953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3826290796202314497338635 5739436194303471746007953)
            ·
              refine ⟨4304577145727603809505965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5739436194303471746007953 4304577145727603809505965)
              ·
                refine ⟨1614216429647851428564737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4304577145727603809505965 1614216429647851428564737)
                ·
                  refine ⟨1210662322235888571423553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1614216429647851428564737 1210662322235888571423553)
                  ·
                    refine ⟨907996741676916428567665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1210662322235888571423553 907996741676916428567665)
                    ·
                      refine ⟨680997556257687321425749, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 907996741676916428567665 680997556257687321425749)
                      ·
                        rfl

theorem cell23_1326238_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 2, 3, 2, 2, 2].length) (baseStart_1326238 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1326238 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1326238 prefixEnd_1326238 := by exact prefixLift 1326238
  have htrace : WordTrace (prefixWord ++ tailWord_1326238) baseStart_1326238 baseEnd_1326238 := by
    simpa [prefixWord, tailWord_1326238, baseEnd_1326238] using wordTrace_append hprefix tailTrace_1326238
  have hstable : (prefixWord ++ tailWord_1326238).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1326238).length < 2 ^ (prefixWord ++ tailWord_1326238).sum := by decide
  have hdescent : baseEnd_1326238 < baseStart_1326238 := by decide
  rcases family_descends (prefixWord ++ tailWord_1326238) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1326240 : List Nat := [2, 1, 1, 4, 2, 1, 2, 2, 1, 7]
def baseStart_1326240 : Nat := 118140960795 + 1326240 * 2 ^ 59
def prefixEnd_1326240 : Nat := 4983230072969 + 3 ^ 40 * 1326240 * 2
def baseEnd_1326240 : Nat := 226999527739665437866913

theorem tailTrace_1326240 : CollatzResearch.WordTrace tailWord_1326240 prefixEnd_1326240 226999527739665437866913 := by
  unfold tailWord_1326240
  simp only [CollatzResearch.WordTrace]
  refine ⟨24185973357633229302112087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32247964476844305736149449 24185973357633229302112087)
  ·
    refine ⟨36278960036449843953168131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24185973357633229302112087 36278960036449843953168131)
    ·
      refine ⟨54418440054674765929752197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36278960036449843953168131 54418440054674765929752197)
      ·
        refine ⟨10203457510251518611828537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 54418440054674765929752197 10203457510251518611828537)
        ·
          refine ⟨7652593132688638958871403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10203457510251518611828537 7652593132688638958871403)
          ·
            refine ⟨11478889699032958438307105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7652593132688638958871403 11478889699032958438307105)
            ·
              refine ⟨8609167274274718828730329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11478889699032958438307105 8609167274274718828730329)
              ·
                refine ⟨6456875455706039121547747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8609167274274718828730329 6456875455706039121547747)
                ·
                  refine ⟨9685313183559058682321621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6456875455706039121547747 9685313183559058682321621)
                  ·
                    refine ⟨226999527739665437866913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 9685313183559058682321621 226999527739665437866913)
                    ·
                      rfl

theorem cell23_1326240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 2, 2, 1, 7].length) (baseStart_1326240 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1326240 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1326240 prefixEnd_1326240 := by exact prefixLift 1326240
  have htrace : WordTrace (prefixWord ++ tailWord_1326240) baseStart_1326240 baseEnd_1326240 := by
    simpa [prefixWord, tailWord_1326240, baseEnd_1326240] using wordTrace_append hprefix tailTrace_1326240
  have hstable : (prefixWord ++ tailWord_1326240).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1326240).length < 2 ^ (prefixWord ++ tailWord_1326240).sum := by decide
  have hdescent : baseEnd_1326240 < baseStart_1326240 := by decide
  rcases family_descends (prefixWord ++ tailWord_1326240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1326257 : List Nat := [1, 2, 2, 5, 1, 2, 1, 1, 1, 7]
def baseStart_1326257 : Nat := 118140960795 + 1326257 * 2 ^ 59
def prefixEnd_1326257 : Nat := 4983230072969 + 3 ^ 40 * 1326257 * 2
def baseEnd_1326257 : Nat := 227002437463374249029387

theorem tailTrace_1326257 : CollatzResearch.WordTrace tailWord_1326257 prefixEnd_1326257 227002437463374249029387 := by
  unfold tailWord_1326257
  simp only [CollatzResearch.WordTrace]
  refine ⟨48372566756204870507593025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32248377837469913671728683 48372566756204870507593025)
  ·
    refine ⟨36279425067153652880694769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48372566756204870507593025 36279425067153652880694769)
    ·
      refine ⟨27209568800365239660521077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36279425067153652880694769 27209568800365239660521077)
      ·
        refine ⟨2550897075034241218173851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 27209568800365239660521077 2550897075034241218173851)
        ·
          refine ⟨3826345612551361827260777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2550897075034241218173851 3826345612551361827260777)
          ·
            refine ⟨2869759209413521370445583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3826345612551361827260777 2869759209413521370445583)
            ·
              refine ⟨4304638814120282055668375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2869759209413521370445583 4304638814120282055668375)
              ·
                refine ⟨6456958221180423083502563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4304638814120282055668375 6456958221180423083502563)
                ·
                  refine ⟨9685437331770634625253845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6456958221180423083502563 9685437331770634625253845)
                  ·
                    refine ⟨227002437463374249029387, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 9685437331770634625253845 227002437463374249029387)
                    ·
                      rfl

theorem cell23_1326257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 2, 1, 1, 1, 7].length) (baseStart_1326257 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1326257 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1326257 prefixEnd_1326257 := by exact prefixLift 1326257
  have htrace : WordTrace (prefixWord ++ tailWord_1326257) baseStart_1326257 baseEnd_1326257 := by
    simpa [prefixWord, tailWord_1326257, baseEnd_1326257] using wordTrace_append hprefix tailTrace_1326257
  have hstable : (prefixWord ++ tailWord_1326257).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1326257).length < 2 ^ (prefixWord ++ tailWord_1326257).sum := by decide
  have hdescent : baseEnd_1326257 < baseStart_1326257 := by decide
  rcases family_descends (prefixWord ++ tailWord_1326257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1326278 : List Nat := [6, 1, 2, 2, 1, 1, 2, 1, 7]
def baseStart_1326278 : Nat := 118140960795 + 1326278 * 2 ^ 59
def prefixEnd_1326278 : Nat := 4983230072969 + 3 ^ 40 * 1326278 * 2
def baseEnd_1326278 : Nat := 75668677275985240547285

theorem tailTrace_1326278 : CollatzResearch.WordTrace tailWord_1326278 prefixEnd_1326278 75668677275985240547285 := by
  unfold tailWord_1326278
  simp only [CollatzResearch.WordTrace]
  refine ⟨1511666646535274721690859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 32248888459419194062738325 1511666646535274721690859)
  ·
    refine ⟨2267499969802912082536289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1511666646535274721690859 2267499969802912082536289)
    ·
      refine ⟨1700624977352184061902217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2267499969802912082536289 1700624977352184061902217)
      ·
        refine ⟨1275468733014138046426663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1700624977352184061902217 1275468733014138046426663)
        ·
          refine ⟨1913203099521207069639995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1275468733014138046426663 1913203099521207069639995)
          ·
            refine ⟨2869804649281810604459993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1913203099521207069639995 2869804649281810604459993)
            ·
              refine ⟨2152353486961357953344995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2869804649281810604459993 2152353486961357953344995)
              ·
                refine ⟨3228530230442036930017493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2152353486961357953344995 3228530230442036930017493)
                ·
                  refine ⟨75668677275985240547285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3228530230442036930017493 75668677275985240547285)
                  ·
                    rfl

theorem cell23_1326278_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 1, 1, 2, 1, 7].length) (baseStart_1326278 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1326278 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1326278 prefixEnd_1326278 := by exact prefixLift 1326278
  have htrace : WordTrace (prefixWord ++ tailWord_1326278) baseStart_1326278 baseEnd_1326278 := by
    simpa [prefixWord, tailWord_1326278, baseEnd_1326278] using wordTrace_append hprefix tailTrace_1326278
  have hstable : (prefixWord ++ tailWord_1326278).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1326278).length < 2 ^ (prefixWord ++ tailWord_1326278).sum := by decide
  have hdescent : baseEnd_1326278 < baseStart_1326278 := by decide
  rcases family_descends (prefixWord ++ tailWord_1326278) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1326280 : List Nat := [2, 1, 3, 1, 2, 1, 2, 1, 2, 3, 5]
def baseStart_1326280 : Nat := 118140960795 + 1326280 * 2 ^ 59
def prefixEnd_1326280 : Nat := 4983230072969 + 3 ^ 40 * 1326280 * 2
def baseEnd_1326280 : Nat := 681019122445176157100555

theorem tailTrace_1326280 : CollatzResearch.WordTrace tailWord_1326280 prefixEnd_1326280 681019122445176157100555 := by
  unfold tailWord_1326280
  simp only [CollatzResearch.WordTrace]
  refine ⟨24186702817560772717840147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32248937090081030290453529 24186702817560772717840147)
  ·
    refine ⟨36280054226341159076760221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24186702817560772717840147 36280054226341159076760221)
    ·
      refine ⟨13605020334877934653785083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 36280054226341159076760221 13605020334877934653785083)
      ·
        refine ⟨20407530502316901980677625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13605020334877934653785083 20407530502316901980677625)
        ·
          refine ⟨15305647876737676485508219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20407530502316901980677625 15305647876737676485508219)
          ·
            refine ⟨22958471815106514728262329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15305647876737676485508219 22958471815106514728262329)
            ·
              refine ⟨17218853861329886046196747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22958471815106514728262329 17218853861329886046196747)
              ·
                refine ⟨25828280791994829069295121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17218853861329886046196747 25828280791994829069295121)
                ·
                  refine ⟨19371210593996121801971341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25828280791994829069295121 19371210593996121801971341)
                  ·
                    refine ⟨7264203972748545675739253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19371210593996121801971341 7264203972748545675739253)
                    ·
                      refine ⟨681019122445176157100555, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7264203972748545675739253 681019122445176157100555)
                      ·
                        rfl

theorem cell23_1326280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 2, 1, 2, 3, 5].length) (baseStart_1326280 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1326280 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1326280 prefixEnd_1326280 := by exact prefixLift 1326280
  have htrace : WordTrace (prefixWord ++ tailWord_1326280) baseStart_1326280 baseEnd_1326280 := by
    simpa [prefixWord, tailWord_1326280, baseEnd_1326280] using wordTrace_append hprefix tailTrace_1326280
  have hstable : (prefixWord ++ tailWord_1326280).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1326280).length < 2 ^ (prefixWord ++ tailWord_1326280).sum := by decide
  have hdescent : baseEnd_1326280 < baseStart_1326280 := by decide
  rcases family_descends (prefixWord ++ tailWord_1326280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1326317 : List Nat := [1, 5, 1, 2, 2, 1, 1, 2, 8]
def baseStart_1326317 : Nat := 118140960795 + 1326317 * 2 ^ 59
def prefixEnd_1326317 : Nat := 4983230072969 + 3 ^ 40 * 1326317 * 2
def baseEnd_1326317 : Nat := 75670902358821390259765

theorem tailTrace_1326317 : CollatzResearch.WordTrace tailWord_1326317 prefixEnd_1326317 75670902358821390259765 := by
  unfold tailWord_1326317
  simp only [CollatzResearch.WordTrace]
  refine ⟨48374755135987500754777205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32249836757325000503184803 48374755135987500754777205)
  ·
    refine ⟨4535133293998828195760363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 48374755135987500754777205 4535133293998828195760363)
    ·
      refine ⟨6802699940998242293640545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4535133293998828195760363 6802699940998242293640545)
      ·
        refine ⟨5102024955748681720230409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6802699940998242293640545 5102024955748681720230409)
        ·
          refine ⟨3826518716811511290172807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5102024955748681720230409 3826518716811511290172807)
          ·
            refine ⟨5739778075217266935259211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3826518716811511290172807 5739778075217266935259211)
            ·
              refine ⟨8609667112825900402888817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5739778075217266935259211 8609667112825900402888817)
              ·
                refine ⟨6457250334619425302166613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8609667112825900402888817 6457250334619425302166613)
                ·
                  refine ⟨75670902358821390259765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 6457250334619425302166613 75670902358821390259765)
                  ·
                    rfl

theorem cell23_1326317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 1, 2, 8].length) (baseStart_1326317 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1326317 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1326317 prefixEnd_1326317 := by exact prefixLift 1326317
  have htrace : WordTrace (prefixWord ++ tailWord_1326317) baseStart_1326317 baseEnd_1326317 := by
    simpa [prefixWord, tailWord_1326317, baseEnd_1326317] using wordTrace_append hprefix tailTrace_1326317
  have hstable : (prefixWord ++ tailWord_1326317).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1326317).length < 2 ^ (prefixWord ++ tailWord_1326317).sum := by decide
  have hdescent : baseEnd_1326317 < baseStart_1326317 := by decide
  rcases family_descends (prefixWord ++ tailWord_1326317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1326338 : List Nat := [3, 4, 1, 1, 3, 2, 1, 1, 3, 4]
def baseStart_1326338 : Nat := 118140960795 + 1326338 * 2 ^ 59
def prefixEnd_1326338 : Nat := 4983230072969 + 3 ^ 40 * 1326338 * 2
def baseEnd_1326338 : Nat := 227016301441045643391763

theorem tailTrace_1326338 : CollatzResearch.WordTrace tailWord_1326338 prefixEnd_1326338 227016301441045643391763 := by
  unfold tailWord_1326338
  simp only [CollatzResearch.WordTrace]
  refine ⟨12093880267227855335322917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32250347379274280894194445 12093880267227855335322917)
  ·
    refine ⟨2267602550105222875373047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 12093880267227855335322917 2267602550105222875373047)
    ·
      refine ⟨3401403825157834313059571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2267602550105222875373047 3401403825157834313059571)
      ·
        refine ⟨5102105737736751469589357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3401403825157834313059571 5102105737736751469589357)
        ·
          refine ⟨1913289651651281801096009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5102105737736751469589357 1913289651651281801096009)
          ·
            refine ⟨1434967238738461350822007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1913289651651281801096009 1434967238738461350822007)
            ·
              refine ⟨2152450858107692026233011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1434967238738461350822007 2152450858107692026233011)
              ·
                refine ⟨3228676287161538039349517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2152450858107692026233011 3228676287161538039349517)
                ·
                  refine ⟨1210753607685576764756069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3228676287161538039349517 1210753607685576764756069)
                  ·
                    refine ⟨227016301441045643391763, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1210753607685576764756069 227016301441045643391763)
                    ·
                      rfl

theorem cell23_1326338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 3, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 3, 2, 1, 1, 3, 4].length) (baseStart_1326338 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1326338 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1326338 prefixEnd_1326338 := by exact prefixLift 1326338
  have htrace : WordTrace (prefixWord ++ tailWord_1326338) baseStart_1326338 baseEnd_1326338 := by
    simpa [prefixWord, tailWord_1326338, baseEnd_1326338] using wordTrace_append hprefix tailTrace_1326338
  have hstable : (prefixWord ++ tailWord_1326338).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1326338).length < 2 ^ (prefixWord ++ tailWord_1326338).sum := by decide
  have hdescent : baseEnd_1326338 < baseStart_1326338 := by decide
  rcases family_descends (prefixWord ++ tailWord_1326338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1326364 : List Nat := [2, 2, 3, 1, 1, 1, 5, 2, 1, 5]
def baseStart_1326364 : Nat := 118140960795 + 1326364 * 2 ^ 59
def prefixEnd_1326364 : Nat := 4983230072969 + 3 ^ 40 * 1326364 * 2
def baseEnd_1326364 : Nat := 227020751606717942816723

theorem tailTrace_1326364 : CollatzResearch.WordTrace tailWord_1326364 prefixEnd_1326364 227020751606717942816723 := by
  unfold tailWord_1326364
  simp only [CollatzResearch.WordTrace]
  refine ⟨24188234683408613890869073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32250979577878151854492097 24188234683408613890869073)
  ·
    refine ⟨18141176012556460418151805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24188234683408613890869073 18141176012556460418151805)
    ·
      refine ⟨6802941004708672656806927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18141176012556460418151805 6802941004708672656806927)
      ·
        refine ⟨10204411507063008985210391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6802941004708672656806927 10204411507063008985210391)
        ·
          refine ⟨15306617260594513477815587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10204411507063008985210391 15306617260594513477815587)
          ·
            refine ⟨22959925890891770216723381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15306617260594513477815587 22959925890891770216723381)
            ·
              refine ⟨2152493052271103457817817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 22959925890891770216723381 2152493052271103457817817)
              ·
                refine ⟨1614369789203327593363363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2152493052271103457817817 1614369789203327593363363)
                ·
                  refine ⟨2421554683804991390045045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1614369789203327593363363 2421554683804991390045045)
                  ·
                    refine ⟨227020751606717942816723, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2421554683804991390045045 227020751606717942816723)
                    ·
                      rfl

theorem cell23_1326364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 5, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 5, 2, 1, 5].length) (baseStart_1326364 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1326364 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1326364 prefixEnd_1326364 := by exact prefixLift 1326364
  have htrace : WordTrace (prefixWord ++ tailWord_1326364) baseStart_1326364 baseEnd_1326364 := by
    simpa [prefixWord, tailWord_1326364, baseEnd_1326364] using wordTrace_append hprefix tailTrace_1326364
  have hstable : (prefixWord ++ tailWord_1326364).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1326364).length < 2 ^ (prefixWord ++ tailWord_1326364).sum := by decide
  have hdescent : baseEnd_1326364 < baseStart_1326364 := by decide
  rcases family_descends (prefixWord ++ tailWord_1326364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1326371 : List Nat := [1, 1, 1, 4, 2, 4, 2, 1, 2, 3, 2]
def baseStart_1326371 : Nat := 118140960795 + 1326371 * 2 ^ 59
def prefixEnd_1326371 : Nat := 4983230072969 + 3 ^ 40 * 1326371 * 2
def baseEnd_1326371 : Nat := 681065849184735301062637

theorem tailTrace_1326371 : CollatzResearch.WordTrace tailWord_1326371 prefixEnd_1326371 681065849184735301062637 := by
  unfold tailWord_1326371
  simp only [CollatzResearch.WordTrace]
  refine ⟨48376724677791867977242967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32251149785194578651495311 48376724677791867977242967)
  ·
    refine ⟨72565087016687801965864451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48376724677791867977242967 72565087016687801965864451)
    ·
      refine ⟨108847630525031702948796677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72565087016687801965864451 108847630525031702948796677)
      ·
        refine ⟨20408930723443444302899377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 108847630525031702948796677 20408930723443444302899377)
        ·
          refine ⟨15306698042582583227174533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20408930723443444302899377 15306698042582583227174533)
          ·
            refine ⟨2870005882984234355095225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 15306698042582583227174533 2870005882984234355095225)
            ·
              refine ⟨2152504412238175766321419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2870005882984234355095225 2152504412238175766321419)
              ·
                refine ⟨3228756618357263649482129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2152504412238175766321419 3228756618357263649482129)
                ·
                  refine ⟨2421567463767947737111597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3228756618357263649482129 2421567463767947737111597)
                  ·
                    refine ⟨908087798912980401416849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2421567463767947737111597 908087798912980401416849)
                    ·
                      refine ⟨681065849184735301062637, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 908087798912980401416849 681065849184735301062637)
                      ·
                        rfl

theorem cell23_1326371_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 4, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 4, 2, 1, 2, 3, 2].length) (baseStart_1326371 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1326371 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1326371 prefixEnd_1326371 := by exact prefixLift 1326371
  have htrace : WordTrace (prefixWord ++ tailWord_1326371) baseStart_1326371 baseEnd_1326371 := by
    simpa [prefixWord, tailWord_1326371, baseEnd_1326371] using wordTrace_append hprefix tailTrace_1326371
  have hstable : (prefixWord ++ tailWord_1326371).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1326371).length < 2 ^ (prefixWord ++ tailWord_1326371).sum := by decide
  have hdescent : baseEnd_1326371 < baseStart_1326371 := by decide
  rcases family_descends (prefixWord ++ tailWord_1326371) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1326407 : List Nat := [1, 1, 4, 1, 2, 3, 3, 8]
def baseStart_1326407 : Nat := 118140960795 + 1326407 * 2 ^ 59
def prefixEnd_1326407 : Nat := 4983230072969 + 3 ^ 40 * 1326407 * 2
def baseEnd_1326407 : Nat := 25225345721788783711573

theorem tailTrace_1326407 : CollatzResearch.WordTrace tailWord_1326407 prefixEnd_1326407 25225345721788783711573 := by
  unfold tailWord_1326407
  simp only [CollatzResearch.WordTrace]
  refine ⟨48378037705661446125553475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32252025137107630750368983 48378037705661446125553475)
  ·
    refine ⟨72567056558492169188330213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48378037705661446125553475 72567056558492169188330213)
    ·
      refine ⟨13606323104717281722811915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 72567056558492169188330213 13606323104717281722811915)
      ·
        refine ⟨20409484657075922584217873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13606323104717281722811915 20409484657075922584217873)
        ·
          refine ⟨15307113492806941938163405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20409484657075922584217873 15307113492806941938163405)
          ·
            refine ⟨5740167559802603226811277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15307113492806941938163405 5740167559802603226811277)
            ·
              refine ⟨2152562834925976210054229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5740167559802603226811277 2152562834925976210054229)
              ·
                refine ⟨25225345721788783711573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 2152562834925976210054229 25225345721788783711573)
                ·
                  rfl

theorem cell23_1326407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 3, 8].length) (baseStart_1326407 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1326407 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1326407 prefixEnd_1326407 := by exact prefixLift 1326407
  have htrace : WordTrace (prefixWord ++ tailWord_1326407) baseStart_1326407 baseEnd_1326407 := by
    simpa [prefixWord, tailWord_1326407, baseEnd_1326407] using wordTrace_append hprefix tailTrace_1326407
  have hstable : (prefixWord ++ tailWord_1326407).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1326407).length < 2 ^ (prefixWord ++ tailWord_1326407).sum := by decide
  have hdescent : baseEnd_1326407 < baseStart_1326407 := by decide
  rcases family_descends (prefixWord ++ tailWord_1326407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1326414 : List Nat := [4, 1, 1, 1, 1, 1, 6, 1, 1, 2, 4]
def baseStart_1326414 : Nat := 118140960795 + 1326414 * 2 ^ 59
def prefixEnd_1326414 : Nat := 4983230072969 + 3 ^ 40 * 1326414 * 2
def baseEnd_1326414 : Nat := 681087928852878632824939

theorem tailTrace_1326414 : CollatzResearch.WordTrace tailWord_1326414 prefixEnd_1326414 681087928852878632824939 := by
  unfold tailWord_1326414
  simp only [CollatzResearch.WordTrace]
  refine ⟨6047286627079510790132287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 32252195344424057547372197 6047286627079510790132287)
  ·
    refine ⟨9070929940619266185198431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6047286627079510790132287 9070929940619266185198431)
    ·
      refine ⟨13606394910928899277797647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9070929940619266185198431 13606394910928899277797647)
      ·
        refine ⟨20409592366393348916696471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13606394910928899277797647 20409592366393348916696471)
        ·
          refine ⟨30614388549590023375044707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20409592366393348916696471 30614388549590023375044707)
          ·
            refine ⟨45921582824385035062567061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30614388549590023375044707 45921582824385035062567061)
            ·
              refine ⟨2152574194893048518557831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 45921582824385035062567061 2152574194893048518557831)
              ·
                refine ⟨3228861292339572777836747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2152574194893048518557831 3228861292339572777836747)
                ·
                  refine ⟨4843291938509359166755121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3228861292339572777836747 4843291938509359166755121)
                  ·
                    refine ⟨3632468953882019375066341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4843291938509359166755121 3632468953882019375066341)
                    ·
                      refine ⟨681087928852878632824939, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3632468953882019375066341 681087928852878632824939)
                      ·
                        rfl

theorem cell23_1326414_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 6, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 6, 1, 1, 2, 4].length) (baseStart_1326414 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1326414 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1326414 prefixEnd_1326414 := by exact prefixLift 1326414
  have htrace : WordTrace (prefixWord ++ tailWord_1326414) baseStart_1326414 baseEnd_1326414 := by
    simpa [prefixWord, tailWord_1326414, baseEnd_1326414] using wordTrace_append hprefix tailTrace_1326414
  have hstable : (prefixWord ++ tailWord_1326414).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1326414).length < 2 ^ (prefixWord ++ tailWord_1326414).sum := by decide
  have hdescent : baseEnd_1326414 < baseStart_1326414 := by decide
  rcases family_descends (prefixWord ++ tailWord_1326414) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1326422 : List Nat := [5, 2, 3, 1, 1, 1, 1, 1, 1, 5, 2]
def baseStart_1326422 : Nat := 118140960795 + 1326422 * 2 ^ 59
def prefixEnd_1326422 : Nat := 4983230072969 + 3 ^ 40 * 1326422 * 2
def baseEnd_1326422 : Nat := 681092036698114601524903

theorem tailTrace_1326422 : CollatzResearch.WordTrace tailWord_1326422 prefixEnd_1326422 681092036698114601524903 := by
  unfold tailWord_1326422
  simp only [CollatzResearch.WordTrace]
  refine ⟨3023661550037943980459345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 32252389867071402458233013 3023661550037943980459345)
  ·
    refine ⟨2267746162528457985344509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3023661550037943980459345 2267746162528457985344509)
    ·
      refine ⟨850404810948171744504191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2267746162528457985344509 850404810948171744504191)
      ·
        refine ⟨1275607216422257616756287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 850404810948171744504191 1275607216422257616756287)
        ·
          refine ⟨1913410824633386425134431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1275607216422257616756287 1913410824633386425134431)
          ·
            refine ⟨2870116236950079637701647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1913410824633386425134431 2870116236950079637701647)
            ·
              refine ⟨4305174355425119456552471, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2870116236950079637701647 4305174355425119456552471)
              ·
                refine ⟨6457761533137679184828707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4305174355425119456552471 6457761533137679184828707)
                ·
                  refine ⟨9686642299706518777243061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6457761533137679184828707 9686642299706518777243061)
                  ·
                    refine ⟨908122715597486135366537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9686642299706518777243061 908122715597486135366537)
                    ·
                      refine ⟨681092036698114601524903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 908122715597486135366537 681092036698114601524903)
                      ·
                        rfl

theorem cell23_1326422_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 1, 1, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 1, 1, 1, 1, 1, 5, 2].length) (baseStart_1326422 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1326422 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1326422 prefixEnd_1326422 := by exact prefixLift 1326422
  have htrace : WordTrace (prefixWord ++ tailWord_1326422) baseStart_1326422 baseEnd_1326422 := by
    simpa [prefixWord, tailWord_1326422, baseEnd_1326422] using wordTrace_append hprefix tailTrace_1326422
  have hstable : (prefixWord ++ tailWord_1326422).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1326422).length < 2 ^ (prefixWord ++ tailWord_1326422).sum := by decide
  have hdescent : baseEnd_1326422 < baseStart_1326422 := by decide
  rcases family_descends (prefixWord ++ tailWord_1326422) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1326429 : List Nat := [1, 4, 5, 1, 1, 1, 2, 3, 1, 1, 3]
def baseStart_1326429 : Nat := 118140960795 + 1326429 * 2 ^ 59
def prefixEnd_1326429 : Nat := 4983230072969 + 3 ^ 40 * 1326429 * 2
def baseEnd_1326429 : Nat := 681095631062696074137371

theorem tailTrace_1326429 : CollatzResearch.WordTrace tailWord_1326429 prefixEnd_1326429 681095631062696074137371 := by
  unfold tailWord_1326429
  simp only [CollatzResearch.WordTrace]
  refine ⟨48378840111581743882854341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32252560074387829255236227 48378840111581743882854341)
  ·
    refine ⟨9071032520921576978035189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 48378840111581743882854341 9071032520921576978035189)
    ·
      refine ⟨850409298836397841690799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 9071032520921576978035189 850409298836397841690799)
      ·
        refine ⟨1275613948254596762536199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 850409298836397841690799 1275613948254596762536199)
        ·
          refine ⟨1913420922381895143804299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1275613948254596762536199 1913420922381895143804299)
          ·
            refine ⟨2870131383572842715706449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1913420922381895143804299 2870131383572842715706449)
            ·
              refine ⟨2152598537679632036779837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2870131383572842715706449 2152598537679632036779837)
              ·
                refine ⟨807224451629862013792439, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2152598537679632036779837 807224451629862013792439)
                ·
                  refine ⟨1210836677444793020688659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 807224451629862013792439 1210836677444793020688659)
                  ·
                    refine ⟨1816255016167189531032989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1210836677444793020688659 1816255016167189531032989)
                    ·
                      refine ⟨681095631062696074137371, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1816255016167189531032989 681095631062696074137371)
                      ·
                        rfl

theorem cell23_1326429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 1, 1, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 1, 1, 2, 3, 1, 1, 3].length) (baseStart_1326429 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1326429 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1326429 prefixEnd_1326429 := by exact prefixLift 1326429
  have htrace : WordTrace (prefixWord ++ tailWord_1326429) baseStart_1326429 baseEnd_1326429 := by
    simpa [prefixWord, tailWord_1326429, baseEnd_1326429] using wordTrace_append hprefix tailTrace_1326429
  have hstable : (prefixWord ++ tailWord_1326429).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1326429).length < 2 ^ (prefixWord ++ tailWord_1326429).sum := by decide
  have hdescent : baseEnd_1326429 < baseStart_1326429 := by decide
  rcases family_descends (prefixWord ++ tailWord_1326429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1326435 : List Nat := [1, 1, 1, 5, 2, 3, 2, 3, 1, 2, 2]
def baseStart_1326435 : Nat := 118140960795 + 1326435 * 2 ^ 59
def prefixEnd_1326435 : Nat := 4983230072969 + 3 ^ 40 * 1326435 * 2
def baseEnd_1326435 : Nat := 681098711946623050662343

theorem tailTrace_1326435 : CollatzResearch.WordTrace tailWord_1326435 prefixEnd_1326435 681098711946623050662343 := by
  unfold tailWord_1326435
  simp only [CollatzResearch.WordTrace]
  refine ⟨48379058949560006907572759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32252705966373337938381839 48379058949560006907572759)
  ·
    refine ⟨72568588424340010361359139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48379058949560006907572759 72568588424340010361359139)
    ·
      refine ⟨108852882636510015542038709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72568588424340010361359139 108852882636510015542038709)
      ·
        refine ⟨10204957747172813957066129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 108852882636510015542038709 10204957747172813957066129)
        ·
          refine ⟨7653718310379610467799597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10204957747172813957066129 7653718310379610467799597)
          ·
            refine ⟨2870144366392353925424849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7653718310379610467799597 2870144366392353925424849)
            ·
              refine ⟨2152608274794265444068637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2870144366392353925424849 2152608274794265444068637)
              ·
                refine ⟨807228103047849541525739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2152608274794265444068637 807228103047849541525739)
                ·
                  refine ⟨1210842154571774312288609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 807228103047849541525739 1210842154571774312288609)
                  ·
                    refine ⟨908131615928830734216457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1210842154571774312288609 908131615928830734216457)
                    ·
                      refine ⟨681098711946623050662343, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 908131615928830734216457 681098711946623050662343)
                      ·
                        rfl

theorem cell23_1326435_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 3, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 3, 2, 3, 1, 2, 2].length) (baseStart_1326435 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1326435 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1326435 prefixEnd_1326435 := by exact prefixLift 1326435
  have htrace : WordTrace (prefixWord ++ tailWord_1326435) baseStart_1326435 baseEnd_1326435 := by
    simpa [prefixWord, tailWord_1326435, baseEnd_1326435] using wordTrace_append hprefix tailTrace_1326435
  have hstable : (prefixWord ++ tailWord_1326435).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1326435).length < 2 ^ (prefixWord ++ tailWord_1326435).sum := by decide
  have hdescent : baseEnd_1326435 < baseStart_1326435 := by decide
  rcases family_descends (prefixWord ++ tailWord_1326435) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1326457 : List Nat := [1, 2, 1, 3, 2, 1, 2, 1, 1, 5, 4]
def baseStart_1326457 : Nat := 118140960795 + 1326457 * 2 ^ 59
def prefixEnd_1326457 : Nat := 4983230072969 + 3 ^ 40 * 1326457 * 2
def baseEnd_1326457 : Nat := 681110008521021964587241

theorem tailTrace_1326457 : CollatzResearch.WordTrace tailWord_1326457 prefixEnd_1326457 681110008521021964587241 := by
  unfold tailWord_1326457
  simp only [CollatzResearch.WordTrace]
  refine ⟨48379861355480304664873625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32253240903653536443249083 48379861355480304664873625)
  ·
    refine ⟨36284896016610228498655219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48379861355480304664873625 36284896016610228498655219)
    ·
      refine ⟨54427344024915342747982829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36284896016610228498655219 54427344024915342747982829)
      ·
        refine ⟨20410254009343253530493561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 54427344024915342747982829 20410254009343253530493561)
        ·
          refine ⟨15307690507007440147870171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20410254009343253530493561 15307690507007440147870171)
          ·
            refine ⟨22961535760511160221805257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15307690507007440147870171 22961535760511160221805257)
            ·
              refine ⟨17221151820383370166353943, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22961535760511160221805257 17221151820383370166353943)
              ·
                refine ⟨25831727730575055249530915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17221151820383370166353943 25831727730575055249530915)
                ·
                  refine ⟨38747591595862582874296373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25831727730575055249530915 38747591595862582874296373)
                  ·
                    refine ⟨3632586712112117144465285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 38747591595862582874296373 3632586712112117144465285)
                    ·
                      refine ⟨681110008521021964587241, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3632586712112117144465285 681110008521021964587241)
                      ·
                        rfl

theorem cell23_1326457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 2, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 2, 1, 1, 5, 4].length) (baseStart_1326457 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1326457 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1326457 prefixEnd_1326457 := by exact prefixLift 1326457
  have htrace : WordTrace (prefixWord ++ tailWord_1326457) baseStart_1326457 baseEnd_1326457 := by
    simpa [prefixWord, tailWord_1326457, baseEnd_1326457] using wordTrace_append hprefix tailTrace_1326457
  have hstable : (prefixWord ++ tailWord_1326457).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1326457).length < 2 ^ (prefixWord ++ tailWord_1326457).sum := by decide
  have hdescent : baseEnd_1326457 < baseStart_1326457 := by decide
  rcases family_descends (prefixWord ++ tailWord_1326457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1326462 : List Nat := [4, 2, 3, 2, 1, 1, 3, 1, 2, 4]
def baseStart_1326462 : Nat := 118140960795 + 1326462 * 2 ^ 59
def prefixEnd_1326462 : Nat := 4983230072969 + 3 ^ 40 * 1326462 * 2
def baseEnd_1326462 : Nat := 227037525308098148341573

theorem tailTrace_1326462 : CollatzResearch.WordTrace tailWord_1326462 prefixEnd_1326462 227037525308098148341573 := by
  unfold tailWord_1326462
  simp only [CollatzResearch.WordTrace]
  refine ⟨6047505465057773814850705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 32253362480308127012537093 6047505465057773814850705)
  ·
    refine ⟨4535629098793330361138029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6047505465057773814850705 4535629098793330361138029)
    ·
      refine ⟨1700860912047498885426761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4535629098793330361138029 1700860912047498885426761)
      ·
        refine ⟨1275645684035624164070071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1700860912047498885426761 1275645684035624164070071)
        ·
          refine ⟨1913468526053436246105107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1275645684035624164070071 1913468526053436246105107)
          ·
            refine ⟨2870202789080154369157661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1913468526053436246105107 2870202789080154369157661)
            ·
              refine ⟨1076326045905057888434123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2870202789080154369157661 1076326045905057888434123)
              ·
                refine ⟨1614489068857586832651185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1076326045905057888434123 1614489068857586832651185)
                ·
                  refine ⟨1210866801643190124488389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1614489068857586832651185 1210866801643190124488389)
                  ·
                    refine ⟨227037525308098148341573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1210866801643190124488389 227037525308098148341573)
                    ·
                      rfl

theorem cell23_1326462_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 1, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 1, 1, 3, 1, 2, 4].length) (baseStart_1326462 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1326462 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1326462 prefixEnd_1326462 := by exact prefixLift 1326462
  have htrace : WordTrace (prefixWord ++ tailWord_1326462) baseStart_1326462 baseEnd_1326462 := by
    simpa [prefixWord, tailWord_1326462, baseEnd_1326462] using wordTrace_append hprefix tailTrace_1326462
  have hstable : (prefixWord ++ tailWord_1326462).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1326462).length < 2 ^ (prefixWord ++ tailWord_1326462).sum := by decide
  have hdescent : baseEnd_1326462 < baseStart_1326462 := by decide
  rcases family_descends (prefixWord ++ tailWord_1326462) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1326527 : List Nat := [1, 1, 2, 2, 2, 1, 1, 3, 3, 7]
def baseStart_1326527 : Nat := 118140960795 + 1326527 * 2 ^ 59
def prefixEnd_1326527 : Nat := 4983230072969 + 3 ^ 40 * 1326527 * 2
def baseEnd_1326527 : Nat := 227048650722278896903973

theorem tailTrace_1326527 : CollatzResearch.WordTrace tailWord_1326527 prefixEnd_1326527 227048650722278896903973 := by
  unfold tailWord_1326527
  simp only [CollatzResearch.WordTrace]
  refine ⟨48382414465226706619921835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32254942976817804413281223 48382414465226706619921835)
  ·
    refine ⟨72573621697840059929882753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48382414465226706619921835 72573621697840059929882753)
    ·
      refine ⟨54430216273380044947412065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 72573621697840059929882753 54430216273380044947412065)
      ·
        refine ⟨40822662205035033710559049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54430216273380044947412065 40822662205035033710559049)
        ·
          refine ⟨30616996653776275282919287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40822662205035033710559049 30616996653776275282919287)
          ·
            refine ⟨45925494980664412924378931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30616996653776275282919287 45925494980664412924378931)
            ·
              refine ⟨68888242470996619386568397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45925494980664412924378931 68888242470996619386568397)
              ·
                refine ⟨25833090926623732269963149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 68888242470996619386568397 25833090926623732269963149)
                ·
                  refine ⟨9687409097483899601236181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25833090926623732269963149 9687409097483899601236181)
                  ·
                    refine ⟨227048650722278896903973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 9687409097483899601236181 227048650722278896903973)
                    ·
                      rfl

theorem cell23_1326527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 3, 3, 7].length) (baseStart_1326527 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1326527 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1326527 prefixEnd_1326527 := by exact prefixLift 1326527
  have htrace : WordTrace (prefixWord ++ tailWord_1326527) baseStart_1326527 baseEnd_1326527 := by
    simpa [prefixWord, tailWord_1326527, baseEnd_1326527] using wordTrace_append hprefix tailTrace_1326527
  have hstable : (prefixWord ++ tailWord_1326527).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1326527).length < 2 ^ (prefixWord ++ tailWord_1326527).sum := by decide
  have hdescent : baseEnd_1326527 < baseStart_1326527 := by decide
  rcases family_descends (prefixWord ++ tailWord_1326527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1326537 : List Nat := [1, 2, 1, 1, 2, 1, 3, 1, 3, 1, 7]
def baseStart_1326537 : Nat := 118140960795 + 1326537 * 2 ^ 59
def prefixEnd_1326537 : Nat := 4983230072969 + 3 ^ 40 * 1326537 * 2
def baseEnd_1326537 : Nat := 681151086973381651586873

theorem tailTrace_1326537 : CollatzResearch.WordTrace tailWord_1326537 prefixEnd_1326537 681151086973381651586873 := by
  unfold tailWord_1326537
  simp only [CollatzResearch.WordTrace]
  refine ⟨48382779195190478327785865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32255186130126985551857243 48382779195190478327785865)
  ·
    refine ⟨36287084396392858745839399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48382779195190478327785865 36287084396392858745839399)
    ·
      refine ⟨54430626594589288118759099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36287084396392858745839399 54430626594589288118759099)
      ·
        refine ⟨81645939891883932178138649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54430626594589288118759099 81645939891883932178138649)
        ·
          refine ⟨61234454918912949133603987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 81645939891883932178138649 61234454918912949133603987)
          ·
            refine ⟨91851682378369423700405981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61234454918912949133603987 91851682378369423700405981)
            ·
              refine ⟨34444380891888533887652243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 91851682378369423700405981 34444380891888533887652243)
              ·
                refine ⟨51666571337832800831478365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34444380891888533887652243 51666571337832800831478365)
                ·
                  refine ⟨19374964251687300311804387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 51666571337832800831478365 19374964251687300311804387)
                  ·
                    refine ⟨29062446377530950467706581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19374964251687300311804387 29062446377530950467706581)
                    ·
                      refine ⟨681151086973381651586873, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 29062446377530950467706581 681151086973381651586873)
                      ·
                        rfl

theorem cell23_1326537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 3, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 3, 1, 3, 1, 7].length) (baseStart_1326537 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1326537 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1326537 prefixEnd_1326537 := by exact prefixLift 1326537
  have htrace : WordTrace (prefixWord ++ tailWord_1326537) baseStart_1326537 baseEnd_1326537 := by
    simpa [prefixWord, tailWord_1326537, baseEnd_1326537] using wordTrace_append hprefix tailTrace_1326537
  have hstable : (prefixWord ++ tailWord_1326537).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1326537).length < 2 ^ (prefixWord ++ tailWord_1326537).sum := by decide
  have hdescent : baseEnd_1326537 < baseStart_1326537 := by decide
  rcases family_descends (prefixWord ++ tailWord_1326537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1326554 : List Nat := [3, 1, 1, 2, 3, 2, 1, 2, 1, 2, 5]
def baseStart_1326554 : Nat := 118140960795 + 1326554 * 2 ^ 59
def prefixEnd_1326554 : Nat := 4983230072969 + 3 ^ 40 * 1326554 * 2
def baseEnd_1326554 : Nat := 681159816144508085074295

theorem tailTrace_1326554 : CollatzResearch.WordTrace tailWord_1326554 prefixEnd_1326554 681159816144508085074295 := by
  unfold tailWord_1326554
  simp only [CollatzResearch.WordTrace]
  refine ⟨12095849809032222557788679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32255599490752593487436477 12095849809032222557788679)
  ·
    refine ⟨18143774713548333836683019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12095849809032222557788679 18143774713548333836683019)
    ·
      refine ⟨27215662070322500755024529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18143774713548333836683019 27215662070322500755024529)
      ·
        refine ⟨20411746552741875566268397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27215662070322500755024529 20411746552741875566268397)
        ·
          refine ⟨7654404957278203337350649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20411746552741875566268397 7654404957278203337350649)
          ·
            refine ⟨5740803717958652503012987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7654404957278203337350649 5740803717958652503012987)
            ·
              refine ⟨8611205576937978754519481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5740803717958652503012987 8611205576937978754519481)
              ·
                refine ⟨6458404182703484065889611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8611205576937978754519481 6458404182703484065889611)
                ·
                  refine ⟨9687606274055226098834417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6458404182703484065889611 9687606274055226098834417)
                  ·
                    refine ⟨7265704705541419574125813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9687606274055226098834417 7265704705541419574125813)
                    ·
                      refine ⟨681159816144508085074295, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7265704705541419574125813 681159816144508085074295)
                      ·
                        rfl

theorem cell23_1326554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 1, 2, 1, 2, 5].length) (baseStart_1326554 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1326554 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1326554 prefixEnd_1326554 := by exact prefixLift 1326554
  have htrace : WordTrace (prefixWord ++ tailWord_1326554) baseStart_1326554 baseEnd_1326554 := by
    simpa [prefixWord, tailWord_1326554, baseEnd_1326554] using wordTrace_append hprefix tailTrace_1326554
  have hstable : (prefixWord ++ tailWord_1326554).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1326554).length < 2 ^ (prefixWord ++ tailWord_1326554).sum := by decide
  have hdescent : baseEnd_1326554 < baseStart_1326554 := by decide
  rcases family_descends (prefixWord ++ tailWord_1326554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1326565 : List Nat := [1, 3, 1, 5, 1, 3, 2, 2, 5]
def baseStart_1326565 : Nat := 118140960795 + 1326565 * 2 ^ 59
def prefixEnd_1326565 : Nat := 4983230072969 + 3 ^ 40 * 1326565 * 2
def baseEnd_1326565 : Nat := 75685051603523060226305

theorem tailTrace_1326565 : CollatzResearch.WordTrace tailWord_1326565 prefixEnd_1326565 75685051603523060226305 := by
  unfold tailWord_1326565
  simp only [CollatzResearch.WordTrace]
  refine ⟨48383800439089039109805149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32255866959392692739870099 48383800439089039109805149)
  ·
    refine ⟨18143925164658389666176931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 48383800439089039109805149 18143925164658389666176931)
    ·
      refine ⟨27215887746987584499265397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18143925164658389666176931 27215887746987584499265397)
      ·
        refine ⟨2551489476280086046806131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 27215887746987584499265397 2551489476280086046806131)
        ·
          refine ⟨3827234214420129070209197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2551489476280086046806131 3827234214420129070209197)
          ·
            refine ⟨1435212830407548401328449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3827234214420129070209197 1435212830407548401328449)
            ·
              refine ⟨1076409622805661300996337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1435212830407548401328449 1076409622805661300996337)
              ·
                refine ⟨807307217104245975747253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1076409622805661300996337 807307217104245975747253)
                ·
                  refine ⟨75685051603523060226305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 807307217104245975747253 75685051603523060226305)
                  ·
                    rfl

theorem cell23_1326565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 3, 2, 2, 5].length) (baseStart_1326565 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1326565 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1326565 prefixEnd_1326565 := by exact prefixLift 1326565
  have htrace : WordTrace (prefixWord ++ tailWord_1326565) baseStart_1326565 baseEnd_1326565 := by
    simpa [prefixWord, tailWord_1326565, baseEnd_1326565] using wordTrace_append hprefix tailTrace_1326565
  have hstable : (prefixWord ++ tailWord_1326565).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1326565).length < 2 ^ (prefixWord ++ tailWord_1326565).sum := by decide
  have hdescent : baseEnd_1326565 < baseStart_1326565 := by decide
  rcases family_descends (prefixWord ++ tailWord_1326565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1326648 : List Nat := [2, 1, 2, 1, 4, 2, 2, 2, 3, 1, 3]
def baseStart_1326648 : Nat := 118140960795 + 1326648 * 2 ^ 59
def prefixEnd_1326648 : Nat := 4983230072969 + 3 ^ 40 * 1326648 * 2
def baseEnd_1326648 : Nat := 681208083326030717298863

theorem tailTrace_1326648 : CollatzResearch.WordTrace tailWord_1326648 prefixEnd_1326648 681208083326030717298863 := by
  unfold tailWord_1326648
  simp only [CollatzResearch.WordTrace]
  refine ⟨24193413848894172142538299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32257885131858896190051065 24193413848894172142538299)
  ·
    refine ⟨36290120773341258213807449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24193413848894172142538299 36290120773341258213807449)
    ·
      refine ⟨27217590580005943660355587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36290120773341258213807449 27217590580005943660355587)
      ·
        refine ⟨40826385870008915490533381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27217590580005943660355587 40826385870008915490533381)
        ·
          refine ⟨7654947350626671654475009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 40826385870008915490533381 7654947350626671654475009)
          ·
            refine ⟨5741210512970003740856257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7654947350626671654475009 5741210512970003740856257)
            ·
              refine ⟨4305907884727502805642193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5741210512970003740856257 4305907884727502805642193)
              ·
                refine ⟨3229430913545627104231645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4305907884727502805642193 3229430913545627104231645)
                ·
                  refine ⟨1211036592579610164086867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3229430913545627104231645 1211036592579610164086867)
                  ·
                    refine ⟨1816554888869415246130301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1211036592579610164086867 1816554888869415246130301)
                    ·
                      refine ⟨681208083326030717298863, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1816554888869415246130301 681208083326030717298863)
                      ·
                        rfl

theorem cell23_1326648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 2, 2, 3, 1, 3].length) (baseStart_1326648 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1326648 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1326648 prefixEnd_1326648 := by exact prefixLift 1326648
  have htrace : WordTrace (prefixWord ++ tailWord_1326648) baseStart_1326648 baseEnd_1326648 := by
    simpa [prefixWord, tailWord_1326648, baseEnd_1326648] using wordTrace_append hprefix tailTrace_1326648
  have hstable : (prefixWord ++ tailWord_1326648).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1326648).length < 2 ^ (prefixWord ++ tailWord_1326648).sum := by decide
  have hdescent : baseEnd_1326648 < baseStart_1326648 := by decide
  rcases family_descends (prefixWord ++ tailWord_1326648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1326691 : List Nat := [1, 1, 1, 5, 1, 3, 2, 2, 1, 1, 5]
def baseStart_1326691 : Nat := 118140960795 + 1326691 * 2 ^ 59
def prefixEnd_1326691 : Nat := 4983230072969 + 3 ^ 40 * 1326691 * 2
def baseEnd_1326691 : Nat := 681230162994174049061165

theorem tailTrace_1326691 : CollatzResearch.WordTrace tailWord_1326691 prefixEnd_1326691 681230162994174049061165 := by
  unfold tailWord_1326691
  simp only [CollatzResearch.WordTrace]
  refine ⟨48388396036632562628891927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32258930691088375085927951 48388396036632562628891927)
  ·
    refine ⟨72582594054948843943337891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48388396036632562628891927 72582594054948843943337891)
    ·
      refine ⟨108873891082423265915006837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72582594054948843943337891 108873891082423265915006837)
      ·
        refine ⟨10206927288977181179531891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 108873891082423265915006837 10206927288977181179531891)
        ·
          refine ⟨15310390933465771769297837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10206927288977181179531891 15310390933465771769297837)
          ·
            refine ⟨5741396600049664413486689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15310390933465771769297837 5741396600049664413486689)
            ·
              refine ⟨4306047450037248310115017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5741396600049664413486689 4306047450037248310115017)
              ·
                refine ⟨3229535587527936232586263, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4306047450037248310115017 3229535587527936232586263)
                ·
                  refine ⟨4844303381291904348879395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3229535587527936232586263 4844303381291904348879395)
                  ·
                    refine ⟨7266455071937856523319093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4844303381291904348879395 7266455071937856523319093)
                    ·
                      refine ⟨681230162994174049061165, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7266455071937856523319093 681230162994174049061165)
                      ·
                        rfl

theorem cell23_1326691_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 2, 2, 1, 1, 5].length) (baseStart_1326691 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1326691 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1326691 prefixEnd_1326691 := by exact prefixLift 1326691
  have htrace : WordTrace (prefixWord ++ tailWord_1326691) baseStart_1326691 baseEnd_1326691 := by
    simpa [prefixWord, tailWord_1326691, baseEnd_1326691] using wordTrace_append hprefix tailTrace_1326691
  have hstable : (prefixWord ++ tailWord_1326691).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1326691).length < 2 ^ (prefixWord ++ tailWord_1326691).sum := by decide
  have hdescent : baseEnd_1326691 < baseStart_1326691 := by decide
  rcases family_descends (prefixWord ++ tailWord_1326691) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1326702 : List Nat := [4, 1, 2, 2, 4, 1, 1, 2, 1, 5]
def baseStart_1326702 : Nat := 118140960795 + 1326702 * 2 ^ 59
def prefixEnd_1326702 : Nat := 4983230072969 + 3 ^ 40 * 1326702 * 2
def baseEnd_1326702 : Nat := 227078603760457835341205

theorem tailTrace_1326702 : CollatzResearch.WordTrace tailWord_1326702 prefixEnd_1326702 227078603760457835341205 := by
  unfold tailWord_1326702
  simp only [CollatzResearch.WordTrace]
  refine ⟨6048599654949088938442795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 32259198159728474338361573 6048599654949088938442795)
  ·
    refine ⟨9072899482423633407664193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6048599654949088938442795 9072899482423633407664193)
    ·
      refine ⟨6804674611817725055748145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9072899482423633407664193 6804674611817725055748145)
      ·
        refine ⟨5103505958863293791811109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6804674611817725055748145 5103505958863293791811109)
        ·
          refine ⟨956907367286867585964583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5103505958863293791811109 956907367286867585964583)
          ·
            refine ⟨1435361050930301378946875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 956907367286867585964583 1435361050930301378946875)
            ·
              refine ⟨2153041576395452068420313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1435361050930301378946875 2153041576395452068420313)
              ·
                refine ⟨1614781182296589051315235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2153041576395452068420313 1614781182296589051315235)
                ·
                  refine ⟨2422171773444883576972853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1614781182296589051315235 2422171773444883576972853)
                  ·
                    refine ⟨227078603760457835341205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2422171773444883576972853 227078603760457835341205)
                    ·
                      rfl

theorem cell23_1326702_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 4, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 4, 1, 1, 2, 1, 5].length) (baseStart_1326702 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1326702 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1326702 prefixEnd_1326702 := by exact prefixLift 1326702
  have htrace : WordTrace (prefixWord ++ tailWord_1326702) baseStart_1326702 baseEnd_1326702 := by
    simpa [prefixWord, tailWord_1326702, baseEnd_1326702] using wordTrace_append hprefix tailTrace_1326702
  have hstable : (prefixWord ++ tailWord_1326702).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1326702).length < 2 ^ (prefixWord ++ tailWord_1326702).sum := by decide
  have hdescent : baseEnd_1326702 < baseStart_1326702 := by decide
  rcases family_descends (prefixWord ++ tailWord_1326702) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1326725 : List Nat := [1, 3, 1, 1, 4, 1, 5, 1, 1, 2, 3]
def baseStart_1326725 : Nat := 118140960795 + 1326725 * 2 ^ 59
def prefixEnd_1326725 : Nat := 4983230072969 + 3 ^ 40 * 1326725 * 2
def baseEnd_1326725 : Nat := 681247621336426916036009

theorem tailTrace_1326725 : CollatzResearch.WordTrace tailWord_1326725 prefixEnd_1326725 681247621336426916036009 := by
  unfold tailWord_1326725
  simp only [CollatzResearch.WordTrace]
  refine ⟨48389636118509386435629629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32259757412339590957086419 48389636118509386435629629)
  ·
    refine ⟨18146113544441019913361111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 48389636118509386435629629 18146113544441019913361111)
    ·
      refine ⟨27219170316661529870041667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18146113544441019913361111 27219170316661529870041667)
      ·
        refine ⟨40828755474992294805062501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27219170316661529870041667 40828755474992294805062501)
        ·
          refine ⟨7655391651561055275949219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 40828755474992294805062501 7655391651561055275949219)
          ·
            refine ⟨11483087477341582913923829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7655391651561055275949219 11483087477341582913923829)
            ·
              refine ⟨1076539451000773398180359, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 11483087477341582913923829 1076539451000773398180359)
              ·
                refine ⟨1614809176501160097270539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1076539451000773398180359 1614809176501160097270539)
                ·
                  refine ⟨2422213764751740145905809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1614809176501160097270539 2422213764751740145905809)
                  ·
                    refine ⟨1816660323563805109429357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2422213764751740145905809 1816660323563805109429357)
                    ·
                      refine ⟨681247621336426916036009, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1816660323563805109429357 681247621336426916036009)
                      ·
                        rfl

theorem cell23_1326725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 5, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 5, 1, 1, 2, 3].length) (baseStart_1326725 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1326725 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1326725 prefixEnd_1326725 := by exact prefixLift 1326725
  have htrace : WordTrace (prefixWord ++ tailWord_1326725) baseStart_1326725 baseEnd_1326725 := by
    simpa [prefixWord, tailWord_1326725, baseEnd_1326725] using wordTrace_append hprefix tailTrace_1326725
  have hstable : (prefixWord ++ tailWord_1326725).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1326725).length < 2 ^ (prefixWord ++ tailWord_1326725).sum := by decide
  have hdescent : baseEnd_1326725 < baseStart_1326725 := by decide
  rcases family_descends (prefixWord ++ tailWord_1326725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1326728 : List Nat := [2, 1, 3, 5, 2, 10]
def baseStart_1326728 : Nat := 118140960795 + 1326728 * 2 ^ 59
def prefixEnd_1326728 : Nat := 4983230072969 + 3 ^ 40 * 1326728 * 2
def baseEnd_1326728 : Nat := 2803494492915186848965

theorem tailTrace_1326728 : CollatzResearch.WordTrace tailWord_1326728 prefixEnd_1326728 2803494492915186848965 := by
  unfold tailWord_1326728
  simp only [CollatzResearch.WordTrace]
  refine ⟨24194872768749258973994419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32259830358332345298659225 24194872768749258973994419)
  ·
    refine ⟨36292309153123888460991629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24194872768749258973994419 36292309153123888460991629)
    ·
      refine ⟨13609615932421458172871861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 36292309153123888460991629 13609615932421458172871861)
      ·
        refine ⟨1275901493664511703706737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 13609615932421458172871861 1275901493664511703706737)
        ·
          refine ⟨956926120248383777780053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1275901493664511703706737 956926120248383777780053)
          ·
            refine ⟨2803494492915186848965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 956926120248383777780053 2803494492915186848965)
            ·
              rfl

theorem cell23_1326728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 2, 10].length) (baseStart_1326728 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1326728 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1326728 prefixEnd_1326728 := by exact prefixLift 1326728
  have htrace : WordTrace (prefixWord ++ tailWord_1326728) baseStart_1326728 baseEnd_1326728 := by
    simpa [prefixWord, tailWord_1326728, baseEnd_1326728] using wordTrace_append hprefix tailTrace_1326728
  have hstable : (prefixWord ++ tailWord_1326728).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1326728).length < 2 ^ (prefixWord ++ tailWord_1326728).sum := by decide
  have hdescent : baseEnd_1326728 < baseStart_1326728 := by decide
  rcases family_descends (prefixWord ++ tailWord_1326728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1326765 : List Nat := [1, 5, 2, 1, 1, 1, 1, 3, 3, 3, 2]
def baseStart_1326765 : Nat := 118140960795 + 1326765 * 2 ^ 59
def prefixEnd_1326765 : Nat := 4983230072969 + 3 ^ 40 * 1326765 * 2
def baseEnd_1326765 : Nat := 681268160562606759535825

theorem tailTrace_1326765 : CollatzResearch.WordTrace tailWord_1326765 prefixEnd_1326765 681268160562606759535825 := by
  unfold tailWord_1326765
  simp only [CollatzResearch.WordTrace]
  refine ⟨48391095038364473267085749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32260730025576315511390499 48391095038364473267085749)
  ·
    refine ⟨4536665159846669368789289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 48391095038364473267085749 4536665159846669368789289)
    ·
      refine ⟨3402498869885002026591967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4536665159846669368789289 3402498869885002026591967)
      ·
        refine ⟨5103748304827503039887951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3402498869885002026591967 5103748304827503039887951)
        ·
          refine ⟨7655622457241254559831927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5103748304827503039887951 7655622457241254559831927)
          ·
            refine ⟨11483433685861881839747891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7655622457241254559831927 11483433685861881839747891)
            ·
              refine ⟨17225150528792822759621837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11483433685861881839747891 17225150528792822759621837)
              ·
                refine ⟨6459431448297308534858189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17225150528792822759621837 6459431448297308534858189)
                ·
                  refine ⟨2422286793111490700571821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6459431448297308534858189 2422286793111490700571821)
                  ·
                    refine ⟨908357547416809012714433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2422286793111490700571821 908357547416809012714433)
                    ·
                      refine ⟨681268160562606759535825, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 908357547416809012714433 681268160562606759535825)
                      ·
                        rfl

theorem cell23_1326765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 1, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 1, 3, 3, 3, 2].length) (baseStart_1326765 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1326765 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1326765 prefixEnd_1326765 := by exact prefixLift 1326765
  have htrace : WordTrace (prefixWord ++ tailWord_1326765) baseStart_1326765 baseEnd_1326765 := by
    simpa [prefixWord, tailWord_1326765, baseEnd_1326765] using wordTrace_append hprefix tailTrace_1326765
  have hstable : (prefixWord ++ tailWord_1326765).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1326765).length < 2 ^ (prefixWord ++ tailWord_1326765).sum := by decide
  have hdescent : baseEnd_1326765 < baseStart_1326765 := by decide
  rcases family_descends (prefixWord ++ tailWord_1326765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1326781 : List Nat := [1, 4, 1, 2, 1, 2, 2, 1, 1, 3, 5]
def baseStart_1326781 : Nat := 118140960795 + 1326781 * 2 ^ 59
def prefixEnd_1326781 : Nat := 4983230072969 + 3 ^ 40 * 1326781 * 2
def baseEnd_1326781 : Nat := 681276376253078696935751

theorem tailTrace_1326781 : CollatzResearch.WordTrace tailWord_1326781 prefixEnd_1326781 681276376253078696935751 := by
  unfold tailWord_1326781
  simp only [CollatzResearch.WordTrace]
  refine ⟨48391678606306507999668197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32261119070871005333112131 48391678606306507999668197)
  ·
    refine ⟨9073439738682470249937787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 48391678606306507999668197 9073439738682470249937787)
    ·
      refine ⟨13610159608023705374906681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9073439738682470249937787 13610159608023705374906681)
      ·
        refine ⟨10207619706017779031180011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13610159608023705374906681 10207619706017779031180011)
        ·
          refine ⟨15311429559026668546770017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10207619706017779031180011 15311429559026668546770017)
          ·
            refine ⟨11483572169270001410077513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15311429559026668546770017 11483572169270001410077513)
            ·
              refine ⟨8612679126952501057558135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11483572169270001410077513 8612679126952501057558135)
              ·
                refine ⟨12919018690428751586337203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8612679126952501057558135 12919018690428751586337203)
                ·
                  refine ⟨19378528035643127379505805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12919018690428751586337203 19378528035643127379505805)
                  ·
                    refine ⟨7266948013366172767314677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19378528035643127379505805 7266948013366172767314677)
                    ·
                      refine ⟨681276376253078696935751, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7266948013366172767314677 681276376253078696935751)
                      ·
                        rfl

theorem cell23_1326781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 2, 1, 1, 3, 5].length) (baseStart_1326781 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1326781 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1326781 prefixEnd_1326781 := by exact prefixLift 1326781
  have htrace : WordTrace (prefixWord ++ tailWord_1326781) baseStart_1326781 baseEnd_1326781 := by
    simpa [prefixWord, tailWord_1326781, baseEnd_1326781] using wordTrace_append hprefix tailTrace_1326781
  have hstable : (prefixWord ++ tailWord_1326781).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1326781).length < 2 ^ (prefixWord ++ tailWord_1326781).sum := by decide
  have hdescent : baseEnd_1326781 < baseStart_1326781 := by decide
  rcases family_descends (prefixWord ++ tailWord_1326781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1326782 : List Nat := [4, 2, 1, 1, 2, 3, 1, 3, 1, 3, 2]
def baseStart_1326782 : Nat := 118140960795 + 1326782 * 2 ^ 59
def prefixEnd_1326782 : Nat := 4983230072969 + 3 ^ 40 * 1326782 * 2
def baseEnd_1326782 : Nat := 681276889733733193023247

theorem tailTrace_1326782 : CollatzResearch.WordTrace tailWord_1326782 prefixEnd_1326782 681276889733733193023247 := by
  unfold tailWord_1326782
  simp only [CollatzResearch.WordTrace]
  refine ⟨6048964384912860646306825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 32261143386201923446969733 6048964384912860646306825)
  ·
    refine ⟨4536723288684645484730119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6048964384912860646306825 4536723288684645484730119)
    ·
      refine ⟨6805084933026968227095179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4536723288684645484730119 6805084933026968227095179)
      ·
        refine ⟨10207627399540452340642769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6805084933026968227095179 10207627399540452340642769)
        ·
          refine ⟨7655720549655339255482077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10207627399540452340642769 7655720549655339255482077)
          ·
            refine ⟨2870895206120752220805779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7655720549655339255482077 2870895206120752220805779)
            ·
              refine ⟨4306342809181128331208669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2870895206120752220805779 4306342809181128331208669)
              ·
                refine ⟨1614878553442923124203251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4306342809181128331208669 1614878553442923124203251)
                ·
                  refine ⟨2422317830164384686304877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1614878553442923124203251 2422317830164384686304877)
                  ·
                    refine ⟨908369186311644257364329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2422317830164384686304877 908369186311644257364329)
                    ·
                      refine ⟨681276889733733193023247, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 908369186311644257364329 681276889733733193023247)
                      ·
                        rfl

theorem cell23_1326782_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 3, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 3, 1, 3, 1, 3, 2].length) (baseStart_1326782 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1326782 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1326782 prefixEnd_1326782 := by exact prefixLift 1326782
  have htrace : WordTrace (prefixWord ++ tailWord_1326782) baseStart_1326782 baseEnd_1326782 := by
    simpa [prefixWord, tailWord_1326782, baseEnd_1326782] using wordTrace_append hprefix tailTrace_1326782
  have hstable : (prefixWord ++ tailWord_1326782).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1326782).length < 2 ^ (prefixWord ++ tailWord_1326782).sum := by decide
  have hdescent : baseEnd_1326782 < baseStart_1326782 := by decide
  rcases family_descends (prefixWord ++ tailWord_1326782) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1326791 : List Nat := [1, 1, 4, 1, 1, 1, 3, 1, 4, 2, 4]
def baseStart_1326791 : Nat := 118140960795 + 1326791 * 2 ^ 59
def prefixEnd_1326791 : Nat := 4983230072969 + 3 ^ 40 * 1326791 * 2
def baseEnd_1326791 : Nat := 681281511059623657810705

theorem tailTrace_1326791 : CollatzResearch.WordTrace tailWord_1326791 prefixEnd_1326791 681281511059623657810705 := by
  unfold tailWord_1326791
  simp only [CollatzResearch.WordTrace]
  refine ⟨48392043336270279707532227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32261362224180186471688151 48392043336270279707532227)
  ·
    refine ⟨72588065004405419561298341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48392043336270279707532227 72588065004405419561298341)
    ·
      refine ⟨13610262188326016167743439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 72588065004405419561298341 13610262188326016167743439)
      ·
        refine ⟨20415393282489024251615159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13610262188326016167743439 20415393282489024251615159)
        ·
          refine ⟨30623089923733536377422739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20415393282489024251615159 30623089923733536377422739)
          ·
            refine ⟨45934634885600304566134109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30623089923733536377422739 45934634885600304566134109)
            ·
              refine ⟨17225488082100114212300291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 45934634885600304566134109 17225488082100114212300291)
              ·
                refine ⟨25838232123150171318450437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17225488082100114212300291 25838232123150171318450437)
                ·
                  refine ⟨4844668523090657122209457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 25838232123150171318450437 4844668523090657122209457)
                  ·
                    refine ⟨3633501392317992841657093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4844668523090657122209457 3633501392317992841657093)
                    ·
                      refine ⟨681281511059623657810705, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3633501392317992841657093 681281511059623657810705)
                      ·
                        rfl

theorem cell23_1326791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 3, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 3, 1, 4, 2, 4].length) (baseStart_1326791 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1326791 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1326791 prefixEnd_1326791 := by exact prefixLift 1326791
  have htrace : WordTrace (prefixWord ++ tailWord_1326791) baseStart_1326791 baseEnd_1326791 := by
    simpa [prefixWord, tailWord_1326791, baseEnd_1326791] using wordTrace_append hprefix tailTrace_1326791
  have hstable : (prefixWord ++ tailWord_1326791).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1326791).length < 2 ^ (prefixWord ++ tailWord_1326791).sum := by decide
  have hdescent : baseEnd_1326791 < baseStart_1326791 := by decide
  rcases family_descends (prefixWord ++ tailWord_1326791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1326801 : List Nat := [1, 2, 2, 1, 2, 4, 1, 3, 7]
def baseStart_1326801 : Nat := 118140960795 + 1326801 * 2 ^ 59
def prefixEnd_1326801 : Nat := 4983230072969 + 3 ^ 40 * 1326801 * 2
def baseEnd_1326801 : Nat := 75698516207352068742851

theorem tailTrace_1326801 : CollatzResearch.WordTrace tailWord_1326801 prefixEnd_1326801 75698516207352068742851 := by
  unfold tailWord_1326801
  simp only [CollatzResearch.WordTrace]
  refine ⟨48392408066234051415396257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32261605377489367610264171 48392408066234051415396257)
  ·
    refine ⟨36294306049675538561547193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48392408066234051415396257 36294306049675538561547193)
    ·
      refine ⟨27220729537256653921160395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36294306049675538561547193 27220729537256653921160395)
      ·
        refine ⟨40831094305884980881740593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27220729537256653921160395 40831094305884980881740593)
        ·
          refine ⟨30623320729413735661305445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40831094305884980881740593 30623320729413735661305445)
          ·
            refine ⟨5741872636765075436494771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 30623320729413735661305445 5741872636765075436494771)
            ·
              refine ⟨8612808955147613154742157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5741872636765075436494771 8612808955147613154742157)
              ·
                refine ⟨3229803358180354933028309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8612808955147613154742157 3229803358180354933028309)
                ·
                  refine ⟨75698516207352068742851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3229803358180354933028309 75698516207352068742851)
                  ·
                    rfl

theorem cell23_1326801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 1, 3, 7].length) (baseStart_1326801 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1326801 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1326801 prefixEnd_1326801 := by exact prefixLift 1326801
  have htrace : WordTrace (prefixWord ++ tailWord_1326801) baseStart_1326801 baseEnd_1326801 := by
    simpa [prefixWord, tailWord_1326801, baseEnd_1326801] using wordTrace_append hprefix tailTrace_1326801
  have hstable : (prefixWord ++ tailWord_1326801).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1326801).length < 2 ^ (prefixWord ++ tailWord_1326801).sum := by decide
  have hdescent : baseEnd_1326801 < baseStart_1326801 := by decide
  rcases family_descends (prefixWord ++ tailWord_1326801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1326806 : List Nat := [5, 2, 1, 3, 2, 1, 1, 1, 1, 3, 3]
def baseStart_1326806 : Nat := 118140960795 + 1326806 * 2 ^ 59
def prefixEnd_1326806 : Nat := 4983230072969 + 3 ^ 40 * 1326806 * 2
def baseEnd_1326806 : Nat := 681289213269441099123137

theorem tailTrace_1326806 : CollatzResearch.WordTrace tailWord_1326806 prefixEnd_1326806 681289213269441099123137 := by
  unfold tailWord_1326806
  simp only [CollatzResearch.WordTrace]
  refine ⟨3024536901950996079333017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 32261726954143958179552181 3024536901950996079333017)
  ·
    refine ⟨2268402676463247059499763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3024536901950996079333017 2268402676463247059499763)
    ·
      refine ⟨3402604014694870589249645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2268402676463247059499763 3402604014694870589249645)
      ·
        refine ⟨1275976505510576470968617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3402604014694870589249645 1275976505510576470968617)
        ·
          refine ⟨956982379132932353226463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1275976505510576470968617 956982379132932353226463)
          ·
            refine ⟨1435473568699398529839695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 956982379132932353226463 1435473568699398529839695)
            ·
              refine ⟨2153210353049097794759543, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1435473568699398529839695 2153210353049097794759543)
              ·
                refine ⟨3229815529573646692139315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2153210353049097794759543 3229815529573646692139315)
                ·
                  refine ⟨4844723294360470038208973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3229815529573646692139315 4844723294360470038208973)
                  ·
                    refine ⟨1816771235385176264328365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4844723294360470038208973 1816771235385176264328365)
                    ·
                      refine ⟨681289213269441099123137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1816771235385176264328365 681289213269441099123137)
                      ·
                        rfl

theorem cell23_1326806_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 2, 1, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 2, 1, 1, 1, 1, 3, 3].length) (baseStart_1326806 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1326806 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1326806 prefixEnd_1326806 := by exact prefixLift 1326806
  have htrace : WordTrace (prefixWord ++ tailWord_1326806) baseStart_1326806 baseEnd_1326806 := by
    simpa [prefixWord, tailWord_1326806, baseEnd_1326806] using wordTrace_append hprefix tailTrace_1326806
  have hstable : (prefixWord ++ tailWord_1326806).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1326806).length < 2 ^ (prefixWord ++ tailWord_1326806).sum := by decide
  have hdescent : baseEnd_1326806 < baseStart_1326806 := by decide
  rcases family_descends (prefixWord ++ tailWord_1326806) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1326831 : List Nat := [1, 1, 2, 1, 5, 1, 1, 3, 1, 7]
def baseStart_1326831 : Nat := 118140960795 + 1326831 * 2 ^ 59
def prefixEnd_1326831 : Nat := 4983230072969 + 3 ^ 40 * 1326831 * 2
def baseEnd_1326831 : Nat := 227100683428601167103507

theorem tailTrace_1326831 : CollatzResearch.WordTrace tailWord_1326831 prefixEnd_1326831 227100683428601167103507 := by
  unfold tailWord_1326831
  simp only [CollatzResearch.WordTrace]
  refine ⟨48393502256125366538988347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32262334837416911025992231 48393502256125366538988347)
  ·
    refine ⟨72590253384188049808482521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48393502256125366538988347 72590253384188049808482521)
    ·
      refine ⟨54442690038141037356361891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 72590253384188049808482521 54442690038141037356361891)
      ·
        refine ⟨81664035057211556034542837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54442690038141037356361891 81664035057211556034542837)
        ·
          refine ⟨7656003286613583378238391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 81664035057211556034542837 7656003286613583378238391)
          ·
            refine ⟨11484004929920375067357587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7656003286613583378238391 11484004929920375067357587)
            ·
              refine ⟨17226007394880562601036381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11484004929920375067357587 17226007394880562601036381)
              ·
                refine ⟨6459752773080210975388643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17226007394880562601036381 6459752773080210975388643)
                ·
                  refine ⟨9689629159620316463082965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6459752773080210975388643 9689629159620316463082965)
                  ·
                    refine ⟨227100683428601167103507, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 9689629159620316463082965 227100683428601167103507)
                    ·
                      rfl

theorem cell23_1326831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 1, 3, 1, 7].length) (baseStart_1326831 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1326831 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1326831 prefixEnd_1326831 := by exact prefixLift 1326831
  have htrace : WordTrace (prefixWord ++ tailWord_1326831) baseStart_1326831 baseEnd_1326831 := by
    simpa [prefixWord, tailWord_1326831, baseEnd_1326831] using wordTrace_append hprefix tailTrace_1326831
  have hstable : (prefixWord ++ tailWord_1326831).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1326831).length < 2 ^ (prefixWord ++ tailWord_1326831).sum := by decide
  have hdescent : baseEnd_1326831 < baseStart_1326831 := by decide
  rcases family_descends (prefixWord ++ tailWord_1326831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1326852 : List Nat := [2, 3, 2, 2, 1, 3, 3, 2, 5]
def baseStart_1326852 : Nat := 118140960795 + 1326852 * 2 ^ 59
def prefixEnd_1326852 : Nat := 4983230072969 + 3 ^ 40 * 1326852 * 2
def baseEnd_1326852 : Nat := 75701425931060879905325

theorem tailTrace_1326852 : CollatzResearch.WordTrace tailWord_1326852 prefixEnd_1326852 75701425931060879905325 := by
  unfold tailWord_1326852
  simp only [CollatzResearch.WordTrace]
  refine ⟨24197134094524643562751405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32262845459366191417001873 24197134094524643562751405)
  ·
    refine ⟨9073925285446741336031777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24197134094524643562751405 9073925285446741336031777)
    ·
      refine ⟨6805443964085056002023833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9073925285446741336031777 6805443964085056002023833)
      ·
        refine ⟨5104082973063792001517875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6805443964085056002023833 5104082973063792001517875)
        ·
          refine ⟨7656124459595688002276813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5104082973063792001517875 7656124459595688002276813)
          ·
            refine ⟨2871046672348383000853805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7656124459595688002276813 2871046672348383000853805)
            ·
              refine ⟨1076642502130643625320177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2871046672348383000853805 1076642502130643625320177)
              ·
                refine ⟨807481876597982718990133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1076642502130643625320177 807481876597982718990133)
                ·
                  refine ⟨75701425931060879905325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 807481876597982718990133 75701425931060879905325)
                  ·
                    rfl

theorem cell23_1326852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 3, 3, 2, 5].length) (baseStart_1326852 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1326852 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1326852 prefixEnd_1326852 := by exact prefixLift 1326852
  have htrace : WordTrace (prefixWord ++ tailWord_1326852) baseStart_1326852 baseEnd_1326852 := by
    simpa [prefixWord, tailWord_1326852, baseEnd_1326852] using wordTrace_append hprefix tailTrace_1326852
  have hstable : (prefixWord ++ tailWord_1326852).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1326852).length < 2 ^ (prefixWord ++ tailWord_1326852).sum := by decide
  have hdescent : baseEnd_1326852 < baseStart_1326852 := by decide
  rcases family_descends (prefixWord ++ tailWord_1326852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1326858 : List Nat := [3, 1, 2, 2, 1, 4, 1, 1, 1, 2, 5]
def baseStart_1326858 : Nat := 118140960795 + 1326858 * 2 ^ 59
def prefixEnd_1326858 : Nat := 4983230072969 + 3 ^ 40 * 1326858 * 2
def baseEnd_1326858 : Nat := 681315914263474895672897

theorem tailTrace_1326858 : CollatzResearch.WordTrace tailWord_1326858 prefixEnd_1326858 681315914263474895672897 := by
  unfold tailWord_1326858
  simp only [CollatzResearch.WordTrace]
  refine ⟨12098621756756887537555307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32262991351351700100147485 12098621756756887537555307)
  ·
    refine ⟨18147932635135331306332961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12098621756756887537555307 18147932635135331306332961)
    ·
      refine ⟨13610949476351498479749721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18147932635135331306332961 13610949476351498479749721)
      ·
        refine ⟨10208212107263623859812291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13610949476351498479749721 10208212107263623859812291)
        ·
          refine ⟨15312318160895435789718437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10208212107263623859812291 15312318160895435789718437)
          ·
            refine ⟨2871059655167894210572207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 15312318160895435789718437 2871059655167894210572207)
            ·
              refine ⟨4306589482751841315858311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2871059655167894210572207 4306589482751841315858311)
              ·
                refine ⟨6459884224127761973787467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4306589482751841315858311 6459884224127761973787467)
                ·
                  refine ⟨9689826336191642960681201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6459884224127761973787467 9689826336191642960681201)
                  ·
                    refine ⟨7267369752143732220510901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9689826336191642960681201 7267369752143732220510901)
                    ·
                      refine ⟨681315914263474895672897, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7267369752143732220510901 681315914263474895672897)
                      ·
                        rfl

theorem cell23_1326858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 4, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 4, 1, 1, 1, 2, 5].length) (baseStart_1326858 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1326858 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1326858 prefixEnd_1326858 := by exact prefixLift 1326858
  have htrace : WordTrace (prefixWord ++ tailWord_1326858) baseStart_1326858 baseEnd_1326858 := by
    simpa [prefixWord, tailWord_1326858, baseEnd_1326858] using wordTrace_append hprefix tailTrace_1326858
  have hstable : (prefixWord ++ tailWord_1326858).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1326858).length < 2 ^ (prefixWord ++ tailWord_1326858).sum := by decide
  have hdescent : baseEnd_1326858 < baseStart_1326858 := by decide
  rcases family_descends (prefixWord ++ tailWord_1326858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1326885 : List Nat := [1, 3, 1, 2, 3, 3, 2, 1, 2, 1, 4]
def baseStart_1326885 : Nat := 118140960795 + 1326885 * 2 ^ 59
def prefixEnd_1326885 : Nat := 4983230072969 + 3 ^ 40 * 1326885 * 2
def baseEnd_1326885 : Nat := 681329778241146290035273

theorem tailTrace_1326885 : CollatzResearch.WordTrace tailWord_1326885 prefixEnd_1326885 681329778241146290035273 := by
  unfold tailWord_1326885
  simp only [CollatzResearch.WordTrace]
  refine ⟨48395471797929733761454109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32263647865286489174302739 48395471797929733761454109)
  ·
    refine ⟨18148301924223650160545291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 48395471797929733761454109 18148301924223650160545291)
    ·
      refine ⟨27222452886335475240817937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18148301924223650160545291 27222452886335475240817937)
      ·
        refine ⟨20416839664751606430613453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27222452886335475240817937 20416839664751606430613453)
        ·
          refine ⟨7656314874281852411480045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20416839664751606430613453 7656314874281852411480045)
          ·
            refine ⟨2871118077855694654305017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7656314874281852411480045 2871118077855694654305017)
            ·
              refine ⟨2153338558391770990728763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2871118077855694654305017 2153338558391770990728763)
              ·
                refine ⟨3230007837587656486093145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2153338558391770990728763 3230007837587656486093145)
                ·
                  refine ⟨2422505878190742364569859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3230007837587656486093145 2422505878190742364569859)
                  ·
                    refine ⟨3633758817286113546854789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2422505878190742364569859 3633758817286113546854789)
                    ·
                      refine ⟨681329778241146290035273, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3633758817286113546854789 681329778241146290035273)
                      ·
                        rfl

theorem cell23_1326885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 3, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 3, 2, 1, 2, 1, 4].length) (baseStart_1326885 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1326885 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1326885 prefixEnd_1326885 := by exact prefixLift 1326885
  have htrace : WordTrace (prefixWord ++ tailWord_1326885) baseStart_1326885 baseEnd_1326885 := by
    simpa [prefixWord, tailWord_1326885, baseEnd_1326885] using wordTrace_append hprefix tailTrace_1326885
  have hstable : (prefixWord ++ tailWord_1326885).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1326885).length < 2 ^ (prefixWord ++ tailWord_1326885).sum := by decide
  have hdescent : baseEnd_1326885 < baseStart_1326885 := by decide
  rcases family_descends (prefixWord ++ tailWord_1326885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1326902 : List Nat := [5, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4]
def baseStart_1326902 : Nat := 118140960795 + 1326902 * 2 ^ 59
def prefixEnd_1326902 : Nat := 4983230072969 + 3 ^ 40 * 1326902 * 2
def baseEnd_1326902 : Nat := 681338507412272723522695

theorem tailTrace_1326902 : CollatzResearch.WordTrace tailWord_1326902 prefixEnd_1326902 681338507412272723522695 := by
  unfold tailWord_1326902
  simp only [CollatzResearch.WordTrace]
  refine ⟨3024755739929259104051435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 32264061225912097109881973 3024755739929259104051435)
  ·
    refine ⟨4537133609893888656077153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3024755739929259104051435 4537133609893888656077153)
    ·
      refine ⟨3402850207420416492057865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4537133609893888656077153 3402850207420416492057865)
      ·
        refine ⟨2552137655565312369043399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3402850207420416492057865 2552137655565312369043399)
        ·
          refine ⟨3828206483347968553565099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2552137655565312369043399 3828206483347968553565099)
          ·
            refine ⟨5742309725021952830347649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3828206483347968553565099 5742309725021952830347649)
            ·
              refine ⟨4306732293766464622760737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5742309725021952830347649 4306732293766464622760737)
              ·
                refine ⟨3230049220324848467070553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4306732293766464622760737 3230049220324848467070553)
                ·
                  refine ⟨2422536915243636350302915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3230049220324848467070553 2422536915243636350302915)
                  ·
                    refine ⟨3633805372865454525454373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2422536915243636350302915 3633805372865454525454373)
                    ·
                      refine ⟨681338507412272723522695, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3633805372865454525454373 681338507412272723522695)
                      ·
                        rfl

theorem cell23_1326902_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4].length) (baseStart_1326902 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1326902 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1326902 prefixEnd_1326902 := by exact prefixLift 1326902
  have htrace : WordTrace (prefixWord ++ tailWord_1326902) baseStart_1326902 baseEnd_1326902 := by
    simpa [prefixWord, tailWord_1326902, baseEnd_1326902] using wordTrace_append hprefix tailTrace_1326902
  have hstable : (prefixWord ++ tailWord_1326902).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1326902).length < 2 ^ (prefixWord ++ tailWord_1326902).sum := by decide
  have hdescent : baseEnd_1326902 < baseStart_1326902 := by decide
  rcases family_descends (prefixWord ++ tailWord_1326902) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1326908 : List Nat := [2, 2, 2, 2, 1, 1, 3, 4, 6]
def baseStart_1326908 : Nat := 118140960795 + 1326908 * 2 ^ 59
def prefixEnd_1326908 : Nat := 4983230072969 + 3 ^ 40 * 1326908 * 2
def baseEnd_1326908 : Nat := 75704620921799966671963

theorem tailTrace_1326908 : CollatzResearch.WordTrace tailWord_1326908 prefixEnd_1326908 75704620921799966671963 := by
  unfold tailWord_1326908
  simp only [CollatzResearch.WordTrace]
  refine ⟨24198155338423204344770689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32264207117897605793027585 24198155338423204344770689)
  ·
    refine ⟨18148616503817403258578017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24198155338423204344770689 18148616503817403258578017)
    ·
      refine ⟨13611462377863052443933513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18148616503817403258578017 13611462377863052443933513)
      ·
        refine ⟨10208596783397289332950135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13611462377863052443933513 10208596783397289332950135)
        ·
          refine ⟨15312895175095933999425203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10208596783397289332950135 15312895175095933999425203)
          ·
            refine ⟨22969342762643900999137805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15312895175095933999425203 22969342762643900999137805)
            ·
              refine ⟨8613503535991462874676677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22969342762643900999137805 8613503535991462874676677)
              ·
                refine ⟨1615031912998399289001877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8613503535991462874676677 1615031912998399289001877)
                ·
                  refine ⟨75704620921799966671963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1615031912998399289001877 75704620921799966671963)
                  ·
                    rfl

theorem cell23_1326908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 3, 4, 6].length) (baseStart_1326908 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1326908 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1326908 prefixEnd_1326908 := by exact prefixLift 1326908
  have htrace : WordTrace (prefixWord ++ tailWord_1326908) baseStart_1326908 baseEnd_1326908 := by
    simpa [prefixWord, tailWord_1326908, baseEnd_1326908] using wordTrace_append hprefix tailTrace_1326908
  have hstable : (prefixWord ++ tailWord_1326908).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1326908).length < 2 ^ (prefixWord ++ tailWord_1326908).sum := by decide
  have hdescent : baseEnd_1326908 < baseStart_1326908 := by decide
  rcases family_descends (prefixWord ++ tailWord_1326908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1326938 : List Nat := [3, 1, 1, 2, 1, 3, 1, 3, 3, 5]
def baseStart_1326938 : Nat := 118140960795 + 1326938 * 2 ^ 59
def prefixEnd_1326938 : Nat := 4983230072969 + 3 ^ 40 * 1326938 * 2
def baseEnd_1326938 : Nat := 227118997571944860890843

theorem tailTrace_1326938 : CollatzResearch.WordTrace tailWord_1326938 prefixEnd_1326938 227118997571944860890843 := by
  unfold tailWord_1326938
  simp only [CollatzResearch.WordTrace]
  refine ⟨12099351216684430953283367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32264936577825149208755645 12099351216684430953283367)
  ·
    refine ⟨18149026825026646429925051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12099351216684430953283367 18149026825026646429925051)
    ·
      refine ⟨27223540237539969644887577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18149026825026646429925051 27223540237539969644887577)
      ·
        refine ⟨20417655178154977233665683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27223540237539969644887577 20417655178154977233665683)
        ·
          refine ⟨30626482767232465850498525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20417655178154977233665683 30626482767232465850498525)
          ·
            refine ⟨11484931037712174693936947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30626482767232465850498525 11484931037712174693936947)
            ·
              refine ⟨17227396556568262040905421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11484931037712174693936947 17227396556568262040905421)
              ·
                refine ⟨6460273708713098265339533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17227396556568262040905421 6460273708713098265339533)
                ·
                  refine ⟨2422602640767411849502325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6460273708713098265339533 2422602640767411849502325)
                  ·
                    refine ⟨227118997571944860890843, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2422602640767411849502325 227118997571944860890843)
                    ·
                      rfl

theorem cell23_1326938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 1, 3, 3, 5].length) (baseStart_1326938 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1326938 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1326938 prefixEnd_1326938 := by exact prefixLift 1326938
  have htrace : WordTrace (prefixWord ++ tailWord_1326938) baseStart_1326938 baseEnd_1326938 := by
    simpa [prefixWord, tailWord_1326938, baseEnd_1326938] using wordTrace_append hprefix tailTrace_1326938
  have hstable : (prefixWord ++ tailWord_1326938).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1326938).length < 2 ^ (prefixWord ++ tailWord_1326938).sum := by decide
  have hdescent : baseEnd_1326938 < baseStart_1326938 := by decide
  rcases family_descends (prefixWord ++ tailWord_1326938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1326945 : List Nat := [1, 2, 3, 1, 1, 1, 5, 1, 1, 5, 2]
def baseStart_1326945 : Nat := 118140960795 + 1326945 * 2 ^ 59
def prefixEnd_1326945 : Nat := 4983230072969 + 3 ^ 40 * 1326945 * 2
def baseEnd_1326945 : Nat := 681360587080416055284997

theorem tailTrace_1326945 : CollatzResearch.WordTrace tailWord_1326945 prefixEnd_1326945 681360587080416055284997 := by
  unfold tailWord_1326945
  simp only [CollatzResearch.WordTrace]
  refine ⟨48397660177712364008638289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32265106785141576005758859 48397660177712364008638289)
  ·
    refine ⟨36298245133284273006478717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48397660177712364008638289 36298245133284273006478717)
    ·
      refine ⟨13611841924981602377429519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 36298245133284273006478717 13611841924981602377429519)
      ·
        refine ⟨20417762887472403566144279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13611841924981602377429519 20417762887472403566144279)
        ·
          refine ⟨30626644331208605349216419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20417762887472403566144279 30626644331208605349216419)
          ·
            refine ⟨45939966496812908023824629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30626644331208605349216419 45939966496812908023824629)
            ·
              refine ⟨4306871859076210127233559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 45939966496812908023824629 4306871859076210127233559)
              ·
                refine ⟨6460307788614315190850339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4306871859076210127233559 6460307788614315190850339)
                ·
                  refine ⟨9690461682921472786275509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6460307788614315190850339 9690461682921472786275509)
                  ·
                    refine ⟨908480782773888073713329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9690461682921472786275509 908480782773888073713329)
                    ·
                      refine ⟨681360587080416055284997, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 908480782773888073713329 681360587080416055284997)
                      ·
                        rfl

theorem cell23_1326945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 5, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 5, 1, 1, 5, 2].length) (baseStart_1326945 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1326945 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1326945 prefixEnd_1326945 := by exact prefixLift 1326945
  have htrace : WordTrace (prefixWord ++ tailWord_1326945) baseStart_1326945 baseEnd_1326945 := by
    simpa [prefixWord, tailWord_1326945, baseEnd_1326945] using wordTrace_append hprefix tailTrace_1326945
  have hstable : (prefixWord ++ tailWord_1326945).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1326945).length < 2 ^ (prefixWord ++ tailWord_1326945).sum := by decide
  have hdescent : baseEnd_1326945 < baseStart_1326945 := by decide
  rcases family_descends (prefixWord ++ tailWord_1326945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1327012 : List Nat := [2, 3, 1, 2, 1, 3, 2, 3, 1, 2, 3]
def baseStart_1327012 : Nat := 118140960795 + 1327012 * 2 ^ 59
def prefixEnd_1327012 : Nat := 4983230072969 + 3 ^ 40 * 1327012 * 2
def baseEnd_1327012 : Nat := 681394990284267293147189

theorem tailTrace_1327012 : CollatzResearch.WordTrace tailWord_1327012 prefixEnd_1327012 681394990284267293147189 := by
  unfold tailWord_1327012
  simp only [CollatzResearch.WordTrace]
  refine ⟨24200051934234817225663645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32266735912313089634218193 24200051934234817225663645)
  ·
    refine ⟨9075019475338056459623867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24200051934234817225663645 9075019475338056459623867)
    ·
      refine ⟨13612529213007084689435801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9075019475338056459623867 13612529213007084689435801)
      ·
        refine ⟨10209396909755313517076851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13612529213007084689435801 10209396909755313517076851)
        ·
          refine ⟨15314095364632970275615277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10209396909755313517076851 15314095364632970275615277)
          ·
            refine ⟨5742785761737363853355729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15314095364632970275615277 5742785761737363853355729)
            ·
              refine ⟨4307089321303022890016797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5742785761737363853355729 4307089321303022890016797)
              ·
                refine ⟨1615158495488633583756299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4307089321303022890016797 1615158495488633583756299)
                ·
                  refine ⟨2422737743232950375634449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1615158495488633583756299 2422737743232950375634449)
                  ·
                    refine ⟨1817053307424712781725837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2422737743232950375634449 1817053307424712781725837)
                    ·
                      refine ⟨681394990284267293147189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1817053307424712781725837 681394990284267293147189)
                      ·
                        rfl

theorem cell23_1327012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 2, 3, 1, 2, 3].length) (baseStart_1327012 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1327012 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1327012 prefixEnd_1327012 := by exact prefixLift 1327012
  have htrace : WordTrace (prefixWord ++ tailWord_1327012) baseStart_1327012 baseEnd_1327012 := by
    simpa [prefixWord, tailWord_1327012, baseEnd_1327012] using wordTrace_append hprefix tailTrace_1327012
  have hstable : (prefixWord ++ tailWord_1327012).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1327012).length < 2 ^ (prefixWord ++ tailWord_1327012).sum := by decide
  have hdescent : baseEnd_1327012 < baseStart_1327012 := by decide
  rcases family_descends (prefixWord ++ tailWord_1327012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1327015 : List Nat := [1, 1, 6, 1, 2, 3, 9]
def baseStart_1327015 : Nat := 118140960795 + 1327015 * 2 ^ 59
def prefixEnd_1327015 : Nat := 4983230072969 + 3 ^ 40 * 1327015 * 2
def baseEnd_1327015 : Nat := 8412302848471984955675

theorem tailTrace_1327015 : CollatzResearch.WordTrace tailWord_1327015 prefixEnd_1327015 8412302848471984955675 := by
  unfold tailWord_1327015
  simp only [CollatzResearch.WordTrace]
  refine ⟨48400213287458765963686499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32266808858305843975790999 48400213287458765963686499)
  ·
    refine ⟨72600319931188148945529749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48400213287458765963686499 72600319931188148945529749)
    ·
      refine ⟨3403139996774444481821707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 72600319931188148945529749 3403139996774444481821707)
      ·
        refine ⟨5104709995161666722732561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3403139996774444481821707 5104709995161666722732561)
        ·
          refine ⟨3828532496371250042049421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5104709995161666722732561 3828532496371250042049421)
          ·
            refine ⟨1435699686139218765768533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3828532496371250042049421 1435699686139218765768533)
            ·
              refine ⟨8412302848471984955675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 1435699686139218765768533 8412302848471984955675)
              ·
                rfl

theorem cell23_1327015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 3, 9].length) (baseStart_1327015 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1327015 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1327015 prefixEnd_1327015 := by exact prefixLift 1327015
  have htrace : WordTrace (prefixWord ++ tailWord_1327015) baseStart_1327015 baseEnd_1327015 := by
    simpa [prefixWord, tailWord_1327015, baseEnd_1327015] using wordTrace_append hprefix tailTrace_1327015
  have hstable : (prefixWord ++ tailWord_1327015).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1327015).length < 2 ^ (prefixWord ++ tailWord_1327015).sum := by decide
  have hdescent : baseEnd_1327015 < baseStart_1327015 := by decide
  rcases family_descends (prefixWord ++ tailWord_1327015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1327082 : List Nat := [3, 1, 3, 1, 2, 1, 1, 2, 3, 4, 2]
def baseStart_1327082 : Nat := 118140960795 + 1327082 * 2 ^ 59
def prefixEnd_1327082 : Nat := 4983230072969 + 3 ^ 40 * 1327082 * 2
def baseEnd_1327082 : Nat := 681430933930082019271867

theorem tailTrace_1327082 : CollatzResearch.WordTrace tailWord_1327082 prefixEnd_1327082 681430933930082019271867 := by
  unfold tailWord_1327082
  simp only [CollatzResearch.WordTrace]
  refine ⟨12100664244554009101593875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32268437985477357604250333 12100664244554009101593875)
  ·
    refine ⟨18150996366831013652390813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12100664244554009101593875 18150996366831013652390813)
    ·
      refine ⟨6806623637561630119646555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18150996366831013652390813 6806623637561630119646555)
      ·
        refine ⟨10209935456342445179469833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6806623637561630119646555 10209935456342445179469833)
        ·
          refine ⟨7657451592256833884602375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10209935456342445179469833 7657451592256833884602375)
          ·
            refine ⟨11486177388385250826903563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7657451592256833884602375 11486177388385250826903563)
            ·
              refine ⟨17229266082577876240355345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11486177388385250826903563 17229266082577876240355345)
              ·
                refine ⟨12921949561933407180266509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17229266082577876240355345 12921949561933407180266509)
                ·
                  refine ⟨4845731085725027692599941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12921949561933407180266509 4845731085725027692599941)
                  ·
                    refine ⟨908574578573442692362489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4845731085725027692599941 908574578573442692362489)
                    ·
                      refine ⟨681430933930082019271867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 908574578573442692362489 681430933930082019271867)
                      ·
                        rfl

theorem cell23_1327082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 1, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 1, 2, 3, 4, 2].length) (baseStart_1327082 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1327082 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1327082 prefixEnd_1327082 := by exact prefixLift 1327082
  have htrace : WordTrace (prefixWord ++ tailWord_1327082) baseStart_1327082 baseEnd_1327082 := by
    simpa [prefixWord, tailWord_1327082, baseEnd_1327082] using wordTrace_append hprefix tailTrace_1327082
  have hstable : (prefixWord ++ tailWord_1327082).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1327082).length < 2 ^ (prefixWord ++ tailWord_1327082).sum := by decide
  have hdescent : baseEnd_1327082 < baseStart_1327082 := by decide
  rcases family_descends (prefixWord ++ tailWord_1327082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1327099 : List Nat := [1, 1, 1, 1, 1, 3, 6, 3, 2, 2, 2]
def baseStart_1327099 : Nat := 118140960795 + 1327099 * 2 ^ 59
def prefixEnd_1327099 : Nat := 4983230072969 + 3 ^ 40 * 1327099 * 2
def baseEnd_1327099 : Nat := 681439663101208452759289

theorem tailTrace_1327099 : CollatzResearch.WordTrace tailWord_1327099 prefixEnd_1327099 681439663101208452759289 := by
  unfold tailWord_1327099
  simp only [CollatzResearch.WordTrace]
  refine ⟨48403277019154448309744351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32268851346102965539829567 48403277019154448309744351)
  ·
    refine ⟨72604915528731672464616527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48403277019154448309744351 72604915528731672464616527)
    ·
      refine ⟨108907373293097508696924791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72604915528731672464616527 108907373293097508696924791)
      ·
        refine ⟨163361059939646263045387187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 108907373293097508696924791 163361059939646263045387187)
        ·
          refine ⟨245041589909469394568080781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 163361059939646263045387187 245041589909469394568080781)
          ·
            refine ⟨91890596216051022963030293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 245041589909469394568080781 91890596216051022963030293)
            ·
              refine ⟨4307371697627391701392045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 91890596216051022963030293 4307371697627391701392045)
              ·
                refine ⟨1615264386610271888022017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4307371697627391701392045 1615264386610271888022017)
                ·
                  refine ⟨1211448289957703916016513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1615264386610271888022017 1211448289957703916016513)
                  ·
                    refine ⟨908586217468277937012385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1211448289957703916016513 908586217468277937012385)
                    ·
                      refine ⟨681439663101208452759289, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 908586217468277937012385 681439663101208452759289)
                      ·
                        rfl

theorem cell23_1327099_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 6, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 6, 3, 2, 2, 2].length) (baseStart_1327099 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1327099 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1327099 prefixEnd_1327099 := by exact prefixLift 1327099
  have htrace : WordTrace (prefixWord ++ tailWord_1327099) baseStart_1327099 baseEnd_1327099 := by
    simpa [prefixWord, tailWord_1327099, baseEnd_1327099] using wordTrace_append hprefix tailTrace_1327099
  have hstable : (prefixWord ++ tailWord_1327099).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1327099).length < 2 ^ (prefixWord ++ tailWord_1327099).sum := by decide
  have hdescent : baseEnd_1327099 < baseStart_1327099 := by decide
  rcases family_descends (prefixWord ++ tailWord_1327099) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1327105 : List Nat := [1, 2, 4, 1, 2, 1, 3, 2, 7]
def baseStart_1327105 : Nat := 118140960795 + 1327105 * 2 ^ 59
def prefixEnd_1327105 : Nat := 4983230072969 + 3 ^ 40 * 1327105 * 2
def baseEnd_1327105 : Nat := 75715860442792825476029

theorem tailTrace_1327105 : CollatzResearch.WordTrace tailWord_1327105 prefixEnd_1327105 75715860442792825476029 := by
  unfold tailWord_1327105
  simp only [CollatzResearch.WordTrace]
  refine ⟨48403495857132711334462769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32268997238088474222975179 48403495857132711334462769)
  ·
    refine ⟨36302621892849533500847077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48403495857132711334462769 36302621892849533500847077)
    ·
      refine ⟨6806741604909287531408827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 36302621892849533500847077 6806741604909287531408827)
      ·
        refine ⟨10210112407363931297113241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6806741604909287531408827 10210112407363931297113241)
        ·
          refine ⟨7657584305522948472834931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10210112407363931297113241 7657584305522948472834931)
          ·
            refine ⟨11486376458284422709252397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7657584305522948472834931 11486376458284422709252397)
            ·
              refine ⟨4307391171856658515969649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11486376458284422709252397 4307391171856658515969649)
              ·
                refine ⟨3230543378892493886977237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4307391171856658515969649 3230543378892493886977237)
                ·
                  refine ⟨75715860442792825476029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3230543378892493886977237 75715860442792825476029)
                  ·
                    rfl

theorem cell23_1327105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 3, 2, 7].length) (baseStart_1327105 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1327105 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1327105 prefixEnd_1327105 := by exact prefixLift 1327105
  have htrace : WordTrace (prefixWord ++ tailWord_1327105) baseStart_1327105 baseEnd_1327105 := by
    simpa [prefixWord, tailWord_1327105, baseEnd_1327105] using wordTrace_append hprefix tailTrace_1327105
  have hstable : (prefixWord ++ tailWord_1327105).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1327105).length < 2 ^ (prefixWord ++ tailWord_1327105).sum := by decide
  have hdescent : baseEnd_1327105 < baseStart_1327105 := by decide
  rcases family_descends (prefixWord ++ tailWord_1327105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1327115 : List Nat := [1, 1, 1, 1, 6, 1, 1, 2, 1, 5, 3]
def baseStart_1327115 : Nat := 118140960795 + 1327115 * 2 ^ 59
def prefixEnd_1327115 : Nat := 4983230072969 + 3 ^ 40 * 1327115 * 2
def baseEnd_1327115 : Nat := 681447878791680390159215

theorem tailTrace_1327115 : CollatzResearch.WordTrace tailWord_1327115 prefixEnd_1327115 681447878791680390159215 := by
  unfold tailWord_1327115
  simp only [CollatzResearch.WordTrace]
  refine ⟨48403860587096483042326799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32269240391397655361551199 48403860587096483042326799)
  ·
    refine ⟨72605790880644724563490199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48403860587096483042326799 72605790880644724563490199)
    ·
      refine ⟨108908686320967086845235299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72605790880644724563490199 108908686320967086845235299)
      ·
        refine ⟨163363029481450630267852949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 108908686320967086845235299 163363029481450630267852949)
        ·
          refine ⟨7657642006942998293805607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 163363029481450630267852949 7657642006942998293805607)
          ·
            refine ⟨11486463010414497440708411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7657642006942998293805607 11486463010414497440708411)
            ·
              refine ⟨17229694515621746161062617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11486463010414497440708411 17229694515621746161062617)
              ·
                refine ⟨12922270886716309620796963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17229694515621746161062617 12922270886716309620796963)
                ·
                  refine ⟨19383406330074464431195445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12922270886716309620796963 19383406330074464431195445)
                  ·
                    refine ⟨1817194343444481040424573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 19383406330074464431195445 1817194343444481040424573)
                    ·
                      refine ⟨681447878791680390159215, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1817194343444481040424573 681447878791680390159215)
                      ·
                        rfl

theorem cell23_1327115_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 1, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 1, 2, 1, 5, 3].length) (baseStart_1327115 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1327115 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1327115 prefixEnd_1327115 := by exact prefixLift 1327115
  have htrace : WordTrace (prefixWord ++ tailWord_1327115) baseStart_1327115 baseEnd_1327115 := by
    simpa [prefixWord, tailWord_1327115, baseEnd_1327115] using wordTrace_append hprefix tailTrace_1327115
  have hstable : (prefixWord ++ tailWord_1327115).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1327115).length < 2 ^ (prefixWord ++ tailWord_1327115).sum := by decide
  have hdescent : baseEnd_1327115 < baseStart_1327115 := by decide
  rcases family_descends (prefixWord ++ tailWord_1327115) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1327132 : List Nat := [2, 2, 3, 1, 3, 1, 1, 2, 2, 3, 3]
def baseStart_1327132 : Nat := 118140960795 + 1327132 * 2 ^ 59
def prefixEnd_1327132 : Nat := 4983230072969 + 3 ^ 40 * 1327132 * 2
def baseEnd_1327132 : Nat := 681456607962806823646637

theorem tailTrace_1327132 : CollatzResearch.WordTrace tailWord_1327132 prefixEnd_1327132 681456607962806823646637 := by
  unfold tailWord_1327132
  simp only [CollatzResearch.WordTrace]
  refine ⟨24202240314017447472847825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32269653752023263297130433 24202240314017447472847825)
  ·
    refine ⟨18151680235513085604635869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24202240314017447472847825 18151680235513085604635869)
    ·
      refine ⟨6806880088317407101738451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18151680235513085604635869 6806880088317407101738451)
      ·
        refine ⟨10210320132476110652607677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6806880088317407101738451 10210320132476110652607677)
        ·
          refine ⟨3828870049678541494727879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10210320132476110652607677 3828870049678541494727879)
          ·
            refine ⟨5743305074517812242091819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3828870049678541494727879 5743305074517812242091819)
            ·
              refine ⟨8614957611776718363137729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5743305074517812242091819 8614957611776718363137729)
              ·
                refine ⟨6461218208832538772353297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8614957611776718363137729 6461218208832538772353297)
                ·
                  refine ⟨4845913656624404079264973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6461218208832538772353297 4845913656624404079264973)
                  ·
                    refine ⟨1817217621234151529724365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4845913656624404079264973 1817217621234151529724365)
                    ·
                      refine ⟨681456607962806823646637, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1817217621234151529724365 681456607962806823646637)
                      ·
                        rfl

theorem cell23_1327132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 1, 2, 2, 3, 3].length) (baseStart_1327132 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1327132 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1327132 prefixEnd_1327132 := by exact prefixLift 1327132
  have htrace : WordTrace (prefixWord ++ tailWord_1327132) baseStart_1327132 baseEnd_1327132 := by
    simpa [prefixWord, tailWord_1327132, baseEnd_1327132] using wordTrace_append hprefix tailTrace_1327132
  have hstable : (prefixWord ++ tailWord_1327132).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1327132).length < 2 ^ (prefixWord ++ tailWord_1327132).sum := by decide
  have hdescent : baseEnd_1327132 < baseStart_1327132 := by decide
  rcases family_descends (prefixWord ++ tailWord_1327132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1327133 : List Nat := [1, 4, 2, 2, 2, 3, 1, 2, 2, 2, 2]
def baseStart_1327133 : Nat := 118140960795 + 1327133 * 2 ^ 59
def prefixEnd_1327133 : Nat := 4983230072969 + 3 ^ 40 * 1327133 * 2
def baseEnd_1327133 : Nat := 681457121443461319734133

theorem tailTrace_1327133 : CollatzResearch.WordTrace tailWord_1327133 prefixEnd_1327133 681457121443461319734133 := by
  unfold tailWord_1327133
  simp only [CollatzResearch.WordTrace]
  refine ⟨48404517101031272116482053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32269678067354181410988035 48404517101031272116482053)
  ·
    refine ⟨9075846956443363521840385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 48404517101031272116482053 9075846956443363521840385)
    ·
      refine ⟨6806885217332522641380289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9075846956443363521840385 6806885217332522641380289)
      ·
        refine ⟨5105163912999391981035217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6806885217332522641380289 5105163912999391981035217)
        ·
          refine ⟨3828872934749543985776413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5105163912999391981035217 3828872934749543985776413)
          ·
            refine ⟨1435827350531078994666155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3828872934749543985776413 1435827350531078994666155)
            ·
              refine ⟨2153741025796618491999233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1435827350531078994666155 2153741025796618491999233)
              ·
                refine ⟨1615305769347463868999425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2153741025796618491999233 1615305769347463868999425)
                ·
                  refine ⟨1211479327010597901749569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1615305769347463868999425 1211479327010597901749569)
                  ·
                    refine ⟨908609495257948426312177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1211479327010597901749569 908609495257948426312177)
                    ·
                      refine ⟨681457121443461319734133, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 908609495257948426312177 681457121443461319734133)
                      ·
                        rfl

theorem cell23_1327133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 3, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 3, 1, 2, 2, 2, 2].length) (baseStart_1327133 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1327133 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1327133 prefixEnd_1327133 := by exact prefixLift 1327133
  have htrace : WordTrace (prefixWord ++ tailWord_1327133) baseStart_1327133 baseEnd_1327133 := by
    simpa [prefixWord, tailWord_1327133, baseEnd_1327133] using wordTrace_append hprefix tailTrace_1327133
  have hstable : (prefixWord ++ tailWord_1327133).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1327133).length < 2 ^ (prefixWord ++ tailWord_1327133).sum := by decide
  have hdescent : baseEnd_1327133 < baseStart_1327133 := by decide
  rcases family_descends (prefixWord ++ tailWord_1327133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1327135 : List Nat := [1, 1, 2, 4, 1, 2, 2, 1, 4, 5]
def baseStart_1327135 : Nat := 118140960795 + 1327135 * 2 ^ 59
def prefixEnd_1327135 : Nat := 4983230072969 + 3 ^ 40 * 1327135 * 2
def baseEnd_1327135 : Nat := 227152716134923437303041

theorem tailTrace_1327135 : CollatzResearch.WordTrace tailWord_1327135 prefixEnd_1327135 227152716134923437303041 := by
  unfold tailWord_1327135
  simp only [CollatzResearch.WordTrace]
  refine ⟨48404590047024026458054859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32269726698016017638703239 48404590047024026458054859)
  ·
    refine ⟨72606885070536039687082289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48404590047024026458054859 72606885070536039687082289)
    ·
      refine ⟨54455163802902029765311717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 72606885070536039687082289 54455163802902029765311717)
      ·
        refine ⟨10210343213044130580995947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 54455163802902029765311717 10210343213044130580995947)
        ·
          refine ⟨15315514819566195871493921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10210343213044130580995947 15315514819566195871493921)
          ·
            refine ⟨11486636114674646903620441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15315514819566195871493921 11486636114674646903620441)
            ·
              refine ⟨8614977086005985177715331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11486636114674646903620441 8614977086005985177715331)
              ·
                refine ⟨12922465629008977766572997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8614977086005985177715331 12922465629008977766572997)
                ·
                  refine ⟨2422962305439183331232437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12922465629008977766572997 2422962305439183331232437)
                  ·
                    refine ⟨227152716134923437303041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2422962305439183331232437 227152716134923437303041)
                    ·
                      rfl

theorem cell23_1327135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 2, 1, 4, 5].length) (baseStart_1327135 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1327135 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1327135 prefixEnd_1327135 := by exact prefixLift 1327135
  have htrace : WordTrace (prefixWord ++ tailWord_1327135) baseStart_1327135 baseEnd_1327135 := by
    simpa [prefixWord, tailWord_1327135, baseEnd_1327135] using wordTrace_append hprefix tailTrace_1327135
  have hstable : (prefixWord ++ tailWord_1327135).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1327135).length < 2 ^ (prefixWord ++ tailWord_1327135).sum := by decide
  have hdescent : baseEnd_1327135 < baseStart_1327135 := by decide
  rcases family_descends (prefixWord ++ tailWord_1327135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1327155 : List Nat := [1, 1, 1, 2, 4, 1, 3, 2, 1, 3, 4]
def baseStart_1327155 : Nat := 118140960795 + 1327155 * 2 ^ 59
def prefixEnd_1327155 : Nat := 4983230072969 + 3 ^ 40 * 1327155 * 2
def baseEnd_1327155 : Nat := 681468418017860233659031

theorem tailTrace_1327155 : CollatzResearch.WordTrace tailWord_1327155 prefixEnd_1327155 681468418017860233659031 := by
  unfold tailWord_1327155
  simp only [CollatzResearch.WordTrace]
  refine ⟨48405319506951569873782919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32270213004634379915855279 48405319506951569873782919)
  ·
    refine ⟨72607979260427354810674379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48405319506951569873782919 72607979260427354810674379)
    ·
      refine ⟨108911968890641032216011569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72607979260427354810674379 108911968890641032216011569)
      ·
        refine ⟨81683976667980774162008677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 108911968890641032216011569 81683976667980774162008677)
        ·
          refine ⟨15315745625246395155376627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 81683976667980774162008677 15315745625246395155376627)
          ·
            refine ⟨22973618437869592733064941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15315745625246395155376627 22973618437869592733064941)
            ·
              refine ⟨8615106914201097274899353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22973618437869592733064941 8615106914201097274899353)
              ·
                refine ⟨6461330185650822956174515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8615106914201097274899353 6461330185650822956174515)
                ·
                  refine ⟨9691995278476234434261773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6461330185650822956174515 9691995278476234434261773)
                  ·
                    refine ⟨3634498229428587912848165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9691995278476234434261773 3634498229428587912848165)
                    ·
                      refine ⟨681468418017860233659031, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3634498229428587912848165 681468418017860233659031)
                      ·
                        rfl

theorem cell23_1327155_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 3, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 3, 2, 1, 3, 4].length) (baseStart_1327155 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1327155 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1327155 prefixEnd_1327155 := by exact prefixLift 1327155
  have htrace : WordTrace (prefixWord ++ tailWord_1327155) baseStart_1327155 baseEnd_1327155 := by
    simpa [prefixWord, tailWord_1327155, baseEnd_1327155] using wordTrace_append hprefix tailTrace_1327155
  have hstable : (prefixWord ++ tailWord_1327155).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1327155).length < 2 ^ (prefixWord ++ tailWord_1327155).sum := by decide
  have hdescent : baseEnd_1327155 < baseStart_1327155 := by decide
  rcases family_descends (prefixWord ++ tailWord_1327155) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1327165 : List Nat := [1, 4, 1, 3, 1, 1, 1, 1, 2, 8]
def baseStart_1327165 : Nat := 118140960795 + 1327165 * 2 ^ 59
def prefixEnd_1327165 : Nat := 4983230072969 + 3 ^ 40 * 1327165 * 2
def baseEnd_1327165 : Nat := 227157850941468398177995

theorem tailTrace_1327165 : CollatzResearch.WordTrace tailWord_1327165 prefixEnd_1327165 227157850941468398177995 := by
  unfold tailWord_1327165
  simp only [CollatzResearch.WordTrace]
  refine ⟨48405684236915341581646949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32270456157943561054431299 48405684236915341581646949)
  ·
    refine ⟨9076065794421626546558803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 48405684236915341581646949 9076065794421626546558803)
    ·
      refine ⟨13614098691632439819838205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9076065794421626546558803 13614098691632439819838205)
      ·
        refine ⟨5105287009362164932439327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13614098691632439819838205 5105287009362164932439327)
        ·
          refine ⟨7657930514043247398658991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5105287009362164932439327 7657930514043247398658991)
          ·
            refine ⟨11486895771064871097988487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7657930514043247398658991 11486895771064871097988487)
            ·
              refine ⟨17230343656597306646982731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11486895771064871097988487 17230343656597306646982731)
              ·
                refine ⟨25845515484895959970474097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17230343656597306646982731 25845515484895959970474097)
                ·
                  refine ⟨19384136613671969977855573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25845515484895959970474097 19384136613671969977855573)
                  ·
                    refine ⟨227157850941468398177995, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 19384136613671969977855573 227157850941468398177995)
                    ·
                      rfl

theorem cell23_1327165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 1, 1, 2, 8].length) (baseStart_1327165 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1327165 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1327165 prefixEnd_1327165 := by exact prefixLift 1327165
  have htrace : WordTrace (prefixWord ++ tailWord_1327165) baseStart_1327165 baseEnd_1327165 := by
    simpa [prefixWord, tailWord_1327165, baseEnd_1327165] using wordTrace_append hprefix tailTrace_1327165
  have hstable : (prefixWord ++ tailWord_1327165).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1327165).length < 2 ^ (prefixWord ++ tailWord_1327165).sum := by decide
  have hdescent : baseEnd_1327165 < baseStart_1327165 := by decide
  rcases family_descends (prefixWord ++ tailWord_1327165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1327192 : List Nat := [2, 1, 2, 2, 1, 4, 1, 1, 4, 2, 3]
def baseStart_1327192 : Nat := 118140960795 + 1327192 * 2 ^ 59
def prefixEnd_1327192 : Nat := 4983230072969 + 3 ^ 40 * 1327192 * 2
def baseEnd_1327192 : Nat := 681487416802076588896361

theorem tailTrace_1327192 : CollatzResearch.WordTrace tailWord_1327192 prefixEnd_1327192 681487416802076588896361 := by
  unfold tailWord_1327192
  simp only [CollatzResearch.WordTrace]
  refine ⟨24203334503908762596439915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32271112671878350128586553 24203334503908762596439915)
  ·
    refine ⟨36305001755863143894659873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24203334503908762596439915 36305001755863143894659873)
    ·
      refine ⟨27228751316897357920994905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36305001755863143894659873 27228751316897357920994905)
      ·
        refine ⟨20421563487673018440746179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27228751316897357920994905 20421563487673018440746179)
        ·
          refine ⟨30632345231509527661119269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20421563487673018440746179 30632345231509527661119269)
          ·
            refine ⟨5743564730908036436459863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 30632345231509527661119269 5743564730908036436459863)
            ·
              refine ⟨8615347096362054654689795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5743564730908036436459863 8615347096362054654689795)
              ·
                refine ⟨12923020644543081982034693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8615347096362054654689795 12923020644543081982034693)
                ·
                  refine ⟨2423066370851827871631505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12923020644543081982034693 2423066370851827871631505)
                  ·
                    refine ⟨1817299778138870903723629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2423066370851827871631505 1817299778138870903723629)
                    ·
                      refine ⟨681487416802076588896361, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1817299778138870903723629 681487416802076588896361)
                      ·
                        rfl

theorem cell23_1327192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 1, 1, 4, 2, 3].length) (baseStart_1327192 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1327192 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1327192 prefixEnd_1327192 := by exact prefixLift 1327192
  have htrace : WordTrace (prefixWord ++ tailWord_1327192) baseStart_1327192 baseEnd_1327192 := by
    simpa [prefixWord, tailWord_1327192, baseEnd_1327192] using wordTrace_append hprefix tailTrace_1327192
  have hstable : (prefixWord ++ tailWord_1327192).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1327192).length < 2 ^ (prefixWord ++ tailWord_1327192).sum := by decide
  have hdescent : baseEnd_1327192 < baseStart_1327192 := by decide
  rcases family_descends (prefixWord ++ tailWord_1327192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1327212 : List Nat := [2, 2, 1, 1, 3, 4, 1, 3, 6]
def baseStart_1327212 : Nat := 118140960795 + 1327212 * 2 ^ 59
def prefixEnd_1327212 : Nat := 4983230072969 + 3 ^ 40 * 1327212 * 2
def baseEnd_1327212 : Nat := 75721965157240723405141

theorem tailTrace_1327212 : CollatzResearch.WordTrace tailWord_1327212 prefixEnd_1327212 75721965157240723405141 := by
  unfold tailWord_1327212
  simp only [CollatzResearch.WordTrace]
  refine ⟨24203699233872534304303945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32271598978496712405738593 24203699233872534304303945)
  ·
    refine ⟨18152774425404400728227959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24203699233872534304303945 18152774425404400728227959)
    ·
      refine ⟨27229161638106601092341939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18152774425404400728227959 27229161638106601092341939)
      ·
        refine ⟨40843742457159901638512909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27229161638106601092341939 40843742457159901638512909)
        ·
          refine ⟨15316403421434963114442341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 40843742457159901638512909 15316403421434963114442341)
          ·
            refine ⟨2871825641519055583957939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 15316403421434963114442341 2871825641519055583957939)
            ·
              refine ⟨4307738462278583375936909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2871825641519055583957939 4307738462278583375936909)
              ·
                refine ⟨1615401923354468765976341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4307738462278583375936909 1615401923354468765976341)
                ·
                  refine ⟨75721965157240723405141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1615401923354468765976341 75721965157240723405141)
                  ·
                    rfl

theorem cell23_1327212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 6].length) (baseStart_1327212 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1327212 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1327212 prefixEnd_1327212 := by exact prefixLift 1327212
  have htrace : WordTrace (prefixWord ++ tailWord_1327212) baseStart_1327212 baseEnd_1327212 := by
    simpa [prefixWord, tailWord_1327212, baseEnd_1327212] using wordTrace_append hprefix tailTrace_1327212
  have hstable : (prefixWord ++ tailWord_1327212).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1327212).length < 2 ^ (prefixWord ++ tailWord_1327212).sum := by decide
  have hdescent : baseEnd_1327212 < baseStart_1327212 := by decide
  rcases family_descends (prefixWord ++ tailWord_1327212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1327275 : List Nat := [1, 1, 1, 1, 2, 1, 1, 1, 7, 1, 6]
def baseStart_1327275 : Nat := 118140960795 + 1327275 * 2 ^ 59
def prefixEnd_1327275 : Nat := 4983230072969 + 3 ^ 40 * 1327275 * 2
def baseEnd_1327275 : Nat := 681530035696399764158479

theorem tailTrace_1327275 : CollatzResearch.WordTrace tailWord_1327275 prefixEnd_1327275 681530035696399764158479 := by
  unfold tailWord_1327275
  simp only [CollatzResearch.WordTrace]
  refine ⟨48409696266516830368151279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32273130844344553578767519 48409696266516830368151279)
  ·
    refine ⟨72614544399775245552226919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48409696266516830368151279 72614544399775245552226919)
    ·
      refine ⟨108921816599662868328340379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72614544399775245552226919 108921816599662868328340379)
      ·
        refine ⟨163382724899494302492510569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 108921816599662868328340379 163382724899494302492510569)
        ·
          refine ⟨122537043674620726869382927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 163382724899494302492510569 122537043674620726869382927)
          ·
            refine ⟨183805565511931090304074391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 122537043674620726869382927 183805565511931090304074391)
            ·
              refine ⟨275708348267896635456111587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 183805565511931090304074391 275708348267896635456111587)
              ·
                refine ⟨413562522401844953184167381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 275708348267896635456111587 413562522401844953184167381)
                ·
                  refine ⟨9692871618793241090253923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 413562522401844953184167381 9692871618793241090253923)
                  ·
                    refine ⟨14539307428189861635380885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9692871618793241090253923 14539307428189861635380885)
                    ·
                      refine ⟨681530035696399764158479, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 14539307428189861635380885 681530035696399764158479)
                      ·
                        rfl

theorem cell23_1327275_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 7, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 7, 1, 6].length) (baseStart_1327275 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1327275 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1327275 prefixEnd_1327275 := by exact prefixLift 1327275
  have htrace : WordTrace (prefixWord ++ tailWord_1327275) baseStart_1327275 baseEnd_1327275 := by
    simpa [prefixWord, tailWord_1327275, baseEnd_1327275] using wordTrace_append hprefix tailTrace_1327275
  have hstable : (prefixWord ++ tailWord_1327275).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1327275).length < 2 ^ (prefixWord ++ tailWord_1327275).sum := by decide
  have hdescent : baseEnd_1327275 < baseStart_1327275 := by decide
  rcases family_descends (prefixWord ++ tailWord_1327275) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1327296 : List Nat := [2, 1, 1, 2, 5, 1, 4, 1, 1, 1, 4]
def baseStart_1327296 : Nat := 118140960795 + 1327296 * 2 ^ 59
def prefixEnd_1327296 : Nat := 4983230072969 + 3 ^ 40 * 1327296 * 2
def baseEnd_1327296 : Nat := 681540818790144181995883

theorem tailTrace_1327296 : CollatzResearch.WordTrace tailWord_1327296 prefixEnd_1327296 681540818790144181995883 := by
  unfold tailWord_1327296
  simp only [CollatzResearch.WordTrace]
  refine ⟨24205231099720375477332871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32273641466293833969777161 24205231099720375477332871)
  ·
    refine ⟨36307846649580563215999307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24205231099720375477332871 36307846649580563215999307)
    ·
      refine ⟨54461769974370844823998961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36307846649580563215999307 54461769974370844823998961)
      ·
        refine ⟨40846327480778133617999221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54461769974370844823998961 40846327480778133617999221)
        ·
          refine ⟨3829343201322950026687427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 40846327480778133617999221 3829343201322950026687427)
          ·
            refine ⟨5744014801984425040031141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3829343201322950026687427 5744014801984425040031141)
            ·
              refine ⟨1077002775372079695005839, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5744014801984425040031141 1077002775372079695005839)
              ·
                refine ⟨1615504163058119542508759, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1077002775372079695005839 1615504163058119542508759)
                ·
                  refine ⟨2423256244587179313763139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1615504163058119542508759 2423256244587179313763139)
                  ·
                    refine ⟨3634884366880768970644709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2423256244587179313763139 3634884366880768970644709)
                    ·
                      refine ⟨681540818790144181995883, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3634884366880768970644709 681540818790144181995883)
                      ·
                        rfl

theorem cell23_1327296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 4, 1, 1, 1, 4].length) (baseStart_1327296 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1327296 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1327296 prefixEnd_1327296 := by exact prefixLift 1327296
  have htrace : WordTrace (prefixWord ++ tailWord_1327296) baseStart_1327296 baseEnd_1327296 := by
    simpa [prefixWord, tailWord_1327296, baseEnd_1327296] using wordTrace_append hprefix tailTrace_1327296
  have hstable : (prefixWord ++ tailWord_1327296).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1327296).length < 2 ^ (prefixWord ++ tailWord_1327296).sum := by decide
  have hdescent : baseEnd_1327296 < baseStart_1327296 := by decide
  rcases family_descends (prefixWord ++ tailWord_1327296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1327313 : List Nat := [1, 2, 2, 1, 2, 2, 4, 4, 1, 2, 2]
def baseStart_1327313 : Nat := 118140960795 + 1327313 * 2 ^ 59
def prefixEnd_1327313 : Nat := 4983230072969 + 3 ^ 40 * 1327313 * 2
def baseEnd_1327313 : Nat := 681549547961270615483305

theorem tailTrace_1327313 : CollatzResearch.WordTrace tailWord_1327313 prefixEnd_1327313 681549547961270615483305 := by
  unfold tailWord_1327313
  simp only [CollatzResearch.WordTrace]
  refine ⟨48411082240379162858034593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32274054826919441905356395 48411082240379162858034593)
  ·
    refine ⟨36308311680284372143525945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48411082240379162858034593 36308311680284372143525945)
    ·
      refine ⟨27231233760213279107644459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36308311680284372143525945 27231233760213279107644459)
      ·
        refine ⟨40846850640319918661466689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27231233760213279107644459 40846850640319918661466689)
        ·
          refine ⟨30635137980239938996100017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40846850640319918661466689 30635137980239938996100017)
          ·
            refine ⟨22976353485179954247075013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30635137980239938996100017 22976353485179954247075013)
            ·
              refine ⟨4308066278471241421326565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 22976353485179954247075013 4308066278471241421326565)
              ·
                refine ⟨807762427213357766498731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4308066278471241421326565 807762427213357766498731)
                ·
                  refine ⟨1211643640820036649748097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 807762427213357766498731 1211643640820036649748097)
                  ·
                    refine ⟨908732730615027487311073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1211643640820036649748097 908732730615027487311073)
                    ·
                      refine ⟨681549547961270615483305, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 908732730615027487311073 681549547961270615483305)
                      ·
                        rfl

theorem cell23_1327313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 4, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 4, 4, 1, 2, 2].length) (baseStart_1327313 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1327313 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1327313 prefixEnd_1327313 := by exact prefixLift 1327313
  have htrace : WordTrace (prefixWord ++ tailWord_1327313) baseStart_1327313 baseEnd_1327313 := by
    simpa [prefixWord, tailWord_1327313, baseEnd_1327313] using wordTrace_append hprefix tailTrace_1327313
  have hstable : (prefixWord ++ tailWord_1327313).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1327313).length < 2 ^ (prefixWord ++ tailWord_1327313).sum := by decide
  have hdescent : baseEnd_1327313 < baseStart_1327313 := by decide
  rcases family_descends (prefixWord ++ tailWord_1327313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1327346 : List Nat := [3, 2, 1, 3, 2, 1, 1, 2, 4, 1, 3]
def baseStart_1327346 : Nat := 118140960795 + 1327346 * 2 ^ 59
def prefixEnd_1327346 : Nat := 4983230072969 + 3 ^ 40 * 1327346 * 2
def baseEnd_1327346 : Nat := 681566492822868986370653

theorem tailTrace_1327346 : CollatzResearch.WordTrace tailWord_1327346 prefixEnd_1327346 681566492822868986370653 := by
  unfold tailWord_1327346
  simp only [CollatzResearch.WordTrace]
  refine ⟨12103071462314902373496473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32274857232839739662657261 12103071462314902373496473)
  ·
    refine ⟨9077303596736176780122355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12103071462314902373496473 9077303596736176780122355)
    ·
      refine ⟨13615955395104265170183533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9077303596736176780122355 13615955395104265170183533)
      ·
        refine ⟨5105983273164099438818825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13615955395104265170183533 5105983273164099438818825)
        ·
          refine ⟨3829487454873074579114119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5105983273164099438818825 3829487454873074579114119)
          ·
            refine ⟨5744231182309611868671179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3829487454873074579114119 5744231182309611868671179)
            ·
              refine ⟨8616346773464417803006769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5744231182309611868671179 8616346773464417803006769)
              ·
                refine ⟨6462260080098313352255077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8616346773464417803006769 6462260080098313352255077)
                ·
                  refine ⟨1211673765018433753547827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6462260080098313352255077 1211673765018433753547827)
                  ·
                    refine ⟨1817510647527650630321741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1211673765018433753547827 1817510647527650630321741)
                    ·
                      refine ⟨681566492822868986370653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1817510647527650630321741 681566492822868986370653)
                      ·
                        rfl

theorem cell23_1327346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 1, 2, 4, 1, 3].length) (baseStart_1327346 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1327346 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1327346 prefixEnd_1327346 := by exact prefixLift 1327346
  have htrace : WordTrace (prefixWord ++ tailWord_1327346) baseStart_1327346 baseEnd_1327346 := by
    simpa [prefixWord, tailWord_1327346, baseEnd_1327346] using wordTrace_append hprefix tailTrace_1327346
  have hstable : (prefixWord ++ tailWord_1327346).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1327346).length < 2 ^ (prefixWord ++ tailWord_1327346).sum := by decide
  have hdescent : baseEnd_1327346 < baseStart_1327346 := by decide
  rcases family_descends (prefixWord ++ tailWord_1327346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1327372 : List Nat := [2, 2, 1, 2, 2, 2, 1, 2, 1, 3, 5]
def baseStart_1327372 : Nat := 118140960795 + 1327372 * 2 ^ 59
def prefixEnd_1327372 : Nat := 4983230072969 + 3 ^ 40 * 1327372 * 2
def baseEnd_1327372 : Nat := 681579843319885884645533

theorem tailTrace_1327372 : CollatzResearch.WordTrace tailWord_1327372 prefixEnd_1327372 681579843319885884645533 := by
  unfold tailWord_1327372
  simp only [CollatzResearch.WordTrace]
  refine ⟨24206617073582707967216185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32275489431443610622954913 24206617073582707967216185)
  ·
    refine ⟨18154962805187030975412139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24206617073582707967216185 18154962805187030975412139)
    ·
      refine ⟨27232444207780546463118209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18154962805187030975412139 27232444207780546463118209)
      ·
        refine ⟨20424333155835409847338657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27232444207780546463118209 20424333155835409847338657)
        ·
          refine ⟨15318249866876557385503993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20424333155835409847338657 15318249866876557385503993)
          ·
            refine ⟨11488687400157418039127995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15318249866876557385503993 11488687400157418039127995)
            ·
              refine ⟨17233031100236127058691993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11488687400157418039127995 17233031100236127058691993)
              ·
                refine ⟨12924773325177095294018995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17233031100236127058691993 12924773325177095294018995)
                ·
                  refine ⟨19387159987765642941028493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12924773325177095294018995 19387159987765642941028493)
                  ·
                    refine ⟨7270184995412116102885685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19387159987765642941028493 7270184995412116102885685)
                    ·
                      refine ⟨681579843319885884645533, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7270184995412116102885685 681579843319885884645533)
                      ·
                        rfl

theorem cell23_1327372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 1, 2, 1, 3, 5].length) (baseStart_1327372 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1327372 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1327372 prefixEnd_1327372 := by exact prefixLift 1327372
  have htrace : WordTrace (prefixWord ++ tailWord_1327372) baseStart_1327372 baseEnd_1327372 := by
    simpa [prefixWord, tailWord_1327372, baseEnd_1327372] using wordTrace_append hprefix tailTrace_1327372
  have hstable : (prefixWord ++ tailWord_1327372).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1327372).length < 2 ^ (prefixWord ++ tailWord_1327372).sum := by decide
  have hdescent : baseEnd_1327372 < baseStart_1327372 := by decide
  rcases family_descends (prefixWord ++ tailWord_1327372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1327390 : List Nat := [4, 3, 2, 1, 1, 2, 1, 1, 3, 3, 2]
def baseStart_1327390 : Nat := 118140960795 + 1327390 * 2 ^ 59
def prefixEnd_1327390 : Nat := 4983230072969 + 3 ^ 40 * 1327390 * 2
def baseEnd_1327390 : Nat := 681589085971666814220451

theorem tailTrace_1327390 : CollatzResearch.WordTrace tailWord_1327390 prefixEnd_1327390 681589085971666814220451 := by
  unfold tailWord_1327390
  simp only [CollatzResearch.WordTrace]
  refine ⟨6051736332637525626073453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 32275927107400136672391749 6051736332637525626073453)
  ·
    refine ⟨2269401124739072109777545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6051736332637525626073453 2269401124739072109777545)
    ·
      refine ⟨1702050843554304082333159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2269401124739072109777545 1702050843554304082333159)
      ·
        refine ⟨2553076265331456123499739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1702050843554304082333159 2553076265331456123499739)
        ·
          refine ⟨3829614397997184185249609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2553076265331456123499739 3829614397997184185249609)
          ·
            refine ⟨2872210798497888138937207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3829614397997184185249609 2872210798497888138937207)
            ·
              refine ⟨4308316197746832208405811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2872210798497888138937207 4308316197746832208405811)
              ·
                refine ⟨6462474296620248312608717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4308316197746832208405811 6462474296620248312608717)
                ·
                  refine ⟨2423427861232593117228269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6462474296620248312608717 2423427861232593117228269)
                  ·
                    refine ⟨908785447962222418960601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2423427861232593117228269 908785447962222418960601)
                    ·
                      refine ⟨681589085971666814220451, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 908785447962222418960601 681589085971666814220451)
                      ·
                        rfl

theorem cell23_1327390_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 2, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 2, 1, 1, 3, 3, 2].length) (baseStart_1327390 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1327390 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1327390 prefixEnd_1327390 := by exact prefixLift 1327390
  have htrace : WordTrace (prefixWord ++ tailWord_1327390) baseStart_1327390 baseEnd_1327390 := by
    simpa [prefixWord, tailWord_1327390, baseEnd_1327390] using wordTrace_append hprefix tailTrace_1327390
  have hstable : (prefixWord ++ tailWord_1327390).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1327390).length < 2 ^ (prefixWord ++ tailWord_1327390).sum := by decide
  have hdescent : baseEnd_1327390 < baseStart_1327390 := by decide
  rcases family_descends (prefixWord ++ tailWord_1327390) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1327459 : List Nat := [1, 1, 1, 5, 2, 1, 3, 1, 1, 3, 4]
def baseStart_1327459 : Nat := 118140960795 + 1327459 * 2 ^ 59
def prefixEnd_1327459 : Nat := 4983230072969 + 3 ^ 40 * 1327459 * 2
def baseEnd_1327459 : Nat := 681624516136827044257633

theorem tailTrace_1327459 : CollatzResearch.WordTrace tailWord_1327459 prefixEnd_1327459 681624516136827044257633 := by
  unfold tailWord_1327459
  simp only [CollatzResearch.WordTrace]
  refine ⟨48416407297850229792849431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32277604865233486528566287 48416407297850229792849431)
  ·
    refine ⟨72624610946775344689274147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48416407297850229792849431 72624610946775344689274147)
    ·
      refine ⟨108936916420163017033911221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72624610946775344689274147 108936916420163017033911221)
      ·
        refine ⟨10212835914390282846929177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 108936916420163017033911221 10212835914390282846929177)
        ·
          refine ⟨7659626935792712135196883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10212835914390282846929177 7659626935792712135196883)
          ·
            refine ⟨11489440403689068202795325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7659626935792712135196883 11489440403689068202795325)
            ·
              refine ⟨4308540151383400576048247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11489440403689068202795325 4308540151383400576048247)
              ·
                refine ⟨6462810227075100864072371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4308540151383400576048247 6462810227075100864072371)
                ·
                  refine ⟨9694215340612651296108557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6462810227075100864072371 9694215340612651296108557)
                  ·
                    refine ⟨3635330752729744236040709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9694215340612651296108557 3635330752729744236040709)
                    ·
                      refine ⟨681624516136827044257633, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3635330752729744236040709 681624516136827044257633)
                      ·
                        rfl

theorem cell23_1327459_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 3, 1, 1, 3, 4].length) (baseStart_1327459 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1327459 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1327459 prefixEnd_1327459 := by exact prefixLift 1327459
  have htrace : WordTrace (prefixWord ++ tailWord_1327459) baseStart_1327459 baseEnd_1327459 := by
    simpa [prefixWord, tailWord_1327459, baseEnd_1327459] using wordTrace_append hprefix tailTrace_1327459
  have hstable : (prefixWord ++ tailWord_1327459).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1327459).length < 2 ^ (prefixWord ++ tailWord_1327459).sum := by decide
  have hdescent : baseEnd_1327459 < baseStart_1327459 := by decide
  rcases family_descends (prefixWord ++ tailWord_1327459) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1327509 : List Nat := [1, 3, 2, 1, 1, 2, 1, 1, 1, 7, 3]
def baseStart_1327509 : Nat := 118140960795 + 1327509 * 2 ^ 59
def prefixEnd_1327509 : Nat := 4983230072969 + 3 ^ 40 * 1327509 * 2
def baseEnd_1327509 : Nat := 681650190169551848632403

theorem tailTrace_1327509 : CollatzResearch.WordTrace tailWord_1327509 prefixEnd_1327509 681650190169551848632403 := by
  unfold tailWord_1327509
  simp only [CollatzResearch.WordTrace]
  refine ⟨48418230947669088332169581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32278820631779392221446387 48418230947669088332169581)
  ·
    refine ⟨18156836605375908124563593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 48418230947669088332169581 18156836605375908124563593)
    ·
      refine ⟨13617627454031931093422695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18156836605375908124563593 13617627454031931093422695)
      ·
        refine ⟨20426441181047896640134043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13617627454031931093422695 20426441181047896640134043)
        ·
          refine ⟨30639661771571844960201065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20426441181047896640134043 30639661771571844960201065)
          ·
            refine ⟨22979746328678883720150799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30639661771571844960201065 22979746328678883720150799)
            ·
              refine ⟨34469619493018325580226199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22979746328678883720150799 34469619493018325580226199)
              ·
                refine ⟨51704429239527488370339299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34469619493018325580226199 51704429239527488370339299)
                ·
                  refine ⟨77556643859291232555508949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 51704429239527488370339299 77556643859291232555508949)
                  ·
                    refine ⟨1817733840452138263019741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 77556643859291232555508949 1817733840452138263019741)
                    ·
                      refine ⟨681650190169551848632403, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1817733840452138263019741 681650190169551848632403)
                      ·
                        rfl

theorem cell23_1327509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 1, 1, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 1, 1, 1, 7, 3].length) (baseStart_1327509 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1327509 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1327509 prefixEnd_1327509 := by exact prefixLift 1327509
  have htrace : WordTrace (prefixWord ++ tailWord_1327509) baseStart_1327509 baseEnd_1327509 := by
    simpa [prefixWord, tailWord_1327509, baseEnd_1327509] using wordTrace_append hprefix tailTrace_1327509
  have hstable : (prefixWord ++ tailWord_1327509).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1327509).length < 2 ^ (prefixWord ++ tailWord_1327509).sum := by decide
  have hdescent : baseEnd_1327509 < baseStart_1327509 := by decide
  rcases family_descends (prefixWord ++ tailWord_1327509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1327520 : List Nat := [2, 1, 1, 4, 1, 5, 1, 3, 1, 4]
def baseStart_1327520 : Nat := 118140960795 + 1327520 * 2 ^ 59
def prefixEnd_1327520 : Nat := 4983230072969 + 3 ^ 40 * 1327520 * 2
def baseEnd_1327520 : Nat := 227218612818917101864951

theorem tailTrace_1327520 : CollatzResearch.WordTrace tailWord_1327520 prefixEnd_1327520 227218612818917101864951 := by
  unfold tailWord_1327520
  simp only [CollatzResearch.WordTrace]
  refine ⟨24209316075314618605410007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32279088100419491473880009 24209316075314618605410007)
  ·
    refine ⟨36313974112971927908115011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24209316075314618605410007 36313974112971927908115011)
    ·
      refine ⟨54470961169457891862172517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36313974112971927908115011 54470961169457891862172517)
      ·
        refine ⟨10213305219273354724157347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 54470961169457891862172517 10213305219273354724157347)
        ·
          refine ⟨15319957828910032086236021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10213305219273354724157347 15319957828910032086236021)
          ·
            refine ⟨1436246046460315508084627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 15319957828910032086236021 1436246046460315508084627)
            ·
              refine ⟨2154369069690473262126941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1436246046460315508084627 2154369069690473262126941)
              ·
                refine ⟨807888401133927473297603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2154369069690473262126941 807888401133927473297603)
                ·
                  refine ⟨1211832601700891209946405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 807888401133927473297603 1211832601700891209946405)
                  ·
                    refine ⟨227218612818917101864951, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1211832601700891209946405 227218612818917101864951)
                    ·
                      rfl

theorem cell23_1327520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 5, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 5, 1, 3, 1, 4].length) (baseStart_1327520 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1327520 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1327520 prefixEnd_1327520 := by exact prefixLift 1327520
  have htrace : WordTrace (prefixWord ++ tailWord_1327520) baseStart_1327520 baseEnd_1327520 := by
    simpa [prefixWord, tailWord_1327520, baseEnd_1327520] using wordTrace_append hprefix tailTrace_1327520
  have hstable : (prefixWord ++ tailWord_1327520).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1327520).length < 2 ^ (prefixWord ++ tailWord_1327520).sum := by decide
  have hdescent : baseEnd_1327520 < baseStart_1327520 := by decide
  rcases family_descends (prefixWord ++ tailWord_1327520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1327543 : List Nat := [1, 1, 3, 1, 3, 3, 3, 1, 3, 1, 3]
def baseStart_1327543 : Nat := 118140960795 + 1327543 * 2 ^ 59
def prefixEnd_1327543 : Nat := 4983230072969 + 3 ^ 40 * 1327543 * 2
def baseEnd_1327543 : Nat := 681667648511804715607247

theorem tailTrace_1327543 : CollatzResearch.WordTrace tailWord_1327543 prefixEnd_1327543 681667648511804715607247 := by
  unfold tailWord_1327543
  simp only [CollatzResearch.WordTrace]
  refine ⟨48419471029545912138907283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32279647353030608092604855 48419471029545912138907283)
  ·
    refine ⟨72629206544318868208360925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48419471029545912138907283 72629206544318868208360925)
    ·
      refine ⟨27235952454119575578135347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 72629206544318868208360925 27235952454119575578135347)
      ·
        refine ⟨40853928681179363367203021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27235952454119575578135347 40853928681179363367203021)
        ·
          refine ⟨15320223255442261262701133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 40853928681179363367203021 15320223255442261262701133)
          ·
            refine ⟨5745083720790847973512925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15320223255442261262701133 5745083720790847973512925)
            ·
              refine ⟨2154406395296567990067347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5745083720790847973512925 2154406395296567990067347)
              ·
                refine ⟨3231609592944851985101021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2154406395296567990067347 3231609592944851985101021)
                ·
                  refine ⟨1211853597354319494412883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3231609592944851985101021 1211853597354319494412883)
                  ·
                    refine ⟨1817780396031479241619325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1211853597354319494412883 1817780396031479241619325)
                    ·
                      refine ⟨681667648511804715607247, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1817780396031479241619325 681667648511804715607247)
                      ·
                        rfl

theorem cell23_1327543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 3, 1, 3, 1, 3].length) (baseStart_1327543 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1327543 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1327543 prefixEnd_1327543 := by exact prefixLift 1327543
  have htrace : WordTrace (prefixWord ++ tailWord_1327543) baseStart_1327543 baseEnd_1327543 := by
    simpa [prefixWord, tailWord_1327543, baseEnd_1327543] using wordTrace_append hprefix tailTrace_1327543
  have hstable : (prefixWord ++ tailWord_1327543).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1327543).length < 2 ^ (prefixWord ++ tailWord_1327543).sum := by decide
  have hdescent : baseEnd_1327543 < baseStart_1327543 := by decide
  rcases family_descends (prefixWord ++ tailWord_1327543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1327569 : List Nat := [1, 2, 2, 1, 2, 1, 1, 4, 3, 1, 5]
def baseStart_1327569 : Nat := 118140960795 + 1327569 * 2 ^ 59
def prefixEnd_1327569 : Nat := 4983230072969 + 3 ^ 40 * 1327569 * 2
def baseEnd_1327569 : Nat := 681680999008821613882127

theorem tailTrace_1327569 : CollatzResearch.WordTrace tailWord_1327569 prefixEnd_1327569 681680999008821613882127 := by
  unfold tailWord_1327569
  simp only [CollatzResearch.WordTrace]
  refine ⟨48420419327451718579353761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32280279551634479052902507 48420419327451718579353761)
  ·
    refine ⟨36315314495588788934515321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48420419327451718579353761 36315314495588788934515321)
    ·
      refine ⟨27236485871691591700886491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36315314495588788934515321 27236485871691591700886491)
      ·
        refine ⟨40854728807537387551329737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27236485871691591700886491 40854728807537387551329737)
        ·
          refine ⟨30641046605653040663497303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40854728807537387551329737 30641046605653040663497303)
          ·
            refine ⟨45961569908479560995245955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30641046605653040663497303 45961569908479560995245955)
            ·
              refine ⟨68942354862719341492868933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45961569908479560995245955 68942354862719341492868933)
              ·
                refine ⟨12926691536759876529912925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 68942354862719341492868933 12926691536759876529912925)
                ·
                  refine ⟨4847509326284953698717347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12926691536759876529912925 4847509326284953698717347)
                  ·
                    refine ⟨7271263989427430548076021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4847509326284953698717347 7271263989427430548076021)
                    ·
                      refine ⟨681680999008821613882127, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7271263989427430548076021 681680999008821613882127)
                      ·
                        rfl

theorem cell23_1327569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 4, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 4, 3, 1, 5].length) (baseStart_1327569 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1327569 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1327569 prefixEnd_1327569 := by exact prefixLift 1327569
  have htrace : WordTrace (prefixWord ++ tailWord_1327569) baseStart_1327569 baseEnd_1327569 := by
    simpa [prefixWord, tailWord_1327569, baseEnd_1327569] using wordTrace_append hprefix tailTrace_1327569
  have hstable : (prefixWord ++ tailWord_1327569).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1327569).length < 2 ^ (prefixWord ++ tailWord_1327569).sum := by decide
  have hdescent : baseEnd_1327569 < baseStart_1327569 := by decide
  rcases family_descends (prefixWord ++ tailWord_1327569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1327589 : List Nat := [1, 3, 1, 5, 13]
def baseStart_1327589 : Nat := 118140960795 + 1327589 * 2 ^ 59
def prefixEnd_1327589 : Nat := 4983230072969 + 3 ^ 40 * 1327589 * 2
def baseEnd_1327589 : Nat := 935104620880537085915

theorem tailTrace_1327589 : CollatzResearch.WordTrace tailWord_1327589 prefixEnd_1327589 935104620880537085915 := by
  unfold tailWord_1327589
  simp only [CollatzResearch.WordTrace]
  refine ⟨48421148787379261995081821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32280765858252841330054547 48421148787379261995081821)
  ·
    refine ⟨18157930795267223248155683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 48421148787379261995081821 18157930795267223248155683)
    ·
      refine ⟨27236896192900834872233525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18157930795267223248155683 27236896192900834872233525)
      ·
        refine ⟨2553459018084453269271893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 27236896192900834872233525 2553459018084453269271893)
        ·
          refine ⟨935104620880537085915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 13 2553459018084453269271893 935104620880537085915)
          ·
            rfl

theorem cell23_1327589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 13].length) (baseStart_1327589 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1327589 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1327589 prefixEnd_1327589 := by exact prefixLift 1327589
  have htrace : WordTrace (prefixWord ++ tailWord_1327589) baseStart_1327589 baseEnd_1327589 := by
    simpa [prefixWord, tailWord_1327589, baseEnd_1327589] using wordTrace_append hprefix tailTrace_1327589
  have hstable : (prefixWord ++ tailWord_1327589).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1327589).length < 2 ^ (prefixWord ++ tailWord_1327589).sum := by decide
  have hdescent : baseEnd_1327589 < baseStart_1327589 := by decide
  rcases family_descends (prefixWord ++ tailWord_1327589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1327594 : List Nat := [3, 1, 3, 1, 3, 3, 2, 2, 1, 1, 3]
def baseStart_1327594 : Nat := 118140960795 + 1327594 * 2 ^ 59
def prefixEnd_1327594 : Nat := 4983230072969 + 3 ^ 40 * 1327594 * 2
def baseEnd_1327594 : Nat := 681693836025184016069513

theorem tailTrace_1327594 : CollatzResearch.WordTrace tailWord_1327594 prefixEnd_1327594 681693836025184016069513 := by
  unfold tailWord_1327594
  simp only [CollatzResearch.WordTrace]
  refine ⟨12105332788090286962253459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32280887434907431899342557 12105332788090286962253459)
  ·
    refine ⟨18157999182135430443380189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12105332788090286962253459 18157999182135430443380189)
    ·
      refine ⟨6809249693300786416267571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18157999182135430443380189 6809249693300786416267571)
      ·
        refine ⟨10213874539951179624401357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6809249693300786416267571 10213874539951179624401357)
        ·
          refine ⟨3830202952481692359150509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10213874539951179624401357 3830202952481692359150509)
          ·
            refine ⟨1436326107180634634681441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3830202952481692359150509 1436326107180634634681441)
            ·
              refine ⟨1077244580385475976011081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1436326107180634634681441 1077244580385475976011081)
              ·
                refine ⟨807933435289106982008311, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1077244580385475976011081 807933435289106982008311)
                ·
                  refine ⟨1211900152933660473012467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 807933435289106982008311 1211900152933660473012467)
                  ·
                    refine ⟨1817850229400490709518701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1211900152933660473012467 1817850229400490709518701)
                    ·
                      refine ⟨681693836025184016069513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1817850229400490709518701 681693836025184016069513)
                      ·
                        rfl

theorem cell23_1327594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 3, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 3, 2, 2, 1, 1, 3].length) (baseStart_1327594 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1327594 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1327594 prefixEnd_1327594 := by exact prefixLift 1327594
  have htrace : WordTrace (prefixWord ++ tailWord_1327594) baseStart_1327594 baseEnd_1327594 := by
    simpa [prefixWord, tailWord_1327594, baseEnd_1327594] using wordTrace_append hprefix tailTrace_1327594
  have hstable : (prefixWord ++ tailWord_1327594).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1327594).length < 2 ^ (prefixWord ++ tailWord_1327594).sum := by decide
  have hdescent : baseEnd_1327594 < baseStart_1327594 := by decide
  rcases family_descends (prefixWord ++ tailWord_1327594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1327609 : List Nat := [1, 2, 1, 3, 1, 2, 2, 1, 2, 2, 6]
def baseStart_1327609 : Nat := 118140960795 + 1327609 * 2 ^ 59
def prefixEnd_1327609 : Nat := 4983230072969 + 3 ^ 40 * 1327609 * 2
def baseEnd_1327609 : Nat := 681701538235001457381943

theorem tailTrace_1327609 : CollatzResearch.WordTrace tailWord_1327609 prefixEnd_1327609 681701538235001457381943 := by
  unfold tailWord_1327609
  simp only [CollatzResearch.WordTrace]
  refine ⟨48421878247306805410809881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32281252164871203607206587 48421878247306805410809881)
  ·
    refine ⟨36316408685480104058107411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48421878247306805410809881 36316408685480104058107411)
    ·
      refine ⟨54474613028220156087161117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36316408685480104058107411 54474613028220156087161117)
      ·
        refine ⟨20427979885582558532685419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 54474613028220156087161117 20427979885582558532685419)
        ·
          refine ⟨30641969828373837799028129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20427979885582558532685419 30641969828373837799028129)
          ·
            refine ⟨22981477371280378349271097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30641969828373837799028129 22981477371280378349271097)
            ·
              refine ⟨17236108028460283761953323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22981477371280378349271097 17236108028460283761953323)
              ·
                refine ⟨25854162042690425642929985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17236108028460283761953323 25854162042690425642929985)
                ·
                  refine ⟨19390621532017819232197489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25854162042690425642929985 19390621532017819232197489)
                  ·
                    refine ⟨14542966149013364424148117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19390621532017819232197489 14542966149013364424148117)
                    ·
                      refine ⟨681701538235001457381943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 14542966149013364424148117 681701538235001457381943)
                      ·
                        rfl

theorem cell23_1327609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 2, 1, 2, 2, 6].length) (baseStart_1327609 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1327609 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1327609 prefixEnd_1327609 := by exact prefixLift 1327609
  have htrace : WordTrace (prefixWord ++ tailWord_1327609) baseStart_1327609 baseEnd_1327609 := by
    simpa [prefixWord, tailWord_1327609, baseEnd_1327609] using wordTrace_append hprefix tailTrace_1327609
  have hstable : (prefixWord ++ tailWord_1327609).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1327609).length < 2 ^ (prefixWord ++ tailWord_1327609).sum := by decide
  have hdescent : baseEnd_1327609 < baseStart_1327609 := by decide
  rcases family_descends (prefixWord ++ tailWord_1327609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1327619 : List Nat := [1, 1, 1, 3, 2, 1, 3, 2, 2, 7]
def baseStart_1327619 : Nat := 118140960795 + 1327619 * 2 ^ 59
def prefixEnd_1327619 : Nat := 4983230072969 + 3 ^ 40 * 1327619 * 2
def baseEnd_1327619 : Nat := 227235557680515472752299

theorem tailTrace_1327619 : CollatzResearch.WordTrace tailWord_1327619 prefixEnd_1327619 227235557680515472752299 := by
  unfold tailWord_1327619
  simp only [CollatzResearch.WordTrace]
  refine ⟨48422242977270577118673911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32281495318180384745782607 48422242977270577118673911)
  ·
    refine ⟨72633364465905865678010867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48422242977270577118673911 72633364465905865678010867)
    ·
      refine ⟨108950046698858798517016301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72633364465905865678010867 108950046698858798517016301)
      ·
        refine ⟨40856267512072049443881113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 108950046698858798517016301 40856267512072049443881113)
        ·
          refine ⟨30642200634054037082910835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40856267512072049443881113 30642200634054037082910835)
          ·
            refine ⟨45963300951081055624366253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30642200634054037082910835 45963300951081055624366253)
            ·
              refine ⟨17236237856655395859137345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 45963300951081055624366253 17236237856655395859137345)
              ·
                refine ⟨12927178392491546894353009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17236237856655395859137345 12927178392491546894353009)
                ·
                  refine ⟨9695383794368660170764757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12927178392491546894353009 9695383794368660170764757)
                  ·
                    refine ⟨227235557680515472752299, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 9695383794368660170764757 227235557680515472752299)
                    ·
                      rfl

theorem cell23_1327619_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 3, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 3, 2, 2, 7].length) (baseStart_1327619 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1327619 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1327619 prefixEnd_1327619 := by exact prefixLift 1327619
  have htrace : WordTrace (prefixWord ++ tailWord_1327619) baseStart_1327619 baseEnd_1327619 := by
    simpa [prefixWord, tailWord_1327619, baseEnd_1327619] using wordTrace_append hprefix tailTrace_1327619
  have hstable : (prefixWord ++ tailWord_1327619).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1327619).length < 2 ^ (prefixWord ++ tailWord_1327619).sum := by decide
  have hdescent : baseEnd_1327619 < baseStart_1327619 := by decide
  rcases family_descends (prefixWord ++ tailWord_1327619) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1327623 : List Nat := [1, 1, 4, 3, 3, 1, 3, 7]
def baseStart_1327623 : Nat := 118140960795 + 1327623 * 2 ^ 59
def prefixEnd_1327623 : Nat := 4983230072969 + 3 ^ 40 * 1327623 * 2
def baseEnd_1327623 : Nat := 25248471369043126022477

theorem tailTrace_1327623 : CollatzResearch.WordTrace tailWord_1327623 prefixEnd_1327623 25248471369043126022477 := by
  unfold tailWord_1327623
  simp only [CollatzResearch.WordTrace]
  refine ⟨48422388869256085801819523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32281592579504057201213015 48422388869256085801819523)
  ·
    refine ⟨72633583303884128702729285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48422388869256085801819523 72633583303884128702729285)
    ·
      refine ⟨13618796869478274131761741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 72633583303884128702729285 13618796869478274131761741)
      ·
        refine ⟨5107048826054352799410653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13618796869478274131761741 5107048826054352799410653)
        ·
          refine ⟨1915143309770382299778995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5107048826054352799410653 1915143309770382299778995)
          ·
            refine ⟨2872714964655573449668493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1915143309770382299778995 2872714964655573449668493)
            ·
              refine ⟨1077268111745840043625685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2872714964655573449668493 1077268111745840043625685)
              ·
                refine ⟨25248471369043126022477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1077268111745840043625685 25248471369043126022477)
                ·
                  rfl

theorem cell23_1327623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 3, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 3, 1, 3, 7].length) (baseStart_1327623 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1327623 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1327623 prefixEnd_1327623 := by exact prefixLift 1327623
  have htrace : WordTrace (prefixWord ++ tailWord_1327623) baseStart_1327623 baseEnd_1327623 := by
    simpa [prefixWord, tailWord_1327623, baseEnd_1327623] using wordTrace_append hprefix tailTrace_1327623
  have hstable : (prefixWord ++ tailWord_1327623).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1327623).length < 2 ^ (prefixWord ++ tailWord_1327623).sum := by decide
  have hdescent : baseEnd_1327623 < baseStart_1327623 := by decide
  rcases family_descends (prefixWord ++ tailWord_1327623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1327661 : List Nat := [1, 5, 4, 1, 1, 1, 3, 1, 2, 4]
def baseStart_1327661 : Nat := 118140960795 + 1327661 * 2 ^ 59
def prefixEnd_1327661 : Nat := 4983230072969 + 3 ^ 40 * 1327661 * 2
def baseEnd_1327661 : Nat := 227242746409678417977235

theorem tailTrace_1327661 : CollatzResearch.WordTrace tailWord_1327661 prefixEnd_1327661 227242746409678417977235 := by
  unfold tailWord_1327661
  simp only [CollatzResearch.WordTrace]
  refine ⟨48423774843118418291702837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32282516562078945527801891 48423774843118418291702837)
  ·
    refine ⟨4539728891542351714847141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 48423774843118418291702837 4539728891542351714847141)
    ·
      refine ⟨851199167164190946533839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4539728891542351714847141 851199167164190946533839)
      ·
        refine ⟨1276798750746286419800759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 851199167164190946533839 1276798750746286419800759)
        ·
          refine ⟨1915198126119429629701139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1276798750746286419800759 1915198126119429629701139)
          ·
            refine ⟨2872797189179144444551709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1915198126119429629701139 2872797189179144444551709)
            ·
              refine ⟨1077298945942179166706891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2872797189179144444551709 1077298945942179166706891)
              ·
                refine ⟨1615948418913268750060337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1077298945942179166706891 1615948418913268750060337)
                ·
                  refine ⟨1211961314184951562545253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1615948418913268750060337 1211961314184951562545253)
                  ·
                    refine ⟨227242746409678417977235, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1211961314184951562545253 227242746409678417977235)
                    ·
                      rfl

theorem cell23_1327661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 1, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 1, 1, 3, 1, 2, 4].length) (baseStart_1327661 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1327661 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1327661 prefixEnd_1327661 := by exact prefixLift 1327661
  have htrace : WordTrace (prefixWord ++ tailWord_1327661) baseStart_1327661 baseEnd_1327661 := by
    simpa [prefixWord, tailWord_1327661, baseEnd_1327661] using wordTrace_append hprefix tailTrace_1327661
  have hstable : (prefixWord ++ tailWord_1327661).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1327661).length < 2 ^ (prefixWord ++ tailWord_1327661).sum := by decide
  have hdescent : baseEnd_1327661 < baseStart_1327661 := by decide
  rcases family_descends (prefixWord ++ tailWord_1327661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1327666 : List Nat := [3, 2, 1, 1, 2, 1, 4, 1, 2, 6]
def baseStart_1327666 : Nat := 118140960795 + 1327666 * 2 ^ 59
def prefixEnd_1327666 : Nat := 4983230072969 + 3 ^ 40 * 1327666 * 2
def baseEnd_1327666 : Nat := 227243602210769244789727

theorem tailTrace_1327666 : CollatzResearch.WordTrace tailWord_1327666 prefixEnd_1327666 227243602210769244789727 := by
  unfold tailWord_1327666
  simp only [CollatzResearch.WordTrace]
  refine ⟨12105989302025076036408713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32282638138733536097089901 12105989302025076036408713)
  ·
    refine ⟨9079491976518807027306535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12105989302025076036408713 9079491976518807027306535)
    ·
      refine ⟨13619237964778210540959803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9079491976518807027306535 13619237964778210540959803)
      ·
        refine ⟨20428856947167315811439705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13619237964778210540959803 20428856947167315811439705)
        ·
          refine ⟨15321642710375486858579779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20428856947167315811439705 15321642710375486858579779)
          ·
            refine ⟨22982464065563230287869669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15321642710375486858579779 22982464065563230287869669)
            ·
              refine ⟨4309212012293105678975563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 22982464065563230287869669 4309212012293105678975563)
              ·
                refine ⟨6463818018439658518463345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4309212012293105678975563 6463818018439658518463345)
                ·
                  refine ⟨4847863513829743888847509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6463818018439658518463345 4847863513829743888847509)
                  ·
                    refine ⟨227243602210769244789727, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4847863513829743888847509 227243602210769244789727)
                    ·
                      rfl

theorem cell23_1327666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 4, 1, 2, 6].length) (baseStart_1327666 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1327666 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1327666 prefixEnd_1327666 := by exact prefixLift 1327666
  have htrace : WordTrace (prefixWord ++ tailWord_1327666) baseStart_1327666 baseEnd_1327666 := by
    simpa [prefixWord, tailWord_1327666, baseEnd_1327666] using wordTrace_append hprefix tailTrace_1327666
  have hstable : (prefixWord ++ tailWord_1327666).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1327666).length < 2 ^ (prefixWord ++ tailWord_1327666).sum := by decide
  have hdescent : baseEnd_1327666 < baseStart_1327666 := by decide
  rcases family_descends (prefixWord ++ tailWord_1327666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1327677 : List Nat := [1, 4, 1, 3, 2, 2, 2, 2, 1, 3, 2]
def baseStart_1327677 : Nat := 118140960795 + 1327677 * 2 ^ 59
def prefixEnd_1327677 : Nat := 4983230072969 + 3 ^ 40 * 1327677 * 2
def baseEnd_1327677 : Nat := 681736454919507191331631

theorem tailTrace_1327677 : CollatzResearch.WordTrace tailWord_1327677 prefixEnd_1327677 681736454919507191331631 := by
  unfold tailWord_1327677
  simp only [CollatzResearch.WordTrace]
  refine ⟨48424358411060453024285285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32282905607373635349523523 48424358411060453024285285)
  ·
    refine ⟨9079567202073834942053491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 48424358411060453024285285 9079567202073834942053491)
    ·
      refine ⟨13619350803110752413080237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9079567202073834942053491 13619350803110752413080237)
      ·
        refine ⟨5107256551166532154905089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13619350803110752413080237 5107256551166532154905089)
        ·
          refine ⟨3830442413374899116178817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5107256551166532154905089 3830442413374899116178817)
          ·
            refine ⟨2872831810031174337134113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3830442413374899116178817 2872831810031174337134113)
            ·
              refine ⟨2154623857523380752850585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2872831810031174337134113 2154623857523380752850585)
              ·
                refine ⟨1615967893142535564637939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2154623857523380752850585 1615967893142535564637939)
                ·
                  refine ⟨2423951839713803346956909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1615967893142535564637939 2423951839713803346956909)
                  ·
                    refine ⟨908981939892676255108841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2423951839713803346956909 908981939892676255108841)
                    ·
                      refine ⟨681736454919507191331631, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 908981939892676255108841 681736454919507191331631)
                      ·
                        rfl

theorem cell23_1327677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 2, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 2, 2, 2, 1, 3, 2].length) (baseStart_1327677 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1327677 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1327677 prefixEnd_1327677 := by exact prefixLift 1327677
  have htrace : WordTrace (prefixWord ++ tailWord_1327677) baseStart_1327677 baseEnd_1327677 := by
    simpa [prefixWord, tailWord_1327677, baseEnd_1327677] using wordTrace_append hprefix tailTrace_1327677
  have hstable : (prefixWord ++ tailWord_1327677).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1327677).length < 2 ^ (prefixWord ++ tailWord_1327677).sum := by decide
  have hdescent : baseEnd_1327677 < baseStart_1327677 := by decide
  rcases family_descends (prefixWord ++ tailWord_1327677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1327690 : List Nat := [3, 1, 2, 1, 1, 4, 1, 2, 4, 2, 2]
def baseStart_1327690 : Nat := 118140960795 + 1327690 * 2 ^ 59
def prefixEnd_1327690 : Nat := 4983230072969 + 3 ^ 40 * 1327690 * 2
def baseEnd_1327690 : Nat := 681743130168015640469071

theorem tailTrace_1327690 : CollatzResearch.WordTrace tailWord_1327690 prefixEnd_1327690 681743130168015640469071 := by
  unfold tailWord_1327690
  simp only [CollatzResearch.WordTrace]
  refine ⟨12106208140003339061127131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32283221706675570829672349 12106208140003339061127131)
  ·
    refine ⟨18159312210005008591690697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12106208140003339061127131 18159312210005008591690697)
    ·
      refine ⟨13619484157503756443768023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18159312210005008591690697 13619484157503756443768023)
      ·
        refine ⟨20429226236255634665652035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13619484157503756443768023 20429226236255634665652035)
        ·
          refine ⟨30643839354383451998478053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20429226236255634665652035 30643839354383451998478053)
          ·
            refine ⟨5745719878946897249714635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 30643839354383451998478053 5745719878946897249714635)
            ·
              refine ⟨8618579818420345874571953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5745719878946897249714635 8618579818420345874571953)
              ·
                refine ⟨6463934863815259405928965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8618579818420345874571953 6463934863815259405928965)
                ·
                  refine ⟨1211987786965361138611681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6463934863815259405928965 1211987786965361138611681)
                  ·
                    refine ⟨908990840224020853958761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1211987786965361138611681 908990840224020853958761)
                    ·
                      refine ⟨681743130168015640469071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 908990840224020853958761 681743130168015640469071)
                      ·
                        rfl

theorem cell23_1327690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 1, 2, 4, 2, 2].length) (baseStart_1327690 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1327690 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1327690 prefixEnd_1327690 := by exact prefixLift 1327690
  have htrace : WordTrace (prefixWord ++ tailWord_1327690) baseStart_1327690 baseEnd_1327690 := by
    simpa [prefixWord, tailWord_1327690, baseEnd_1327690] using wordTrace_append hprefix tailTrace_1327690
  have hstable : (prefixWord ++ tailWord_1327690).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1327690).length < 2 ^ (prefixWord ++ tailWord_1327690).sum := by decide
  have hdescent : baseEnd_1327690 < baseStart_1327690 := by decide
  rcases family_descends (prefixWord ++ tailWord_1327690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1327693 : List Nat := [1, 6, 1, 1, 2, 1, 1, 1, 1, 3, 5]
def baseStart_1327693 : Nat := 118140960795 + 1327693 * 2 ^ 59
def prefixEnd_1327693 : Nat := 4983230072969 + 3 ^ 40 * 1327693 * 2
def baseEnd_1327693 : Nat := 681744670609979128731557

theorem tailTrace_1327693 : CollatzResearch.WordTrace tailWord_1327693 prefixEnd_1327693 681744670609979128731557 := by
  unfold tailWord_1327693
  simp only [CollatzResearch.WordTrace]
  refine ⟨48424941979002487756867733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32283294652668325171245155 48424941979002487756867733)
  ·
    refine ⟨2269919155265741613603175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 48424941979002487756867733 2269919155265741613603175)
    ·
      refine ⟨3404878732898612420404763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2269919155265741613603175 3404878732898612420404763)
      ·
        refine ⟨5107318099347918630607145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3404878732898612420404763 5107318099347918630607145)
        ·
          refine ⟨3830488574510938972955359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5107318099347918630607145 3830488574510938972955359)
          ·
            refine ⟨5745732861766408459433039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3830488574510938972955359 5745732861766408459433039)
            ·
              refine ⟨8618599292649612689149559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5745732861766408459433039 8618599292649612689149559)
              ·
                refine ⟨12927898938974419033724339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8618599292649612689149559 12927898938974419033724339)
                ·
                  refine ⟨19391848408461628550586509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12927898938974419033724339 19391848408461628550586509)
                  ·
                    refine ⟨7271943153173110706469941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19391848408461628550586509 7271943153173110706469941)
                    ·
                      refine ⟨681744670609979128731557, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7271943153173110706469941 681744670609979128731557)
                      ·
                        rfl

theorem cell23_1327693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 1, 1, 1, 3, 5].length) (baseStart_1327693 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1327693 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1327693 prefixEnd_1327693 := by exact prefixLift 1327693
  have htrace : WordTrace (prefixWord ++ tailWord_1327693) baseStart_1327693 baseEnd_1327693 := by
    simpa [prefixWord, tailWord_1327693, baseEnd_1327693] using wordTrace_append hprefix tailTrace_1327693
  have hstable : (prefixWord ++ tailWord_1327693).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1327693).length < 2 ^ (prefixWord ++ tailWord_1327693).sum := by decide
  have hdescent : baseEnd_1327693 < baseStart_1327693 := by decide
  rcases family_descends (prefixWord ++ tailWord_1327693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1327713 : List Nat := [1, 2, 3, 1, 1, 6, 1, 1, 7]
def baseStart_1327713 : Nat := 118140960795 + 1327713 * 2 ^ 59
def prefixEnd_1327713 : Nat := 4983230072969 + 3 ^ 40 * 1327713 * 2
def baseEnd_1327713 : Nat := 75750548913674338942385

theorem tailTrace_1327713 : CollatzResearch.WordTrace tailWord_1327713 prefixEnd_1327713 75750548913674338942385 := by
  unfold tailWord_1327713
  simp only [CollatzResearch.WordTrace]
  refine ⟨48425671438930031172595793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32283780959286687448397195 48425671438930031172595793)
  ·
    refine ⟨36319253579197523379446845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48425671438930031172595793 36319253579197523379446845)
    ·
      refine ⟨13619720092199071267292567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 36319253579197523379446845 13619720092199071267292567)
      ·
        refine ⟨20429580138298606900938851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13619720092199071267292567 20429580138298606900938851)
        ·
          refine ⟨30644370207447910351408277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20429580138298606900938851 30644370207447910351408277)
          ·
            refine ⟨1436454853474120797722263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 30644370207447910351408277 1436454853474120797722263)
            ·
              refine ⟨2154682280211181196583395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1436454853474120797722263 2154682280211181196583395)
              ·
                refine ⟨3232023420316771794875093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2154682280211181196583395 3232023420316771794875093)
                ·
                  refine ⟨75750548913674338942385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3232023420316771794875093 75750548913674338942385)
                  ·
                    rfl

theorem cell23_1327713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 6, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 6, 1, 1, 7].length) (baseStart_1327713 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1327713 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1327713 prefixEnd_1327713 := by exact prefixLift 1327713
  have htrace : WordTrace (prefixWord ++ tailWord_1327713) baseStart_1327713 baseEnd_1327713 := by
    simpa [prefixWord, tailWord_1327713, baseEnd_1327713] using wordTrace_append hprefix tailTrace_1327713
  have hstable : (prefixWord ++ tailWord_1327713).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1327713).length < 2 ^ (prefixWord ++ tailWord_1327713).sum := by decide
  have hdescent : baseEnd_1327713 < baseStart_1327713 := by decide
  rcases family_descends (prefixWord ++ tailWord_1327713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1327763 : List Nat := [1, 1, 1, 2, 1, 2, 2, 3, 4, 4, 2]
def baseStart_1327763 : Nat := 118140960795 + 1327763 * 2 ^ 59
def prefixEnd_1327763 : Nat := 4983230072969 + 3 ^ 40 * 1327763 * 2
def baseEnd_1327763 : Nat := 681780614255793854856235

theorem tailTrace_1327763 : CollatzResearch.WordTrace tailWord_1327763 prefixEnd_1327763 681780614255793854856235 := by
  unfold tailWord_1327763
  simp only [CollatzResearch.WordTrace]
  refine ⟨48427495088748889711915943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32284996725832593141277295 48427495088748889711915943)
  ·
    refine ⟨72641242633123334567873915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48427495088748889711915943 72641242633123334567873915)
    ·
      refine ⟨108961863949685001851810873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72641242633123334567873915 108961863949685001851810873)
      ·
        refine ⟨81721397962263751388858155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 108961863949685001851810873 81721397962263751388858155)
        ·
          refine ⟨122582096943395627083287233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 81721397962263751388858155 122582096943395627083287233)
          ·
            refine ⟨91936572707546720312465425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 122582096943395627083287233 91936572707546720312465425)
            ·
              refine ⟨68952429530660040234349069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 91936572707546720312465425 68952429530660040234349069)
              ·
                refine ⟨25857161073997515087880901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 68952429530660040234349069 25857161073997515087880901)
                ·
                  refine ⟨4848217701374534078977669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 25857161073997515087880901 4848217701374534078977669)
                  ·
                    refine ⟨909040819007725139808313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4848217701374534078977669 909040819007725139808313)
                    ·
                      refine ⟨681780614255793854856235, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 909040819007725139808313 681780614255793854856235)
                      ·
                        rfl

theorem cell23_1327763_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 3, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 3, 4, 4, 2].length) (baseStart_1327763 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1327763 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1327763 prefixEnd_1327763 := by exact prefixLift 1327763
  have htrace : WordTrace (prefixWord ++ tailWord_1327763) baseStart_1327763 baseEnd_1327763 := by
    simpa [prefixWord, tailWord_1327763, baseEnd_1327763] using wordTrace_append hprefix tailTrace_1327763
  have hstable : (prefixWord ++ tailWord_1327763).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1327763).length < 2 ^ (prefixWord ++ tailWord_1327763).sum := by decide
  have hdescent : baseEnd_1327763 < baseStart_1327763 := by decide
  rcases family_descends (prefixWord ++ tailWord_1327763) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1327764 : List Nat := [2, 4, 2, 2, 1, 3, 2, 2, 5]
def baseStart_1327764 : Nat := 118140960795 + 1327764 * 2 ^ 59
def prefixEnd_1327764 : Nat := 4983230072969 + 3 ^ 40 * 1327764 * 2
def baseEnd_1327764 : Nat := 75753458637383150104859

theorem tailTrace_1327764 : CollatzResearch.WordTrace tailWord_1327764 prefixEnd_1327764 75753458637383150104859 := by
  unfold tailWord_1327764
  simp only [CollatzResearch.WordTrace]
  refine ⟨24213765780872633441351173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32285021041163511255134897 24213765780872633441351173)
  ·
    refine ⟨4540081083913618770253345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 24213765780872633441351173 4540081083913618770253345)
    ·
      refine ⟨3405060812935214077690009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4540081083913618770253345 3405060812935214077690009)
      ·
        refine ⟨2553795609701410558267507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3405060812935214077690009 2553795609701410558267507)
        ·
          refine ⟨3830693414552115837401261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2553795609701410558267507 3830693414552115837401261)
          ·
            refine ⟨1436510030457043439025473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3830693414552115837401261 1436510030457043439025473)
            ·
              refine ⟨1077382522842782579269105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1436510030457043439025473 1077382522842782579269105)
              ·
                refine ⟨808036892132086934451829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1077382522842782579269105 808036892132086934451829)
                ·
                  refine ⟨75753458637383150104859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 808036892132086934451829 75753458637383150104859)
                  ·
                    rfl

theorem cell23_1327764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 3, 2, 2, 5].length) (baseStart_1327764 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1327764 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1327764 prefixEnd_1327764 := by exact prefixLift 1327764
  have htrace : WordTrace (prefixWord ++ tailWord_1327764) baseStart_1327764 baseEnd_1327764 := by
    simpa [prefixWord, tailWord_1327764, baseEnd_1327764] using wordTrace_append hprefix tailTrace_1327764
  have hstable : (prefixWord ++ tailWord_1327764).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1327764).length < 2 ^ (prefixWord ++ tailWord_1327764).sum := by decide
  have hdescent : baseEnd_1327764 < baseStart_1327764 := by decide
  rcases family_descends (prefixWord ++ tailWord_1327764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1327780 : List Nat := [2, 3, 1, 2, 2, 1, 3, 1, 2, 4, 2]
def baseStart_1327780 : Nat := 118140960795 + 1327780 * 2 ^ 59
def prefixEnd_1327780 : Nat := 4983230072969 + 3 ^ 40 * 1327780 * 2
def baseEnd_1327780 : Nat := 681789343426920288343657

theorem tailTrace_1327780 : CollatzResearch.WordTrace tailWord_1327780 prefixEnd_1327780 681789343426920288343657 := by
  unfold tailWord_1327780
  simp only [CollatzResearch.WordTrace]
  refine ⟨24214057564843650807642397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32285410086458201076856529 24214057564843650807642397)
  ·
    refine ⟨9080271586816369052865899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24214057564843650807642397 9080271586816369052865899)
    ·
      refine ⟨13620407380224553579298849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9080271586816369052865899 13620407380224553579298849)
      ·
        refine ⟨10215305535168415184474137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13620407380224553579298849 10215305535168415184474137)
        ·
          refine ⟨7661479151376311388355603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10215305535168415184474137 7661479151376311388355603)
          ·
            refine ⟨11492218727064467082533405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7661479151376311388355603 11492218727064467082533405)
            ·
              refine ⟨4309582022649175155950027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11492218727064467082533405 4309582022649175155950027)
              ·
                refine ⟨6464373033973762733925041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4309582022649175155950027 6464373033973762733925041)
                ·
                  refine ⟨4848279775480322050443781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6464373033973762733925041 4848279775480322050443781)
                  ·
                    refine ⟨909052457902560384458209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4848279775480322050443781 909052457902560384458209)
                    ·
                      refine ⟨681789343426920288343657, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 909052457902560384458209 681789343426920288343657)
                      ·
                        rfl

theorem cell23_1327780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 3, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 3, 1, 2, 4, 2].length) (baseStart_1327780 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1327780 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1327780 prefixEnd_1327780 := by exact prefixLift 1327780
  have htrace : WordTrace (prefixWord ++ tailWord_1327780) baseStart_1327780 baseEnd_1327780 := by
    simpa [prefixWord, tailWord_1327780, baseEnd_1327780] using wordTrace_append hprefix tailTrace_1327780
  have hstable : (prefixWord ++ tailWord_1327780).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1327780).length < 2 ^ (prefixWord ++ tailWord_1327780).sum := by decide
  have hdescent : baseEnd_1327780 < baseStart_1327780 := by decide
  rcases family_descends (prefixWord ++ tailWord_1327780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1327797 : List Nat := [1, 3, 3, 3, 1, 3, 1, 1, 2, 1, 4]
def baseStart_1327797 : Nat := 118140960795 + 1327797 * 2 ^ 59
def prefixEnd_1327797 : Nat := 4983230072969 + 3 ^ 40 * 1327797 * 2
def baseEnd_1327797 : Nat := 681798072598046721831079

theorem tailTrace_1327797 : CollatzResearch.WordTrace tailWord_1327797 prefixEnd_1327797 681798072598046721831079 := by
  unfold tailWord_1327797
  simp only [CollatzResearch.WordTrace]
  refine ⟨48428735170625713518653645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32285823447083809012435763 48428735170625713518653645)
  ·
    refine ⟨18160775688984642569495117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 48428735170625713518653645 18160775688984642569495117)
    ·
      refine ⟨6810290883369240963560669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18160775688984642569495117 6810290883369240963560669)
      ·
        refine ⟨2553859081263465361335251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6810290883369240963560669 2553859081263465361335251)
        ·
          refine ⟨3830788621895198042002877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2553859081263465361335251 3830788621895198042002877)
          ·
            refine ⟨1436545733210699265751079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3830788621895198042002877 1436545733210699265751079)
            ·
              refine ⟨2154818599816048898626619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1436545733210699265751079 2154818599816048898626619)
              ·
                refine ⟨3232227899724073347939929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2154818599816048898626619 3232227899724073347939929)
                ·
                  refine ⟨2424170924793055010954947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3232227899724073347939929 2424170924793055010954947)
                  ·
                    refine ⟨3636256387189582516432421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2424170924793055010954947 3636256387189582516432421)
                    ·
                      refine ⟨681798072598046721831079, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3636256387189582516432421 681798072598046721831079)
                      ·
                        rfl

theorem cell23_1327797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 3, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 3, 1, 1, 2, 1, 4].length) (baseStart_1327797 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1327797 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1327797 prefixEnd_1327797 := by exact prefixLift 1327797
  have htrace : WordTrace (prefixWord ++ tailWord_1327797) baseStart_1327797 baseEnd_1327797 := by
    simpa [prefixWord, tailWord_1327797, baseEnd_1327797] using wordTrace_append hprefix tailTrace_1327797
  have hstable : (prefixWord ++ tailWord_1327797).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1327797).length < 2 ^ (prefixWord ++ tailWord_1327797).sum := by decide
  have hdescent : baseEnd_1327797 < baseStart_1327797 := by decide
  rcases family_descends (prefixWord ++ tailWord_1327797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1327807 : List Nat := [1, 1, 2, 2, 2, 5, 2, 3, 1, 4]
def baseStart_1327807 : Nat := 118140960795 + 1327807 * 2 ^ 59
def prefixEnd_1327807 : Nat := 4983230072969 + 3 ^ 40 * 1327807 * 2
def baseEnd_1327807 : Nat := 227267735801530560902011

theorem tailTrace_1327807 : CollatzResearch.WordTrace tailWord_1327807 prefixEnd_1327807 227267735801530560902011 := by
  unfold tailWord_1327807
  simp only [CollatzResearch.WordTrace]
  refine ⟨48429099900589485226517675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32286066600392990151011783 48429099900589485226517675)
  ·
    refine ⟨72643649850884227839776513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48429099900589485226517675 72643649850884227839776513)
    ·
      refine ⟨54482737388163170879832385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 72643649850884227839776513 54482737388163170879832385)
      ·
        refine ⟨40862053041122378159874289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54482737388163170879832385 40862053041122378159874289)
        ·
          refine ⟨30646539780841783619905717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40862053041122378159874289 30646539780841783619905717)
          ·
            refine ⟨2873113104453917214366161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 30646539780841783619905717 2873113104453917214366161)
            ·
              refine ⟨2154834828340437910774621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2873113104453917214366161 2154834828340437910774621)
              ·
                refine ⟨808063060627664216540483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2154834828340437910774621 808063060627664216540483)
                ·
                  refine ⟨1212094590941496324810725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 808063060627664216540483 1212094590941496324810725)
                  ·
                    refine ⟨227267735801530560902011, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1212094590941496324810725 227267735801530560902011)
                    ·
                      rfl

theorem cell23_1327807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 5, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 5, 2, 3, 1, 4].length) (baseStart_1327807 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1327807 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1327807 prefixEnd_1327807 := by exact prefixLift 1327807
  have htrace : WordTrace (prefixWord ++ tailWord_1327807) baseStart_1327807 baseEnd_1327807 := by
    simpa [prefixWord, tailWord_1327807, baseEnd_1327807] using wordTrace_append hprefix tailTrace_1327807
  have hstable : (prefixWord ++ tailWord_1327807).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1327807).length < 2 ^ (prefixWord ++ tailWord_1327807).sum := by decide
  have hdescent : baseEnd_1327807 < baseStart_1327807 := by decide
  rcases family_descends (prefixWord ++ tailWord_1327807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1327820 : List Nat := [2, 2, 1, 5, 1, 1, 3, 2, 6]
def baseStart_1327820 : Nat := 118140960795 + 1327820 * 2 ^ 59
def prefixEnd_1327820 : Nat := 4983230072969 + 3 ^ 40 * 1327820 * 2
def baseEnd_1327820 : Nat := 75756653628122236871497

theorem tailTrace_1327820 : CollatzResearch.WordTrace tailWord_1327820 prefixEnd_1327820 75756653628122236871497 := by
  unfold tailWord_1327820
  simp only [CollatzResearch.WordTrace]
  refine ⟨24214787024771194223370457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32286382699694925631160609 24214787024771194223370457)
  ·
    refine ⟨18161090268578395667527843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24214787024771194223370457 18161090268578395667527843)
    ·
      refine ⟨27241635402867593501291765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18161090268578395667527843 27241635402867593501291765)
      ·
        refine ⟨2553903319018836890746103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 27241635402867593501291765 2553903319018836890746103)
        ·
          refine ⟨3830854978528255336119155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2553903319018836890746103 3830854978528255336119155)
          ·
            refine ⟨5746282467792383004178733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3830854978528255336119155 5746282467792383004178733)
            ·
              refine ⟨2154855925422143626567025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5746282467792383004178733 2154855925422143626567025)
              ·
                refine ⟨1616141944066607719925269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2154855925422143626567025 1616141944066607719925269)
                ·
                  refine ⟨75756653628122236871497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1616141944066607719925269 75756653628122236871497)
                  ·
                    rfl

theorem cell23_1327820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 3, 2, 6].length) (baseStart_1327820 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1327820 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1327820 prefixEnd_1327820 := by exact prefixLift 1327820
  have htrace : WordTrace (prefixWord ++ tailWord_1327820) baseStart_1327820 baseEnd_1327820 := by
    simpa [prefixWord, tailWord_1327820, baseEnd_1327820] using wordTrace_append hprefix tailTrace_1327820
  have hstable : (prefixWord ++ tailWord_1327820).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1327820).length < 2 ^ (prefixWord ++ tailWord_1327820).sum := by decide
  have hdescent : baseEnd_1327820 < baseStart_1327820 := by decide
  rcases family_descends (prefixWord ++ tailWord_1327820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1327874 : List Nat := [3, 4, 1, 1, 1, 3, 1, 2, 2, 3, 2]
def baseStart_1327874 : Nat := 118140960795 + 1327874 * 2 ^ 59
def prefixEnd_1327874 : Nat := 4983230072969 + 3 ^ 40 * 1327874 * 2
def baseEnd_1327874 : Nat := 681837610608442920568225

theorem tailTrace_1327874 : CollatzResearch.WordTrace tailWord_1327874 prefixEnd_1327874 681837610608442920568225 := by
  unfold tailWord_1327874
  simp only [CollatzResearch.WordTrace]
  refine ⟨12107885897836688917301669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32287695727564503779471117 12107885897836688917301669)
  ·
    refine ⟨2270228605844379171994063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 12107885897836688917301669 2270228605844379171994063)
    ·
      refine ⟨3405342908766568757991095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2270228605844379171994063 3405342908766568757991095)
      ·
        refine ⟨5108014363149853136986643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3405342908766568757991095 5108014363149853136986643)
        ·
          refine ⟨7662021544724779705479965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5108014363149853136986643 7662021544724779705479965)
          ·
            refine ⟨2873258079271792389554987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7662021544724779705479965 2873258079271792389554987)
            ·
              refine ⟨4309887118907688584332481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2873258079271792389554987 4309887118907688584332481)
              ·
                refine ⟨3232415339180766438249361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4309887118907688584332481 3232415339180766438249361)
                ·
                  refine ⟨2424311504385574828687021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3232415339180766438249361 2424311504385574828687021)
                  ·
                    refine ⟨909116814144590560757633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2424311504385574828687021 909116814144590560757633)
                    ·
                      refine ⟨681837610608442920568225, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 909116814144590560757633 681837610608442920568225)
                      ·
                        rfl

theorem cell23_1327874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 3, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 3, 1, 2, 2, 3, 2].length) (baseStart_1327874 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1327874 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1327874 prefixEnd_1327874 := by exact prefixLift 1327874
  have htrace : WordTrace (prefixWord ++ tailWord_1327874) baseStart_1327874 baseEnd_1327874 := by
    simpa [prefixWord, tailWord_1327874, baseEnd_1327874] using wordTrace_append hprefix tailTrace_1327874
  have hstable : (prefixWord ++ tailWord_1327874).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1327874).length < 2 ^ (prefixWord ++ tailWord_1327874).sum := by decide
  have hdescent : baseEnd_1327874 < baseStart_1327874 := by decide
  rcases family_descends (prefixWord ++ tailWord_1327874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1327880 : List Nat := [2, 1, 3, 2, 2, 2, 2, 1, 4, 4]
def baseStart_1327880 : Nat := 118140960795 + 1327880 * 2 ^ 59
def prefixEnd_1327880 : Nat := 4983230072969 + 3 ^ 40 * 1327880 * 2
def baseEnd_1327880 : Nat := 227280230497456632364399

theorem tailTrace_1327880 : CollatzResearch.WordTrace tailWord_1327880 prefixEnd_1327880 227280230497456632364399 := by
  unfold tailWord_1327880
  simp only [CollatzResearch.WordTrace]
  refine ⟨24215881214662509346962547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32287841619550012462616729 24215881214662509346962547)
  ·
    refine ⟨36323821821993764020443821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24215881214662509346962547 36323821821993764020443821)
    ·
      refine ⟨13621433183247661507666433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 36323821821993764020443821 13621433183247661507666433)
      ·
        refine ⟨10216074887435746130749825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13621433183247661507666433 10216074887435746130749825)
        ·
          refine ⟨7662056165576809598062369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10216074887435746130749825 7662056165576809598062369)
          ·
            refine ⟨5746542124182607198546777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7662056165576809598062369 5746542124182607198546777)
            ·
              refine ⟨4309906593136955398910083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5746542124182607198546777 4309906593136955398910083)
              ·
                refine ⟨6464859889705433098365125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4309906593136955398910083 6464859889705433098365125)
                ·
                  refine ⟨1212161229319768705943461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6464859889705433098365125 1212161229319768705943461)
                  ·
                    refine ⟨227280230497456632364399, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1212161229319768705943461 227280230497456632364399)
                    ·
                      rfl

theorem cell23_1327880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 2, 1, 4, 4].length) (baseStart_1327880 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1327880 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1327880 prefixEnd_1327880 := by exact prefixLift 1327880
  have htrace : WordTrace (prefixWord ++ tailWord_1327880) baseStart_1327880 baseEnd_1327880 := by
    simpa [prefixWord, tailWord_1327880, baseEnd_1327880] using wordTrace_append hprefix tailTrace_1327880
  have hstable : (prefixWord ++ tailWord_1327880).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1327880).length < 2 ^ (prefixWord ++ tailWord_1327880).sum := by decide
  have hdescent : baseEnd_1327880 < baseStart_1327880 := by decide
  rcases family_descends (prefixWord ++ tailWord_1327880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1327893 : List Nat := [1, 3, 2, 1, 2, 2, 4, 8]
def baseStart_1327893 : Nat := 118140960795 + 1327893 * 2 ^ 59
def prefixEnd_1327893 : Nat := 4983230072969 + 3 ^ 40 * 1327893 * 2
def baseEnd_1327893 : Nat := 25253606175588086897431

theorem tailTrace_1327893 : CollatzResearch.WordTrace tailWord_1327893 prefixEnd_1327893 25253606175588086897431 := by
  unfold tailWord_1327893
  simp only [CollatzResearch.WordTrace]
  refine ⟨48432236578277921914148333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32288157718851947942765555 48432236578277921914148333)
  ·
    refine ⟨18162088716854220717805625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 48432236578277921914148333 18162088716854220717805625)
    ·
      refine ⟨13621566537640665538354219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18162088716854220717805625 13621566537640665538354219)
      ·
        refine ⟨20432349806460998307531329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13621566537640665538354219 20432349806460998307531329)
        ·
          refine ⟨15324262354845748730648497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20432349806460998307531329 15324262354845748730648497)
          ·
            refine ⟨11493196766134311547986373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15324262354845748730648497 11493196766134311547986373)
            ·
              refine ⟨2154974393650183415247445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11493196766134311547986373 2154974393650183415247445)
              ·
                refine ⟨25253606175588086897431, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 2154974393650183415247445 25253606175588086897431)
                ·
                  rfl

theorem cell23_1327893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 4, 8].length) (baseStart_1327893 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1327893 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1327893 prefixEnd_1327893 := by exact prefixLift 1327893
  have htrace : WordTrace (prefixWord ++ tailWord_1327893) baseStart_1327893 baseEnd_1327893 := by
    simpa [prefixWord, tailWord_1327893, baseEnd_1327893] using wordTrace_append hprefix tailTrace_1327893
  have hstable : (prefixWord ++ tailWord_1327893).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1327893).length < 2 ^ (prefixWord ++ tailWord_1327893).sum := by decide
  have hdescent : baseEnd_1327893 < baseStart_1327893 := by decide
  rcases family_descends (prefixWord ++ tailWord_1327893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1327901 : List Nat := [1, 4, 2, 4, 2, 1, 1, 2, 1, 5]
def baseStart_1327901 : Nat := 118140960795 + 1327901 * 2 ^ 59
def prefixEnd_1327901 : Nat := 4983230072969 + 3 ^ 40 * 1327901 * 2
def baseEnd_1327901 : Nat := 227283824862038104976867

theorem tailTrace_1327901 : CollatzResearch.WordTrace tailWord_1327901 prefixEnd_1327901 227283824862038104976867 := by
  unfold tailWord_1327901
  simp only [CollatzResearch.WordTrace]
  refine ⟨48432528362248939280439557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32288352241499292853626371 48432528362248939280439557)
  ·
    refine ⟨9081099067921676115082417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 48432528362248939280439557 9081099067921676115082417)
    ·
      refine ⟨6810824300941257086311813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9081099067921676115082417 6810824300941257086311813)
      ·
        refine ⟨1277029556426485703683465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6810824300941257086311813 1277029556426485703683465)
        ·
          refine ⟨957772167319864277762599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1277029556426485703683465 957772167319864277762599)
          ·
            refine ⟨1436658250979796416643899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 957772167319864277762599 1436658250979796416643899)
            ·
              refine ⟨2154987376469694624965849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1436658250979796416643899 2154987376469694624965849)
              ·
                refine ⟨1616240532352270968724387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2154987376469694624965849 1616240532352270968724387)
                ·
                  refine ⟨2424360798528406453086581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1616240532352270968724387 2424360798528406453086581)
                  ·
                    refine ⟨227283824862038104976867, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2424360798528406453086581 227283824862038104976867)
                    ·
                      rfl

theorem cell23_1327901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 2, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 2, 1, 1, 2, 1, 5].length) (baseStart_1327901 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1327901 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1327901 prefixEnd_1327901 := by exact prefixLift 1327901
  have htrace : WordTrace (prefixWord ++ tailWord_1327901) baseStart_1327901 baseEnd_1327901 := by
    simpa [prefixWord, tailWord_1327901, baseEnd_1327901] using wordTrace_append hprefix tailTrace_1327901
  have hstable : (prefixWord ++ tailWord_1327901).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1327901).length < 2 ^ (prefixWord ++ tailWord_1327901).sum := by decide
  have hdescent : baseEnd_1327901 < baseStart_1327901 := by decide
  rcases family_descends (prefixWord ++ tailWord_1327901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1327920 : List Nat := [2, 1, 1, 1, 2, 2, 1, 3, 6, 1, 3]
def baseStart_1327920 : Nat := 118140960795 + 1327920 * 2 ^ 59
def prefixEnd_1327920 : Nat := 4983230072969 + 3 ^ 40 * 1327920 * 2
def baseEnd_1327920 : Nat := 681861230718549740593013

theorem tailTrace_1327920 : CollatzResearch.WordTrace tailWord_1327920 prefixEnd_1327920 681861230718549740593013 := by
  unfold tailWord_1327920
  simp only [CollatzResearch.WordTrace]
  refine ⟨24216610674590052762690607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32288814232786737016920809 24216610674590052762690607)
  ·
    refine ⟨36324916011885079144035911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24216610674590052762690607 36324916011885079144035911)
    ·
      refine ⟨54487374017827618716053867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36324916011885079144035911 54487374017827618716053867)
      ·
        refine ⟨81731061026741428074080801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54487374017827618716053867 81731061026741428074080801)
        ·
          refine ⟨61298295770056071055560601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 81731061026741428074080801 61298295770056071055560601)
          ·
            refine ⟨45973721827542053291670451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 61298295770056071055560601 45973721827542053291670451)
            ·
              refine ⟨68960582741313079937505677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45973721827542053291670451 68960582741313079937505677)
              ·
                refine ⟨25860218527992404976564629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 68960582741313079937505677 25860218527992404976564629)
                ·
                  refine ⟨1212197743499643983276467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 25860218527992404976564629 1212197743499643983276467)
                  ·
                    refine ⟨1818296615249465974914701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1212197743499643983276467 1818296615249465974914701)
                    ·
                      refine ⟨681861230718549740593013, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1818296615249465974914701 681861230718549740593013)
                      ·
                        rfl

theorem cell23_1327920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 3, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 3, 6, 1, 3].length) (baseStart_1327920 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1327920 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1327920 prefixEnd_1327920 := by exact prefixLift 1327920
  have htrace : WordTrace (prefixWord ++ tailWord_1327920) baseStart_1327920 baseEnd_1327920 := by
    simpa [prefixWord, tailWord_1327920, baseEnd_1327920] using wordTrace_append hprefix tailTrace_1327920
  have hstable : (prefixWord ++ tailWord_1327920).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1327920).length < 2 ^ (prefixWord ++ tailWord_1327920).sum := by decide
  have hdescent : baseEnd_1327920 < baseStart_1327920 := by decide
  rcases family_descends (prefixWord ++ tailWord_1327920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1327924 : List Nat := [2, 5, 1, 1, 3, 2, 1, 1, 1, 1, 5]
def baseStart_1327924 : Nat := 118140960795 + 1327924 * 2 ^ 59
def prefixEnd_1327924 : Nat := 4983230072969 + 3 ^ 40 * 1327924 * 2
def baseEnd_1327924 : Nat := 681863284641167724942995

theorem tailTrace_1327924 : CollatzResearch.WordTrace tailWord_1327924 prefixEnd_1327924 681863284641167724942995 := by
  unfold tailWord_1327924
  simp only [CollatzResearch.WordTrace]
  refine ⟨24216683620582807104263413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32288911494110409472351217 24216683620582807104263413)
  ·
    refine ⟨2270314089429638166024695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 24216683620582807104263413 2270314089429638166024695)
    ·
      refine ⟨3405471134144457249037043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2270314089429638166024695 3405471134144457249037043)
      ·
        refine ⟨5108206701216685873555565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3405471134144457249037043 5108206701216685873555565)
        ·
          refine ⟨1915577512956257202583337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5108206701216685873555565 1915577512956257202583337)
          ·
            refine ⟨1436683134717192901937503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1915577512956257202583337 1436683134717192901937503)
            ·
              refine ⟨2155024702075789352906255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1436683134717192901937503 2155024702075789352906255)
              ·
                refine ⟨3232537053113684029359383, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2155024702075789352906255 3232537053113684029359383)
                ·
                  refine ⟨4848805579670526044039075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3232537053113684029359383 4848805579670526044039075)
                  ·
                    refine ⟨7273208369505789066058613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4848805579670526044039075 7273208369505789066058613)
                    ·
                      refine ⟨681863284641167724942995, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7273208369505789066058613 681863284641167724942995)
                      ·
                        rfl

theorem cell23_1327924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 3, 2, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 3, 2, 1, 1, 1, 1, 5].length) (baseStart_1327924 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1327924 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1327924 prefixEnd_1327924 := by exact prefixLift 1327924
  have htrace : WordTrace (prefixWord ++ tailWord_1327924) baseStart_1327924 baseEnd_1327924 := by
    simpa [prefixWord, tailWord_1327924, baseEnd_1327924] using wordTrace_append hprefix tailTrace_1327924
  have hstable : (prefixWord ++ tailWord_1327924).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1327924).length < 2 ^ (prefixWord ++ tailWord_1327924).sum := by decide
  have hdescent : baseEnd_1327924 < baseStart_1327924 := by decide
  rcases family_descends (prefixWord ++ tailWord_1327924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1327964 : List Nat := [2, 2, 4, 2, 1, 1, 2, 1, 3, 3, 2]
def baseStart_1327964 : Nat := 118140960795 + 1327964 * 2 ^ 59
def prefixEnd_1327964 : Nat := 4983230072969 + 3 ^ 40 * 1327964 * 2
def baseEnd_1327964 : Nat := 681883823867347568442811

theorem tailTrace_1327964 : CollatzResearch.WordTrace tailWord_1327964 prefixEnd_1327964 681883823867347568442811 := by
  unfold tailWord_1327964
  simp only [CollatzResearch.WordTrace]
  refine ⟨24217413080510350519991473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32289884107347134026655297 24217413080510350519991473)
  ·
    refine ⟨18163059810382762889993605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24217413080510350519991473 18163059810382762889993605)
    ·
      refine ⟨3405573714446768041873801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 18163059810382762889993605 3405573714446768041873801)
      ·
        refine ⟨2554180285835076031405351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3405573714446768041873801 2554180285835076031405351)
        ·
          refine ⟨3831270428752614047108027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2554180285835076031405351 3831270428752614047108027)
          ·
            refine ⟨5746905643128921070662041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3831270428752614047108027 5746905643128921070662041)
            ·
              refine ⟨4310179232346690802996531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5746905643128921070662041 4310179232346690802996531)
              ·
                refine ⟨6465268848520036204494797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4310179232346690802996531 6465268848520036204494797)
                ·
                  refine ⟨2424475818195013576685549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6465268848520036204494797 2424475818195013576685549)
                  ·
                    refine ⟨909178431823130091257081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2424475818195013576685549 909178431823130091257081)
                    ·
                      refine ⟨681883823867347568442811, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 909178431823130091257081 681883823867347568442811)
                      ·
                        rfl

theorem cell23_1327964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 2, 1, 3, 3, 2].length) (baseStart_1327964 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1327964 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1327964 prefixEnd_1327964 := by exact prefixLift 1327964
  have htrace : WordTrace (prefixWord ++ tailWord_1327964) baseStart_1327964 baseEnd_1327964 := by
    simpa [prefixWord, tailWord_1327964, baseEnd_1327964] using wordTrace_append hprefix tailTrace_1327964
  have hstable : (prefixWord ++ tailWord_1327964).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1327964).length < 2 ^ (prefixWord ++ tailWord_1327964).sum := by decide
  have hdescent : baseEnd_1327964 < baseStart_1327964 := by decide
  rcases family_descends (prefixWord ++ tailWord_1327964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1328034 : List Nat := [3, 3, 1, 2, 2, 1, 3, 3, 5]
def baseStart_1328034 : Nat := 118140960795 + 1328034 * 2 ^ 59
def prefixEnd_1328034 : Nat := 4983230072969 + 3 ^ 40 * 1328034 * 2
def baseEnd_1328034 : Nat := 75768863057018032729721

theorem tailTrace_1328034 : CollatzResearch.WordTrace tailWord_1328034 prefixEnd_1328034 75768863057018032729721 := by
  unfold tailWord_1328034
  simp only [CollatzResearch.WordTrace]
  refine ⟨12109344817691775748757789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32291586180511401996687437 12109344817691775748757789)
  ·
    refine ⟨4541004306634415905784171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12109344817691775748757789 4541004306634415905784171)
    ·
      refine ⟨6811506459951623858676257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4541004306634415905784171 6811506459951623858676257)
      ·
        refine ⟨5108629844963717894007193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6811506459951623858676257 5108629844963717894007193)
        ·
          refine ⟨3831472383722788420505395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5108629844963717894007193 3831472383722788420505395)
          ·
            refine ⟨5747208575584182630758093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3831472383722788420505395 5747208575584182630758093)
            ·
              refine ⟨2155203215844068486534285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5747208575584182630758093 2155203215844068486534285)
              ·
                refine ⟨808201205941525682450357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2155203215844068486534285 808201205941525682450357)
                ·
                  refine ⟨75768863057018032729721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 808201205941525682450357 75768863057018032729721)
                  ·
                    rfl

theorem cell23_1328034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 3, 3, 5].length) (baseStart_1328034 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1328034 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1328034 prefixEnd_1328034 := by exact prefixLift 1328034
  have htrace : WordTrace (prefixWord ++ tailWord_1328034) baseStart_1328034 baseEnd_1328034 := by
    simpa [prefixWord, tailWord_1328034, baseEnd_1328034] using wordTrace_append hprefix tailTrace_1328034
  have hstable : (prefixWord ++ tailWord_1328034).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1328034).length < 2 ^ (prefixWord ++ tailWord_1328034).sum := by decide
  have hdescent : baseEnd_1328034 < baseStart_1328034 := by decide
  rcases family_descends (prefixWord ++ tailWord_1328034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1328043 : List Nat := [1, 1, 1, 1, 2, 1, 1, 4, 1, 10]
def baseStart_1328043 : Nat := 118140960795 + 1328043 * 2 ^ 59
def prefixEnd_1328043 : Nat := 4983230072969 + 3 ^ 40 * 1328043 * 2
def baseEnd_1328043 : Nat := 227308129613017586451649

theorem tailTrace_1328043 : CollatzResearch.WordTrace tailWord_1328043 prefixEnd_1328043 227308129613017586451649 := by
  unfold tailWord_1328043
  simp only [CollatzResearch.WordTrace]
  refine ⟨48437707527734497532108783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32291805018489665021405855 48437707527734497532108783)
  ·
    refine ⟨72656561291601746298163175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48437707527734497532108783 72656561291601746298163175)
    ·
      refine ⟨108984841937402619447244763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72656561291601746298163175 108984841937402619447244763)
      ·
        refine ⟨163477262906103929170867145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 108984841937402619447244763 163477262906103929170867145)
        ·
          refine ⟨122607947179577946878150359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 163477262906103929170867145 122607947179577946878150359)
          ·
            refine ⟨183911920769366920317225539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 122607947179577946878150359 183911920769366920317225539)
            ·
              refine ⟨275867881154050380475838309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 183911920769366920317225539 275867881154050380475838309)
              ·
                refine ⟨51725227716384446339219683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 275867881154050380475838309 51725227716384446339219683)
                ·
                  refine ⟨77587841574576669508829525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 51725227716384446339219683 77587841574576669508829525)
                  ·
                    refine ⟨227308129613017586451649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 77587841574576669508829525 227308129613017586451649)
                    ·
                      rfl

theorem cell23_1328043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 4, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 4, 1, 10].length) (baseStart_1328043 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1328043 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1328043 prefixEnd_1328043 := by exact prefixLift 1328043
  have htrace : WordTrace (prefixWord ++ tailWord_1328043) baseStart_1328043 baseEnd_1328043 := by
    simpa [prefixWord, tailWord_1328043, baseEnd_1328043] using wordTrace_append hprefix tailTrace_1328043
  have hstable : (prefixWord ++ tailWord_1328043).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1328043).length < 2 ^ (prefixWord ++ tailWord_1328043).sum := by decide
  have hdescent : baseEnd_1328043 < baseStart_1328043 := by decide
  rcases family_descends (prefixWord ++ tailWord_1328043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1328084 : List Nat := [2, 4, 1, 2, 1, 3, 2, 1, 2, 1, 4]
def baseStart_1328084 : Nat := 118140960795 + 1328084 * 2 ^ 59
def prefixEnd_1328084 : Nat := 4983230072969 + 3 ^ 40 * 1328084 * 2
def baseEnd_1328084 : Nat := 681945441545887098942259

theorem tailTrace_1328084 : CollatzResearch.WordTrace tailWord_1328084 prefixEnd_1328084 681945441545887098942259 := by
  unfold tailWord_1328084
  simp only [CollatzResearch.WordTrace]
  refine ⟨24219601460292980767175653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32292801947057307689567537 24219601460292980767175653)
  ·
    refine ⟨4541175273804933893845435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 24219601460292980767175653 4541175273804933893845435)
    ·
      refine ⟨6811762910707400840768153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4541175273804933893845435 6811762910707400840768153)
      ·
        refine ⟨5108822183030550630576115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6811762910707400840768153 5108822183030550630576115)
        ·
          refine ⟨7663233274545825945864173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5108822183030550630576115 7663233274545825945864173)
          ·
            refine ⟨2873712477954684729699065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7663233274545825945864173 2873712477954684729699065)
            ·
              refine ⟨2155284358466013547274299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2873712477954684729699065 2155284358466013547274299)
              ·
                refine ⟨3232926537699020320911449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2155284358466013547274299 3232926537699020320911449)
                ·
                  refine ⟨2424694903274265240683587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3232926537699020320911449 2424694903274265240683587)
                  ·
                    refine ⟨3637042354911397861025381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2424694903274265240683587 3637042354911397861025381)
                    ·
                      refine ⟨681945441545887098942259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3637042354911397861025381 681945441545887098942259)
                      ·
                        rfl

theorem cell23_1328084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 3, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 3, 2, 1, 2, 1, 4].length) (baseStart_1328084 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1328084 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1328084 prefixEnd_1328084 := by exact prefixLift 1328084
  have htrace : WordTrace (prefixWord ++ tailWord_1328084) baseStart_1328084 baseEnd_1328084 := by
    simpa [prefixWord, tailWord_1328084, baseEnd_1328084] using wordTrace_append hprefix tailTrace_1328084
  have hstable : (prefixWord ++ tailWord_1328084).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1328084).length < 2 ^ (prefixWord ++ tailWord_1328084).sum := by decide
  have hdescent : baseEnd_1328084 < baseStart_1328084 := by decide
  rcases family_descends (prefixWord ++ tailWord_1328084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1328111 : List Nat := [1, 1, 2, 1, 4, 3, 4, 2, 1, 4]
def baseStart_1328111 : Nat := 118140960795 + 1328111 * 2 ^ 59
def prefixEnd_1328111 : Nat := 4983230072969 + 3 ^ 40 * 1328111 * 2
def baseEnd_1328111 : Nat := 227319768507852831101545

theorem tailTrace_1328111 : CollatzResearch.WordTrace tailWord_1328111 prefixEnd_1328111 227319768507852831101545 := by
  unfold tailWord_1328111
  simp only [CollatzResearch.WordTrace]
  refine ⟨48440187691488145145584187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32293458460992096763722791 48440187691488145145584187)
  ·
    refine ⟨72660281537232217718376281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48440187691488145145584187 72660281537232217718376281)
    ·
      refine ⟨54495211152924163288782211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 72660281537232217718376281 54495211152924163288782211)
      ·
        refine ⟨81742816729386244933173317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54495211152924163288782211 81742816729386244933173317)
        ·
          refine ⟨15326778136759920924969997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 81742816729386244933173317 15326778136759920924969997)
          ·
            refine ⟨5747541801284970346863749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15326778136759920924969997 5747541801284970346863749)
            ·
              refine ⟨1077664087740931940036953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5747541801284970346863749 1077664087740931940036953)
              ·
                refine ⟨808248065805698955027715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1077664087740931940036953 808248065805698955027715)
                ·
                  refine ⟨1212372098708548432541573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 808248065805698955027715 1212372098708548432541573)
                  ·
                    refine ⟨227319768507852831101545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1212372098708548432541573 227319768507852831101545)
                    ·
                      rfl

theorem cell23_1328111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 4, 2, 1, 4].length) (baseStart_1328111 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1328111 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1328111 prefixEnd_1328111 := by exact prefixLift 1328111
  have htrace : WordTrace (prefixWord ++ tailWord_1328111) baseStart_1328111 baseEnd_1328111 := by
    simpa [prefixWord, tailWord_1328111, baseEnd_1328111] using wordTrace_append hprefix tailTrace_1328111
  have hstable : (prefixWord ++ tailWord_1328111).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1328111).length < 2 ^ (prefixWord ++ tailWord_1328111).sum := by decide
  have hdescent : baseEnd_1328111 < baseStart_1328111 := by decide
  rcases family_descends (prefixWord ++ tailWord_1328111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1328177 : List Nat := [1, 2, 2, 3, 1, 2, 3, 2, 1, 1, 5]
def baseStart_1328177 : Nat := 118140960795 + 1328177 * 2 ^ 59
def prefixEnd_1328177 : Nat := 4983230072969 + 3 ^ 40 * 1328177 * 2
def baseEnd_1328177 : Nat := 681993195246755235079331

theorem tailTrace_1328177 : CollatzResearch.WordTrace tailWord_1328177 prefixEnd_1328177 681993195246755235079331 := by
  unfold tailWord_1328177
  simp only [CollatzResearch.WordTrace]
  refine ⟨48442594909249038417486785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32295063272832692278324523 48442594909249038417486785)
  ·
    refine ⟨36331946181936778813115089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48442594909249038417486785 36331946181936778813115089)
    ·
      refine ⟨27248959636452584109836317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36331946181936778813115089 27248959636452584109836317)
      ·
        refine ⟨10218359863669719041188619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27248959636452584109836317 10218359863669719041188619)
        ·
          refine ⟨15327539795504578561782929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10218359863669719041188619 15327539795504578561782929)
          ·
            refine ⟨11495654846628433921337197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15327539795504578561782929 11495654846628433921337197)
            ·
              refine ⟨4310870567485662720501449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11495654846628433921337197 4310870567485662720501449)
              ·
                refine ⟨3233152925614247040376087, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4310870567485662720501449 3233152925614247040376087)
                ·
                  refine ⟨4849729388421370560564131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3233152925614247040376087 4849729388421370560564131)
                  ·
                    refine ⟨7274594082632055840846197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4849729388421370560564131 7274594082632055840846197)
                    ·
                      refine ⟨681993195246755235079331, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7274594082632055840846197 681993195246755235079331)
                      ·
                        rfl

theorem cell23_1328177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 3, 2, 1, 1, 5].length) (baseStart_1328177 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1328177 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1328177 prefixEnd_1328177 := by exact prefixLift 1328177
  have htrace : WordTrace (prefixWord ++ tailWord_1328177) baseStart_1328177 baseEnd_1328177 := by
    simpa [prefixWord, tailWord_1328177, baseEnd_1328177] using wordTrace_append hprefix tailTrace_1328177
  have hstable : (prefixWord ++ tailWord_1328177).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1328177).length < 2 ^ (prefixWord ++ tailWord_1328177).sum := by decide
  have hdescent : baseEnd_1328177 < baseStart_1328177 := by decide
  rcases family_descends (prefixWord ++ tailWord_1328177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1328184 : List Nat := [2, 1, 2, 1, 5, 3, 1, 1, 1, 6]
def baseStart_1328184 : Nat := 118140960795 + 1328184 * 2 ^ 59
def prefixEnd_1328184 : Nat := 4983230072969 + 3 ^ 40 * 1328184 * 2
def baseEnd_1328184 : Nat := 227332263203778902563933

theorem tailTrace_1328184 : CollatzResearch.WordTrace tailWord_1328184 prefixEnd_1328184 227332263203778902563933 := by
  unfold tailWord_1328184
  simp only [CollatzResearch.WordTrace]
  refine ⟨24221425110111839306495803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32295233480149119075327737 24221425110111839306495803)
  ·
    refine ⟨36332137665167758959743705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24221425110111839306495803 36332137665167758959743705)
    ·
      refine ⟨27249103248875819219807779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36332137665167758959743705 27249103248875819219807779)
      ·
        refine ⟨40873654873313728829711669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27249103248875819219807779 40873654873313728829711669)
        ·
          refine ⟨3831905144373162077785469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 40873654873313728829711669 3831905144373162077785469)
          ·
            refine ⟨1436964429139935779169551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3831905144373162077785469 1436964429139935779169551)
            ·
              refine ⟨2155446643709903668754327, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1436964429139935779169551 2155446643709903668754327)
              ·
                refine ⟨3233169965564855503131491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2155446643709903668754327 3233169965564855503131491)
                ·
                  refine ⟨4849754948347283254697237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3233169965564855503131491 4849754948347283254697237)
                  ·
                    refine ⟨227332263203778902563933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4849754948347283254697237 227332263203778902563933)
                    ·
                      rfl

theorem cell23_1328184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 3, 1, 1, 1, 6].length) (baseStart_1328184 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1328184 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1328184 prefixEnd_1328184 := by exact prefixLift 1328184
  have htrace : WordTrace (prefixWord ++ tailWord_1328184) baseStart_1328184 baseEnd_1328184 := by
    simpa [prefixWord, tailWord_1328184, baseEnd_1328184] using wordTrace_append hprefix tailTrace_1328184
  have hstable : (prefixWord ++ tailWord_1328184).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1328184).length < 2 ^ (prefixWord ++ tailWord_1328184).sum := by decide
  have hdescent : baseEnd_1328184 < baseStart_1328184 := by decide
  rcases family_descends (prefixWord ++ tailWord_1328184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1328197 : List Nat := [1, 3, 1, 1, 1, 3, 6, 7]
def baseStart_1328197 : Nat := 118140960795 + 1328197 * 2 ^ 59
def prefixEnd_1328197 : Nat := 4983230072969 + 3 ^ 40 * 1328197 * 2
def baseEnd_1328197 : Nat := 25259387587401672475157

theorem tailTrace_1328197 : CollatzResearch.WordTrace tailWord_1328197 prefixEnd_1328197 25259387587401672475157 := by
  unfold tailWord_1328197
  simp only [CollatzResearch.WordTrace]
  refine ⟨48443324369176581833214845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32295549579451054555476563 48443324369176581833214845)
  ·
    refine ⟨18166246638441218187455567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 48443324369176581833214845 18166246638441218187455567)
    ·
      refine ⟨27249369957661827281183351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18166246638441218187455567 27249369957661827281183351)
      ·
        refine ⟨40874054936492740921775027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27249369957661827281183351 40874054936492740921775027)
        ·
          refine ⟨61311082404739111382662541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40874054936492740921775027 61311082404739111382662541)
          ·
            refine ⟨22991655901777166768498453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 61311082404739111382662541 22991655901777166768498453)
            ·
              refine ⟨1077733870395804692273365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 22991655901777166768498453 1077733870395804692273365)
              ·
                refine ⟨25259387587401672475157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1077733870395804692273365 25259387587401672475157)
                ·
                  rfl

theorem cell23_1328197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 6, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 6, 7].length) (baseStart_1328197 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1328197 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1328197 prefixEnd_1328197 := by exact prefixLift 1328197
  have htrace : WordTrace (prefixWord ++ tailWord_1328197) baseStart_1328197 baseEnd_1328197 := by
    simpa [prefixWord, tailWord_1328197, baseEnd_1328197] using wordTrace_append hprefix tailTrace_1328197
  have hstable : (prefixWord ++ tailWord_1328197).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1328197).length < 2 ^ (prefixWord ++ tailWord_1328197).sum := by decide
  have hdescent : baseEnd_1328197 < baseStart_1328197 := by decide
  rcases family_descends (prefixWord ++ tailWord_1328197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1328224 : List Nat := [2, 1, 1, 3, 2, 2, 1, 3, 4, 1, 3]
def baseStart_1328224 : Nat := 118140960795 + 1328224 * 2 ^ 59
def prefixEnd_1328224 : Nat := 4983230072969 + 3 ^ 40 * 1328224 * 2
def baseEnd_1328224 : Nat := 682017328837516551191615

theorem tailTrace_1328224 : CollatzResearch.WordTrace tailWord_1328224 prefixEnd_1328224 682017328837516551191615 := by
  unfold tailWord_1328224
  simp only [CollatzResearch.WordTrace]
  refine ⟨24222154570039382722223863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32296206093385843629631817 24222154570039382722223863)
  ·
    refine ⟨36333231855059074083335795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24222154570039382722223863 36333231855059074083335795)
    ·
      refine ⟨54499847782588611125003693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36333231855059074083335795 54499847782588611125003693)
      ·
        refine ⟨20437442918470729171876385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 54499847782588611125003693 20437442918470729171876385)
        ·
          refine ⟨15328082188853046878907289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20437442918470729171876385 15328082188853046878907289)
          ·
            refine ⟨11496061641639785159180467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15328082188853046878907289 11496061641639785159180467)
            ·
              refine ⟨17244092462459677738770701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11496061641639785159180467 17244092462459677738770701)
              ·
                refine ⟨6466534673422379152039013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17244092462459677738770701 6466534673422379152039013)
                ·
                  refine ⟨1212475251266696091007315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6466534673422379152039013 1212475251266696091007315)
                  ·
                    refine ⟨1818712876900044136510973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1212475251266696091007315 1818712876900044136510973)
                    ·
                      refine ⟨682017328837516551191615, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1818712876900044136510973 682017328837516551191615)
                      ·
                        rfl

theorem cell23_1328224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 1, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 1, 3, 4, 1, 3].length) (baseStart_1328224 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1328224 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1328224 prefixEnd_1328224 := by exact prefixLift 1328224
  have htrace : WordTrace (prefixWord ++ tailWord_1328224) baseStart_1328224 baseEnd_1328224 := by
    simpa [prefixWord, tailWord_1328224, baseEnd_1328224] using wordTrace_append hprefix tailTrace_1328224
  have hstable : (prefixWord ++ tailWord_1328224).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1328224).length < 2 ^ (prefixWord ++ tailWord_1328224).sum := by decide
  have hdescent : baseEnd_1328224 < baseStart_1328224 := by decide
  rcases family_descends (prefixWord ++ tailWord_1328224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1328245 : List Nat := [1, 3, 4, 3, 1, 2, 1, 2, 1, 2, 3]
def baseStart_1328245 : Nat := 118140960795 + 1328245 * 2 ^ 59
def prefixEnd_1328245 : Nat := 4983230072969 + 3 ^ 40 * 1328245 * 2
def baseEnd_1328245 : Nat := 682028111931260969029019

theorem tailTrace_1328245 : CollatzResearch.WordTrace tailWord_1328245 prefixEnd_1328245 682028111931260969029019 := by
  unfold tailWord_1328245
  simp only [CollatzResearch.WordTrace]
  refine ⟨48445075073002686030962189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32296716715335124020641459 48445075073002686030962189)
  ·
    refine ⟨18166903152376007261610821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 48445075073002686030962189 18166903152376007261610821)
    ·
      refine ⟨3406294341070501361552029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 18166903152376007261610821 3406294341070501361552029)
      ·
        refine ⟨1277360377901438010582011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3406294341070501361552029 1277360377901438010582011)
        ·
          refine ⟨1916040566852157015873017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1277360377901438010582011 1916040566852157015873017)
          ·
            refine ⟨1437030425139117761904763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1916040566852157015873017 1437030425139117761904763)
            ·
              refine ⟨2155545637708676642857145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1437030425139117761904763 2155545637708676642857145)
              ·
                refine ⟨1616659228281507482142859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2155545637708676642857145 1616659228281507482142859)
                ·
                  refine ⟨2424988842422261223214289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1616659228281507482142859 2424988842422261223214289)
                  ·
                    refine ⟨1818741631816695917410717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2424988842422261223214289 1818741631816695917410717)
                    ·
                      refine ⟨682028111931260969029019, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1818741631816695917410717 682028111931260969029019)
                      ·
                        rfl

theorem cell23_1328245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 1, 2, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 1, 2, 1, 2, 1, 2, 3].length) (baseStart_1328245 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1328245 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1328245 prefixEnd_1328245 := by exact prefixLift 1328245
  have htrace : WordTrace (prefixWord ++ tailWord_1328245) baseStart_1328245 baseEnd_1328245 := by
    simpa [prefixWord, tailWord_1328245, baseEnd_1328245] using wordTrace_append hprefix tailTrace_1328245
  have hstable : (prefixWord ++ tailWord_1328245).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1328245).length < 2 ^ (prefixWord ++ tailWord_1328245).sum := by decide
  have hdescent : baseEnd_1328245 < baseStart_1328245 := by decide
  rcases family_descends (prefixWord ++ tailWord_1328245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1328267 : List Nat := [1, 1, 1, 1, 4, 1, 1, 2, 4, 4, 3]
def baseStart_1328267 : Nat := 118140960795 + 1328267 * 2 ^ 59
def prefixEnd_1328267 : Nat := 4983230072969 + 3 ^ 40 * 1328267 * 2
def baseEnd_1328267 : Nat := 682039408505659882953917

theorem tailTrace_1328267 : CollatzResearch.WordTrace tailWord_1328267 prefixEnd_1328267 682039408505659882953917 := by
  unfold tailWord_1328267
  simp only [CollatzResearch.WordTrace]
  refine ⟨48445877478922983788263055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32297251652615322525508703 48445877478922983788263055)
  ·
    refine ⟨72668816218384475682394583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48445877478922983788263055 72668816218384475682394583)
    ·
      refine ⟨109003224327576713523591875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72668816218384475682394583 109003224327576713523591875)
      ·
        refine ⟨163504836491365070285387813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 109003224327576713523591875 163504836491365070285387813)
        ·
          refine ⟨30657156842130950678510215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 163504836491365070285387813 30657156842130950678510215)
          ·
            refine ⟨45985735263196426017765323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30657156842130950678510215 45985735263196426017765323)
            ·
              refine ⟨68978602894794639026647985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45985735263196426017765323 68978602894794639026647985)
              ·
                refine ⟨51733952171095979269985989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 68978602894794639026647985 51733952171095979269985989)
                ·
                  refine ⟨9700116032080496113122373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 51733952171095979269985989 9700116032080496113122373)
                  ·
                    refine ⟨1818771756015093021210445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9700116032080496113122373 1818771756015093021210445)
                    ·
                      refine ⟨682039408505659882953917, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1818771756015093021210445 682039408505659882953917)
                      ·
                        rfl

theorem cell23_1328267_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 2, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 2, 4, 4, 3].length) (baseStart_1328267 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1328267 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1328267 prefixEnd_1328267 := by exact prefixLift 1328267
  have htrace : WordTrace (prefixWord ++ tailWord_1328267) baseStart_1328267 baseEnd_1328267 := by
    simpa [prefixWord, tailWord_1328267, baseEnd_1328267] using wordTrace_append hprefix tailTrace_1328267
  have hstable : (prefixWord ++ tailWord_1328267).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1328267).length < 2 ^ (prefixWord ++ tailWord_1328267).sum := by decide
  have hdescent : baseEnd_1328267 < baseStart_1328267 := by decide
  rcases family_descends (prefixWord ++ tailWord_1328267) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1328284 : List Nat := [2, 2, 3, 2, 1, 2, 1, 1, 2, 4, 3]
def baseStart_1328284 : Nat := 118140960795 + 1328284 * 2 ^ 59
def prefixEnd_1328284 : Nat := 4983230072969 + 3 ^ 40 * 1328284 * 2
def baseEnd_1328284 : Nat := 682048137676786316441339

theorem tailTrace_1328284 : CollatzResearch.WordTrace tailWord_1328284 prefixEnd_1328284 682048137676786316441339 := by
  unfold tailWord_1328284
  simp only [CollatzResearch.WordTrace]
  refine ⟨24223248759930697845815953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32297665013240930461087937 24223248759930697845815953)
  ·
    refine ⟨18167436569948023384361965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24223248759930697845815953 18167436569948023384361965)
    ·
      refine ⟨6812788713730508769135737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18167436569948023384361965 6812788713730508769135737)
      ·
        refine ⟨5109591535297881576851803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6812788713730508769135737 5109591535297881576851803)
        ·
          refine ⟨7664387302946822365277705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5109591535297881576851803 7664387302946822365277705)
          ·
            refine ⟨5748290477210116773958279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7664387302946822365277705 5748290477210116773958279)
            ·
              refine ⟨8622435715815175160937419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5748290477210116773958279 8622435715815175160937419)
              ·
                refine ⟨12933653573722762741406129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8622435715815175160937419 12933653573722762741406129)
                ·
                  refine ⟨9700240180292072056054597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12933653573722762741406129 9700240180292072056054597)
                  ·
                    refine ⟨1818795033804763510510237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9700240180292072056054597 1818795033804763510510237)
                    ·
                      refine ⟨682048137676786316441339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1818795033804763510510237 682048137676786316441339)
                      ·
                        rfl

theorem cell23_1328284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 1, 1, 2, 4, 3].length) (baseStart_1328284 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1328284 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1328284 prefixEnd_1328284 := by exact prefixLift 1328284
  have htrace : WordTrace (prefixWord ++ tailWord_1328284) baseStart_1328284 baseEnd_1328284 := by
    simpa [prefixWord, tailWord_1328284, baseEnd_1328284] using wordTrace_append hprefix tailTrace_1328284
  have hstable : (prefixWord ++ tailWord_1328284).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1328284).length < 2 ^ (prefixWord ++ tailWord_1328284).sum := by decide
  have hdescent : baseEnd_1328284 < baseStart_1328284 := by decide
  rcases family_descends (prefixWord ++ tailWord_1328284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1328298 : List Nat := [3, 1, 5, 1, 1, 1, 1, 3, 1, 4, 2]
def baseStart_1328298 : Nat := 118140960795 + 1328298 * 2 ^ 59
def prefixEnd_1328298 : Nat := 4983230072969 + 3 ^ 40 * 1328298 * 2
def baseEnd_1328298 : Nat := 682055326405949261666275

theorem tailTrace_1328298 : CollatzResearch.WordTrace tailWord_1328298 prefixEnd_1328298 682055326405949261666275 := by
  unfold tailWord_1328298
  simp only [CollatzResearch.WordTrace]
  refine ⟨12111752035452669020660387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32298005427873784055094365 12111752035452669020660387)
  ·
    refine ⟨18167628053179003530990581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12111752035452669020660387 18167628053179003530990581)
    ·
      refine ⟨1703215129985531581030367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 18167628053179003530990581 1703215129985531581030367)
      ·
        refine ⟨2554822694978297371545551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1703215129985531581030367 2554822694978297371545551)
        ·
          refine ⟨3832234042467446057318327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2554822694978297371545551 3832234042467446057318327)
          ·
            refine ⟨5748351063701169085977491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3832234042467446057318327 5748351063701169085977491)
            ·
              refine ⟨8622526595551753628966237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5748351063701169085977491 8622526595551753628966237)
              ·
                refine ⟨3233447473331907610862339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8622526595551753628966237 3233447473331907610862339)
                ·
                  refine ⟨4850171209997861416293509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3233447473331907610862339 4850171209997861416293509)
                  ·
                    refine ⟨909407101874599015555033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4850171209997861416293509 909407101874599015555033)
                    ·
                      refine ⟨682055326405949261666275, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 909407101874599015555033 682055326405949261666275)
                      ·
                        rfl

theorem cell23_1328298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 1, 3, 1, 4, 2].length) (baseStart_1328298 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1328298 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1328298 prefixEnd_1328298 := by exact prefixLift 1328298
  have htrace : WordTrace (prefixWord ++ tailWord_1328298) baseStart_1328298 baseEnd_1328298 := by
    simpa [prefixWord, tailWord_1328298, baseEnd_1328298] using wordTrace_append hprefix tailTrace_1328298
  have hstable : (prefixWord ++ tailWord_1328298).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1328298).length < 2 ^ (prefixWord ++ tailWord_1328298).sum := by decide
  have hdescent : baseEnd_1328298 < baseStart_1328298 := by decide
  rcases family_descends (prefixWord ++ tailWord_1328298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1328326 : List Nat := [6, 1, 2, 2, 2, 1, 1, 2, 2, 1, 3]
def baseStart_1328326 : Nat := 118140960795 + 1328326 * 2 ^ 59
def prefixEnd_1328326 : Nat := 4983230072969 + 3 ^ 40 * 1328326 * 2
def baseEnd_1328326 : Nat := 682069703864275152116147

theorem tailTrace_1328326 : CollatzResearch.WordTrace tailWord_1328326 prefixEnd_1328326 682069703864275152116147 := by
  unfold tailWord_1328326
  simp only [CollatzResearch.WordTrace]
  refine ⟨1514000918303413652020651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 32298686257139491243107221 1514000918303413652020651)
  ·
    refine ⟨2271001377455120478030977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1514000918303413652020651 2271001377455120478030977)
    ·
      refine ⟨1703251033091340358523233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2271001377455120478030977 1703251033091340358523233)
      ·
        refine ⟨1277438274818505268892425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1703251033091340358523233 1277438274818505268892425)
        ·
          refine ⟨958078706113878951669319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1277438274818505268892425 958078706113878951669319)
          ·
            refine ⟨1437118059170818427503979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 958078706113878951669319 1437118059170818427503979)
            ·
              refine ⟨2155677088756227641255969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1437118059170818427503979 2155677088756227641255969)
              ·
                refine ⟨1616757816567170730941977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2155677088756227641255969 1616757816567170730941977)
                ·
                  refine ⟨1212568362425378048206483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1616757816567170730941977 1212568362425378048206483)
                  ·
                    refine ⟨1818852543638067072309725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1212568362425378048206483 1818852543638067072309725)
                    ·
                      refine ⟨682069703864275152116147, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1818852543638067072309725 682069703864275152116147)
                      ·
                        rfl

theorem cell23_1328326_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 2, 1, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 2, 1, 1, 2, 2, 1, 3].length) (baseStart_1328326 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1328326 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1328326 prefixEnd_1328326 := by exact prefixLift 1328326
  have htrace : WordTrace (prefixWord ++ tailWord_1328326) baseStart_1328326 baseEnd_1328326 := by
    simpa [prefixWord, tailWord_1328326, baseEnd_1328326] using wordTrace_append hprefix tailTrace_1328326
  have hstable : (prefixWord ++ tailWord_1328326).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1328326).length < 2 ^ (prefixWord ++ tailWord_1328326).sum := by decide
  have hdescent : baseEnd_1328326 < baseStart_1328326 := by decide
  rcases family_descends (prefixWord ++ tailWord_1328326) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1328327 : List Nat := [1, 1, 4, 1, 1, 1, 1, 3, 3, 2, 5]
def baseStart_1328327 : Nat := 118140960795 + 1328327 * 2 ^ 59
def prefixEnd_1328327 : Nat := 4983230072969 + 3 ^ 40 * 1328327 * 2
def baseEnd_1328327 : Nat := 682070217344929648203641

theorem tailTrace_1328327 : CollatzResearch.WordTrace tailWord_1328327 prefixEnd_1328327 682070217344929648203641 := by
  unfold tailWord_1328327
  simp only [CollatzResearch.WordTrace]
  refine ⟨48448065858705614035447235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32298710572470409356964823 48448065858705614035447235)
  ·
    refine ⟨72672098788058421053170853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48448065858705614035447235 72672098788058421053170853)
    ·
      refine ⟨13626018522760953947469535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 72672098788058421053170853 13626018522760953947469535)
      ·
        refine ⟨20439027784141430921204303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13626018522760953947469535 20439027784141430921204303)
        ·
          refine ⟨30658541676212146381806455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20439027784141430921204303 30658541676212146381806455)
          ·
            refine ⟨45987812514318219572709683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30658541676212146381806455 45987812514318219572709683)
            ·
              refine ⟨68981718771477329359064525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45987812514318219572709683 68981718771477329359064525)
              ·
                refine ⟨25868144539303998509649197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 68981718771477329359064525 25868144539303998509649197)
                ·
                  refine ⟨9700554202238999441118449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25868144539303998509649197 9700554202238999441118449)
                  ·
                    refine ⟨7275415651679249580838837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9700554202238999441118449 7275415651679249580838837)
                    ·
                      refine ⟨682070217344929648203641, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7275415651679249580838837 682070217344929648203641)
                      ·
                        rfl

theorem cell23_1328327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 3, 3, 2, 5].length) (baseStart_1328327 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1328327 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1328327 prefixEnd_1328327 := by exact prefixLift 1328327
  have htrace : WordTrace (prefixWord ++ tailWord_1328327) baseStart_1328327 baseEnd_1328327 := by
    simpa [prefixWord, tailWord_1328327, baseEnd_1328327] using wordTrace_append hprefix tailTrace_1328327
  have hstable : (prefixWord ++ tailWord_1328327).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1328327).length < 2 ^ (prefixWord ++ tailWord_1328327).sum := by decide
  have hdescent : baseEnd_1328327 < baseStart_1328327 := by decide
  rcases family_descends (prefixWord ++ tailWord_1328327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1328374 : List Nat := [5, 1, 1, 1, 1, 1, 1, 2, 2, 3, 5]
def baseStart_1328374 : Nat := 118140960795 + 1328374 * 2 ^ 59
def prefixEnd_1328374 : Nat := 4983230072969 + 3 ^ 40 * 1328374 * 2
def baseEnd_1328374 : Nat := 682094350935690964315925

theorem tailTrace_1328374 : CollatzResearch.WordTrace tailWord_1328374 prefixEnd_1328374 682094350935690964315925 := by
  unfold tailWord_1328374
  simp only [CollatzResearch.WordTrace]
  refine ⟨3028111255595958816400511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 32299853393023560708272117 3028111255595958816400511)
  ·
    refine ⟨4542166883393938224600767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3028111255595958816400511 4542166883393938224600767)
    ·
      refine ⟨6813250325090907336901151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4542166883393938224600767 6813250325090907336901151)
      ·
        refine ⟨10219875487636361005351727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6813250325090907336901151 10219875487636361005351727)
        ·
          refine ⟨15329813231454541508027591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10219875487636361005351727 15329813231454541508027591)
          ·
            refine ⟨22994719847181812262041387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15329813231454541508027591 22994719847181812262041387)
            ·
              refine ⟨34492079770772718393062081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22994719847181812262041387 34492079770772718393062081)
              ·
                refine ⟨25869059828079538794796561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34492079770772718393062081 25869059828079538794796561)
                ·
                  refine ⟨19401794871059654096097421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25869059828079538794796561 19401794871059654096097421)
                  ·
                    refine ⟨7275673076647370286036533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19401794871059654096097421 7275673076647370286036533)
                    ·
                      refine ⟨682094350935690964315925, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7275673076647370286036533 682094350935690964315925)
                      ·
                        rfl

theorem cell23_1328374_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 1, 2, 2, 3, 5].length) (baseStart_1328374 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1328374 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1328374 prefixEnd_1328374 := by exact prefixLift 1328374
  have htrace : WordTrace (prefixWord ++ tailWord_1328374) baseStart_1328374 baseEnd_1328374 := by
    simpa [prefixWord, tailWord_1328374, baseEnd_1328374] using wordTrace_append hprefix tailTrace_1328374
  have hstable : (prefixWord ++ tailWord_1328374).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1328374).length < 2 ^ (prefixWord ++ tailWord_1328374).sum := by decide
  have hdescent : baseEnd_1328374 < baseStart_1328374 := by decide
  rcases family_descends (prefixWord ++ tailWord_1328374) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1328377 : List Nat := [1, 2, 1, 3, 1, 1, 3, 1, 10]
def baseStart_1328377 : Nat := 118140960795 + 1328377 * 2 ^ 59
def prefixEnd_1328377 : Nat := 4983230072969 + 3 ^ 40 * 1328377 * 2
def baseEnd_1328377 : Nat := 75788432375294939175379

theorem tailTrace_1328377 : CollatzResearch.WordTrace tailWord_1328377 prefixEnd_1328377 75788432375294939175379 := by
  unfold tailWord_1328377
  simp only [CollatzResearch.WordTrace]
  refine ⟨48449889508524472574767385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32299926339016315049844923 48449889508524472574767385)
  ·
    refine ⟨36337417131393354431075539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48449889508524472574767385 36337417131393354431075539)
    ·
      refine ⟨54506125697090031646613309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36337417131393354431075539 54506125697090031646613309)
      ·
        refine ⟨20439797136408761867479991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 54506125697090031646613309 20439797136408761867479991)
        ·
          refine ⟨30659695704613142801219987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20439797136408761867479991 30659695704613142801219987)
          ·
            refine ⟨45989543556919714201829981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30659695704613142801219987 45989543556919714201829981)
            ·
              refine ⟨17246078833844892825686243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 45989543556919714201829981 17246078833844892825686243)
              ·
                refine ⟨25869118250767339238529365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17246078833844892825686243 25869118250767339238529365)
                ·
                  refine ⟨75788432375294939175379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 25869118250767339238529365 75788432375294939175379)
                  ·
                    rfl

theorem cell23_1328377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 3, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 3, 1, 10].length) (baseStart_1328377 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1328377 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1328377 prefixEnd_1328377 := by exact prefixLift 1328377
  have htrace : WordTrace (prefixWord ++ tailWord_1328377) baseStart_1328377 baseEnd_1328377 := by
    simpa [prefixWord, tailWord_1328377, baseEnd_1328377] using wordTrace_append hprefix tailTrace_1328377
  have hstable : (prefixWord ++ tailWord_1328377).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1328377).length < 2 ^ (prefixWord ++ tailWord_1328377).sum := by decide
  have hdescent : baseEnd_1328377 < baseStart_1328377 := by decide
  rcases family_descends (prefixWord ++ tailWord_1328377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1328394 : List Nat := [3, 1, 2, 2, 1, 1, 1, 6, 6]
def baseStart_1328394 : Nat := 118140960795 + 1328394 * 2 ^ 59
def prefixEnd_1328394 : Nat := 4983230072969 + 3 ^ 40 * 1328394 * 2
def baseEnd_1328394 : Nat := 75789402283197876229537

theorem tailTrace_1328394 : CollatzResearch.WordTrace tailWord_1328394 prefixEnd_1328394 75789402283197876229537 := by
  unfold tailWord_1328394
  simp only [CollatzResearch.WordTrace]
  refine ⟨12112627387365721119534059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32300339699641922985424157 12112627387365721119534059)
  ·
    refine ⟨18168941081048581679301089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12112627387365721119534059 18168941081048581679301089)
    ·
      refine ⟨13626705810786436259475817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18168941081048581679301089 13626705810786436259475817)
      ·
        refine ⟨10220029358089827194606863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13626705810786436259475817 10220029358089827194606863)
        ·
          refine ⟨15330044037134740791910295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10220029358089827194606863 15330044037134740791910295)
          ·
            refine ⟨22995066055702111187865443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15330044037134740791910295 22995066055702111187865443)
            ·
              refine ⟨34492599083553166781798165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22995066055702111187865443 34492599083553166781798165)
              ·
                refine ⟨1616840582041554692896789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 34492599083553166781798165 1616840582041554692896789)
                ·
                  refine ⟨75789402283197876229537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1616840582041554692896789 75789402283197876229537)
                  ·
                    rfl

theorem cell23_1328394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 1, 6, 6].length) (baseStart_1328394 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1328394 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1328394 prefixEnd_1328394 := by exact prefixLift 1328394
  have htrace : WordTrace (prefixWord ++ tailWord_1328394) baseStart_1328394 baseEnd_1328394 := by
    simpa [prefixWord, tailWord_1328394, baseEnd_1328394] using wordTrace_append hprefix tailTrace_1328394
  have hstable : (prefixWord ++ tailWord_1328394).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1328394).length < 2 ^ (prefixWord ++ tailWord_1328394).sum := by decide
  have hdescent : baseEnd_1328394 < baseStart_1328394 := by decide
  rcases family_descends (prefixWord ++ tailWord_1328394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1328398 : List Nat := [4, 1, 1, 2, 1, 5, 1, 1, 3, 4]
def baseStart_1328398 : Nat := 118140960795 + 1328398 * 2 ^ 59
def prefixEnd_1328398 : Nat := 4983230072969 + 3 ^ 40 * 1328398 * 2
def baseEnd_1328398 : Nat := 227368891490466290138605

theorem tailTrace_1328398 : CollatzResearch.WordTrace tailWord_1328398 prefixEnd_1328398 227368891490466290138605 := by
  unfold tailWord_1328398
  simp only [CollatzResearch.WordTrace]
  refine ⟨6056331930181049145160231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 32300436960965595440854565 6056331930181049145160231)
  ·
    refine ⟨9084497895271573717740347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6056331930181049145160231 9084497895271573717740347)
    ·
      refine ⟨13626746842907360576610521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9084497895271573717740347 13626746842907360576610521)
      ·
        refine ⟨10220060132180520432457891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13626746842907360576610521 10220060132180520432457891)
        ·
          refine ⟨15330090198270780648686837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10220060132180520432457891 15330090198270780648686837)
          ·
            refine ⟨1437195956087885685814391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 15330090198270780648686837 1437195956087885685814391)
            ·
              refine ⟨2155793934131828528721587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1437195956087885685814391 2155793934131828528721587)
              ·
                refine ⟨3233690901197742793082381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2155793934131828528721587 3233690901197742793082381)
                ·
                  refine ⟨1212634087949153547405893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3233690901197742793082381 1212634087949153547405893)
                  ·
                    refine ⟨227368891490466290138605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1212634087949153547405893 227368891490466290138605)
                    ·
                      rfl

theorem cell23_1328398_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 5, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 5, 1, 1, 3, 4].length) (baseStart_1328398 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1328398 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1328398 prefixEnd_1328398 := by exact prefixLift 1328398
  have htrace : WordTrace (prefixWord ++ tailWord_1328398) baseStart_1328398 baseEnd_1328398 := by
    simpa [prefixWord, tailWord_1328398, baseEnd_1328398] using wordTrace_append hprefix tailTrace_1328398
  have hstable : (prefixWord ++ tailWord_1328398).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1328398).length < 2 ^ (prefixWord ++ tailWord_1328398).sum := by decide
  have hdescent : baseEnd_1328398 < baseStart_1328398 := by decide
  rcases family_descends (prefixWord ++ tailWord_1328398) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1328455 : List Nat := [1, 1, 4, 1, 2, 4, 1, 4, 1, 1, 3]
def baseStart_1328455 : Nat := 118140960795 + 1328455 * 2 ^ 59
def prefixEnd_1328455 : Nat := 4983230072969 + 3 ^ 40 * 1328455 * 2
def baseEnd_1328455 : Nat := 682135942868705147403053

theorem tailTrace_1328455 : CollatzResearch.WordTrace tailWord_1328455 prefixEnd_1328455 682135942868705147403053 := by
  unfold tailWord_1328455
  simp only [CollatzResearch.WordTrace]
  refine ⟨48452734402241891896106819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32301822934827927930737879 48452734402241891896106819)
  ·
    refine ⟨72679101603362837844160229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48452734402241891896106819 72679101603362837844160229)
    ·
      refine ⟨13627331550630532095780043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 72679101603362837844160229 13627331550630532095780043)
      ·
        refine ⟨20440997325945798143670065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13627331550630532095780043 20440997325945798143670065)
        ·
          refine ⟨15330747994459348607752549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20440997325945798143670065 15330747994459348607752549)
          ·
            refine ⟨2874515248961127863953603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 15330747994459348607752549 2874515248961127863953603)
            ·
              refine ⟨4311772873441691795930405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2874515248961127863953603 4311772873441691795930405)
              ·
                refine ⟨808457413770317211736951, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4311772873441691795930405 808457413770317211736951)
                ·
                  refine ⟨1212686120655475817605427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 808457413770317211736951 1212686120655475817605427)
                  ·
                    refine ⟨1819029180983213726408141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1212686120655475817605427 1819029180983213726408141)
                    ·
                      refine ⟨682135942868705147403053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1819029180983213726408141 682135942868705147403053)
                      ·
                        rfl

theorem cell23_1328455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 4, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 4, 1, 4, 1, 1, 3].length) (baseStart_1328455 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1328455 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1328455 prefixEnd_1328455 := by exact prefixLift 1328455
  have htrace : WordTrace (prefixWord ++ tailWord_1328455) baseStart_1328455 baseEnd_1328455 := by
    simpa [prefixWord, tailWord_1328455, baseEnd_1328455] using wordTrace_append hprefix tailTrace_1328455
  have hstable : (prefixWord ++ tailWord_1328455).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1328455).length < 2 ^ (prefixWord ++ tailWord_1328455).sum := by decide
  have hdescent : baseEnd_1328455 < baseStart_1328455 := by decide
  rcases family_descends (prefixWord ++ tailWord_1328455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1328464 : List Nat := [2, 1, 1, 1, 1, 5, 2, 1, 3, 1, 5]
def baseStart_1328464 : Nat := 118140960795 + 1328464 * 2 ^ 59
def prefixEnd_1328464 : Nat := 4983230072969 + 3 ^ 40 * 1328464 * 2
def baseEnd_1328464 : Nat := 682140564194595612190511

theorem tailTrace_1328464 : CollatzResearch.WordTrace tailWord_1328464 prefixEnd_1328464 682140564194595612190511 := by
  unfold tailWord_1328464
  simp only [CollatzResearch.WordTrace]
  refine ⟨24226531329604643216592223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32302041772806190955456297 24226531329604643216592223)
  ·
    refine ⟨36339796994406964824888335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24226531329604643216592223 36339796994406964824888335)
    ·
      refine ⟨54509695491610447237332503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36339796994406964824888335 54509695491610447237332503)
      ·
        refine ⟨81764543237415670855998755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54509695491610447237332503 81764543237415670855998755)
        ·
          refine ⟨122646814856123506283998133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 81764543237415670855998755 122646814856123506283998133)
          ·
            refine ⟨11498138892761578714124825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 122646814856123506283998133 11498138892761578714124825)
            ·
              refine ⟨8623604169571184035593619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11498138892761578714124825 8623604169571184035593619)
              ·
                refine ⟨12935406254356776053390429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8623604169571184035593619 12935406254356776053390429)
                ·
                  refine ⟨4850777345383791020021411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12935406254356776053390429 4850777345383791020021411)
                  ·
                    refine ⟨7276166018075686530032117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4850777345383791020021411 7276166018075686530032117)
                    ·
                      refine ⟨682140564194595612190511, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7276166018075686530032117 682140564194595612190511)
                      ·
                        rfl

theorem cell23_1328464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 2, 1, 3, 1, 5].length) (baseStart_1328464 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1328464 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1328464 prefixEnd_1328464 := by exact prefixLift 1328464
  have htrace : WordTrace (prefixWord ++ tailWord_1328464) baseStart_1328464 baseEnd_1328464 := by
    simpa [prefixWord, tailWord_1328464, baseEnd_1328464] using wordTrace_append hprefix tailTrace_1328464
  have hstable : (prefixWord ++ tailWord_1328464).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1328464).length < 2 ^ (prefixWord ++ tailWord_1328464).sum := by decide
  have hdescent : baseEnd_1328464 < baseStart_1328464 := by decide
  rcases family_descends (prefixWord ++ tailWord_1328464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1328471 : List Nat := [1, 1, 3, 2, 3, 3, 2, 1, 1, 6]
def baseStart_1328471 : Nat := 118140960795 + 1328471 * 2 ^ 59
def prefixEnd_1328471 : Nat := 4983230072969 + 3 ^ 40 * 1328471 * 2
def baseEnd_1328471 : Nat := 227381386186392361600993

theorem tailTrace_1328471 : CollatzResearch.WordTrace tailWord_1328471 prefixEnd_1328471 227381386186392361600993 := by
  unfold tailWord_1328471
  simp only [CollatzResearch.WordTrace]
  refine ⟨48453317970183926628689267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32302211980122617752459511 48453317970183926628689267)
  ·
    refine ⟨72679976955275889943033901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48453317970183926628689267 72679976955275889943033901)
    ·
      refine ⟨27254991358228458728637713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 72679976955275889943033901 27254991358228458728637713)
      ·
        refine ⟨20441243518671344046478285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27254991358228458728637713 20441243518671344046478285)
        ·
          refine ⟨7665466319501754017429357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20441243518671344046478285 7665466319501754017429357)
          ·
            refine ⟨2874549869813157756536009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7665466319501754017429357 2874549869813157756536009)
            ·
              refine ⟨2155912402359868317402007, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2874549869813157756536009 2155912402359868317402007)
              ·
                refine ⟨3233868603539802476103011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2155912402359868317402007 3233868603539802476103011)
                ·
                  refine ⟨4850802905309703714154517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3233868603539802476103011 4850802905309703714154517)
                  ·
                    refine ⟨227381386186392361600993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4850802905309703714154517 227381386186392361600993)
                    ·
                      rfl

theorem cell23_1328471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 3, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 3, 2, 1, 1, 6].length) (baseStart_1328471 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1328471 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1328471 prefixEnd_1328471 := by exact prefixLift 1328471
  have htrace : WordTrace (prefixWord ++ tailWord_1328471) baseStart_1328471 baseEnd_1328471 := by
    simpa [prefixWord, tailWord_1328471, baseEnd_1328471] using wordTrace_append hprefix tailTrace_1328471
  have hstable : (prefixWord ++ tailWord_1328471).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1328471).length < 2 ^ (prefixWord ++ tailWord_1328471).sum := by decide
  have hdescent : baseEnd_1328471 < baseStart_1328471 := by decide
  rcases family_descends (prefixWord ++ tailWord_1328471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1328474 : List Nat := [3, 1, 1, 2, 1, 2, 2, 3, 1, 1, 6]
def baseStart_1328474 : Nat := 118140960795 + 1328474 * 2 ^ 59
def prefixEnd_1328474 : Nat := 4983230072969 + 3 ^ 40 * 1328474 * 2
def baseEnd_1328474 : Nat := 682145699001140573065465

theorem tailTrace_1328474 : CollatzResearch.WordTrace tailWord_1328474 prefixEnd_1328474 682145699001140573065465 := by
  unfold tailWord_1328474
  simp only [CollatzResearch.WordTrace]
  refine ⟨12113356847293264535262119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32302284926115372094032317 12113356847293264535262119)
  ·
    refine ⟨18170035270939896802893179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12113356847293264535262119 18170035270939896802893179)
    ·
      refine ⟨27255052906409845204339769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18170035270939896802893179 27255052906409845204339769)
      ·
        refine ⟨20441289679807383903254827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27255052906409845204339769 20441289679807383903254827)
        ·
          refine ⟨30661934519711075854882241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20441289679807383903254827 30661934519711075854882241)
          ·
            refine ⟨22996450889783306891161681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30661934519711075854882241 22996450889783306891161681)
            ·
              refine ⟨17247338167337480168371261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22996450889783306891161681 17247338167337480168371261)
              ·
                refine ⟨6467751812751555063139223, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17247338167337480168371261 6467751812751555063139223)
                ·
                  refine ⟨9701627719127332594708835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6467751812751555063139223 9701627719127332594708835)
                  ·
                    refine ⟨14552441578690998892063253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9701627719127332594708835 14552441578690998892063253)
                    ·
                      refine ⟨682145699001140573065465, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 14552441578690998892063253 682145699001140573065465)
                      ·
                        rfl

theorem cell23_1328474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 2, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 2, 3, 1, 1, 6].length) (baseStart_1328474 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1328474 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1328474 prefixEnd_1328474 := by exact prefixLift 1328474
  have htrace : WordTrace (prefixWord ++ tailWord_1328474) baseStart_1328474 baseEnd_1328474 := by
    simpa [prefixWord, tailWord_1328474, baseEnd_1328474] using wordTrace_append hprefix tailTrace_1328474
  have hstable : (prefixWord ++ tailWord_1328474).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1328474).length < 2 ^ (prefixWord ++ tailWord_1328474).sum := by decide
  have hdescent : baseEnd_1328474 < baseStart_1328474 := by decide
  rcases family_descends (prefixWord ++ tailWord_1328474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1328498 : List Nat := [3, 2, 1, 2, 1, 2, 3, 3, 1, 2, 3]
def baseStart_1328498 : Nat := 118140960795 + 1328498 * 2 ^ 59
def prefixEnd_1328498 : Nat := 4983230072969 + 3 ^ 40 * 1328498 * 2
def baseEnd_1328498 : Nat := 682158022536848479165355

theorem tailTrace_1328498 : CollatzResearch.WordTrace tailWord_1328498 prefixEnd_1328498 682158022536848479165355 := by
  unfold tailWord_1328498
  simp only [CollatzResearch.WordTrace]
  refine ⟨12113575685271527559980537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32302868494057406826614765 12113575685271527559980537)
  ·
    refine ⟨9085181763953645669985403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12113575685271527559980537 9085181763953645669985403)
    ·
      refine ⟨13627772645930468504978105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9085181763953645669985403 13627772645930468504978105)
      ·
        refine ⟨10220829484447851378733579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13627772645930468504978105 10220829484447851378733579)
        ·
          refine ⟨15331244226671777068100369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10220829484447851378733579 15331244226671777068100369)
          ·
            refine ⟨11498433170003832801075277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15331244226671777068100369 11498433170003832801075277)
            ·
              refine ⟨4311912438751437300403229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11498433170003832801075277 4311912438751437300403229)
              ·
                refine ⟨1616967164531788987651211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4311912438751437300403229 1616967164531788987651211)
                ·
                  refine ⟨2425450746797683481476817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1616967164531788987651211 2425450746797683481476817)
                  ·
                    refine ⟨1819088060098262611107613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2425450746797683481476817 1819088060098262611107613)
                    ·
                      refine ⟨682158022536848479165355, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1819088060098262611107613 682158022536848479165355)
                      ·
                        rfl

theorem cell23_1328498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 3, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 3, 3, 1, 2, 3].length) (baseStart_1328498 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1328498 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1328498 prefixEnd_1328498 := by exact prefixLift 1328498
  have htrace : WordTrace (prefixWord ++ tailWord_1328498) baseStart_1328498 baseEnd_1328498 := by
    simpa [prefixWord, tailWord_1328498, baseEnd_1328498] using wordTrace_append hprefix tailTrace_1328498
  have hstable : (prefixWord ++ tailWord_1328498).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1328498).length < 2 ^ (prefixWord ++ tailWord_1328498).sum := by decide
  have hdescent : baseEnd_1328498 < baseStart_1328498 := by decide
  rcases family_descends (prefixWord ++ tailWord_1328498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1328501 : List Nat := [1, 3, 4, 1, 3, 1, 10]
def baseStart_1328501 : Nat := 118140960795 + 1328501 * 2 ^ 59
def prefixEnd_1328501 : Nat := 4983230072969 + 3 ^ 40 * 1328501 * 2
def baseEnd_1328501 : Nat := 8421722999738419350961

theorem tailTrace_1328501 : CollatzResearch.WordTrace tailWord_1328501 prefixEnd_1328501 8421722999738419350961 := by
  unfold tailWord_1328501
  simp only [CollatzResearch.WordTrace]
  refine ⟨48454412160075241752281357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32302941440050161168187571 48454412160075241752281357)
  ·
    refine ⟨18170404560028215657105509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 48454412160075241752281357 18170404560028215657105509)
    ·
      refine ⟨3406950855005290435707283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 18170404560028215657105509 3406950855005290435707283)
      ·
        refine ⟨5110426282507935653560925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3406950855005290435707283 5110426282507935653560925)
        ·
          refine ⟨1916409855940475870085347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5110426282507935653560925 1916409855940475870085347)
          ·
            refine ⟨2874614783910713805128021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1916409855940475870085347 2874614783910713805128021)
            ·
              refine ⟨8421722999738419350961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 2874614783910713805128021 8421722999738419350961)
              ·
                rfl

theorem cell23_1328501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 3, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 3, 1, 10].length) (baseStart_1328501 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1328501 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1328501 prefixEnd_1328501 := by exact prefixLift 1328501
  have htrace : WordTrace (prefixWord ++ tailWord_1328501) baseStart_1328501 baseEnd_1328501 := by
    simpa [prefixWord, tailWord_1328501, baseEnd_1328501] using wordTrace_append hprefix tailTrace_1328501
  have hstable : (prefixWord ++ tailWord_1328501).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1328501).length < 2 ^ (prefixWord ++ tailWord_1328501).sum := by decide
  have hdescent : baseEnd_1328501 < baseStart_1328501 := by decide
  rcases family_descends (prefixWord ++ tailWord_1328501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1328541 : List Nat := [1, 4, 2, 1, 3, 1, 1, 1, 2, 2, 5]
def baseStart_1328541 : Nat := 118140960795 + 1328541 * 2 ^ 59
def prefixEnd_1328541 : Nat := 4983230072969 + 3 ^ 40 * 1328541 * 2
def baseEnd_1328541 : Nat := 682180102204991810927657

theorem tailTrace_1328541 : CollatzResearch.WordTrace tailWord_1328541 prefixEnd_1328541 682180102204991810927657 := by
  unfold tailWord_1328541
  simp only [CollatzResearch.WordTrace]
  refine ⟨48455871079930328583737477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32303914053286885722491651 48455871079930328583737477)
  ·
    refine ⟨9085475827486936609450777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 48455871079930328583737477 9085475827486936609450777)
    ·
      refine ⟨6814106870615202457088083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9085475827486936609450777 6814106870615202457088083)
      ·
        refine ⟨10221160305922803685632125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6814106870615202457088083 10221160305922803685632125)
        ·
          refine ⟨3832935114721051382112047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10221160305922803685632125 3832935114721051382112047)
          ·
            refine ⟨5749402672081577073168071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3832935114721051382112047 5749402672081577073168071)
            ·
              refine ⟨8624104008122365609752107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5749402672081577073168071 8624104008122365609752107)
              ·
                refine ⟨12936156012183548414628161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8624104008122365609752107 12936156012183548414628161)
                ·
                  refine ⟨9702117009137661310971121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12936156012183548414628161 9702117009137661310971121)
                  ·
                    refine ⟨7276587756853245983228341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9702117009137661310971121 7276587756853245983228341)
                    ·
                      refine ⟨682180102204991810927657, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7276587756853245983228341 682180102204991810927657)
                      ·
                        rfl

theorem cell23_1328541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 1, 1, 2, 2, 5].length) (baseStart_1328541 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1328541 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1328541 prefixEnd_1328541 := by exact prefixLift 1328541
  have htrace : WordTrace (prefixWord ++ tailWord_1328541) baseStart_1328541 baseEnd_1328541 := by
    simpa [prefixWord, tailWord_1328541, baseEnd_1328541] using wordTrace_append hprefix tailTrace_1328541
  have hstable : (prefixWord ++ tailWord_1328541).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1328541).length < 2 ^ (prefixWord ++ tailWord_1328541).sum := by decide
  have hdescent : baseEnd_1328541 < baseStart_1328541 := by decide
  rcases family_descends (prefixWord ++ tailWord_1328541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1328625 : List Nat := [1, 2, 2, 2, 3, 2, 4, 2, 5]
def baseStart_1328625 : Nat := 118140960795 + 1328625 * 2 ^ 59
def prefixEnd_1328625 : Nat := 4983230072969 + 3 ^ 40 * 1328625 * 2
def baseEnd_1328625 : Nat := 75802581619996609141919

theorem tailTrace_1328625 : CollatzResearch.WordTrace tailWord_1328625 prefixEnd_1328625 75802581619996609141919 := by
  unfold tailWord_1328625
  simp only [CollatzResearch.WordTrace]
  refine ⟨48458934811626010929795329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32305956541084007286530219 48458934811626010929795329)
  ·
    refine ⟨36344201108719508197346497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48458934811626010929795329 36344201108719508197346497)
    ·
      refine ⟨27258150831539631148009873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36344201108719508197346497 27258150831539631148009873)
      ·
        refine ⟨20443613123654723361007405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27258150831539631148009873 20443613123654723361007405)
        ·
          refine ⟨7666354921370521260377777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20443613123654723361007405 7666354921370521260377777)
          ·
            refine ⟨5749766191027890945283333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7666354921370521260377777 5749766191027890945283333)
            ·
              refine ⟨1078081160817729552240625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5749766191027890945283333 1078081160817729552240625)
              ·
                refine ⟨808560870613297164180469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1078081160817729552240625 808560870613297164180469)
                ·
                  refine ⟨75802581619996609141919, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 808560870613297164180469 75802581619996609141919)
                  ·
                    rfl

theorem cell23_1328625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 4, 2, 5].length) (baseStart_1328625 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1328625 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1328625 prefixEnd_1328625 := by exact prefixLift 1328625
  have htrace : WordTrace (prefixWord ++ tailWord_1328625) baseStart_1328625 baseEnd_1328625 := by
    simpa [prefixWord, tailWord_1328625, baseEnd_1328625] using wordTrace_append hprefix tailTrace_1328625
  have hstable : (prefixWord ++ tailWord_1328625).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1328625).length < 2 ^ (prefixWord ++ tailWord_1328625).sum := by decide
  have hdescent : baseEnd_1328625 < baseStart_1328625 := by decide
  rcases family_descends (prefixWord ++ tailWord_1328625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1328668 : List Nat := [2, 2, 3, 1, 2, 1, 1, 2, 5, 4]
def baseStart_1328668 : Nat := 118140960795 + 1328668 * 2 ^ 59
def prefixEnd_1328668 : Nat := 4983230072969 + 3 ^ 40 * 1328668 * 2
def baseEnd_1328668 : Nat := 227415104749370938013191

theorem tailTrace_1328668 : CollatzResearch.WordTrace tailWord_1328668 prefixEnd_1328668 227415104749370938013191 := by
  unfold tailWord_1328668
  simp only [CollatzResearch.WordTrace]
  refine ⟨24230251575235114636805329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32307002100313486182407105 24230251575235114636805329)
  ·
    refine ⟨18172688681426335977603997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24230251575235114636805329 18172688681426335977603997)
    ·
      refine ⟨6814758255534875991601499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18172688681426335977603997 6814758255534875991601499)
      ·
        refine ⟨10222137383302313987402249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6814758255534875991601499 10222137383302313987402249)
        ·
          refine ⟨7666603037476735490551687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10222137383302313987402249 7666603037476735490551687)
          ·
            refine ⟨11499904556215103235827531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7666603037476735490551687 11499904556215103235827531)
            ·
              refine ⟨17249856834322654853741297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11499904556215103235827531 17249856834322654853741297)
              ·
                refine ⟨12937392625741991140305973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17249856834322654853741297 12937392625741991140305973)
                ·
                  refine ⟨1212880558663311669403685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 12937392625741991140305973 1212880558663311669403685)
                  ·
                    refine ⟨227415104749370938013191, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1212880558663311669403685 227415104749370938013191)
                    ·
                      rfl

theorem cell23_1328668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 1, 2, 5, 4].length) (baseStart_1328668 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1328668 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1328668 prefixEnd_1328668 := by exact prefixLift 1328668
  have htrace : WordTrace (prefixWord ++ tailWord_1328668) baseStart_1328668 baseEnd_1328668 := by
    simpa [prefixWord, tailWord_1328668, baseEnd_1328668] using wordTrace_append hprefix tailTrace_1328668
  have hstable : (prefixWord ++ tailWord_1328668).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1328668).length < 2 ^ (prefixWord ++ tailWord_1328668).sum := by decide
  have hdescent : baseEnd_1328668 < baseStart_1328668 := by decide
  rcases family_descends (prefixWord ++ tailWord_1328668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1328670 : List Nat := [4, 3, 3, 1, 1, 2, 1, 2, 2, 2, 2]
def baseStart_1328670 : Nat := 118140960795 + 1328670 * 2 ^ 59
def prefixEnd_1328670 : Nat := 4983230072969 + 3 ^ 40 * 1328670 * 2
def baseEnd_1328670 : Nat := 682246341209421806214565

theorem tailTrace_1328670 : CollatzResearch.WordTrace tailWord_1328670 prefixEnd_1328670 682246341209421806214565 := by
  unfold tailWord_1328670
  simp only [CollatzResearch.WordTrace]
  refine ⟨6057572012057872951897933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 32307050730975322410122309 6057572012057872951897933)
  ·
    refine ⟨2271589504521702356961725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6057572012057872951897933 2271589504521702356961725)
    ·
      refine ⟨851846064195638383860647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2271589504521702356961725 851846064195638383860647)
      ·
        refine ⟨1277769096293457575790971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 851846064195638383860647 1277769096293457575790971)
        ·
          refine ⟨1916653644440186363686457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1277769096293457575790971 1916653644440186363686457)
          ·
            refine ⟨1437490233330139772764843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1916653644440186363686457 1437490233330139772764843)
            ·
              refine ⟨2156235349995209659147265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1437490233330139772764843 2156235349995209659147265)
              ·
                refine ⟨1617176512496407244360449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2156235349995209659147265 1617176512496407244360449)
                ·
                  refine ⟨1212882384372305433270337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1617176512496407244360449 1212882384372305433270337)
                  ·
                    refine ⟨909661788279229074952753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1212882384372305433270337 909661788279229074952753)
                    ·
                      refine ⟨682246341209421806214565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 909661788279229074952753 682246341209421806214565)
                      ·
                        rfl

theorem cell23_1328670_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 1, 2, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 1, 2, 1, 2, 2, 2, 2].length) (baseStart_1328670 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1328670 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1328670 prefixEnd_1328670 := by exact prefixLift 1328670
  have htrace : WordTrace (prefixWord ++ tailWord_1328670) baseStart_1328670 baseEnd_1328670 := by
    simpa [prefixWord, tailWord_1328670, baseEnd_1328670] using wordTrace_append hprefix tailTrace_1328670
  have hstable : (prefixWord ++ tailWord_1328670).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1328670).length < 2 ^ (prefixWord ++ tailWord_1328670).sum := by decide
  have hdescent : baseEnd_1328670 < baseStart_1328670 := by decide
  rcases family_descends (prefixWord ++ tailWord_1328670) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1328671 : List Nat := [1, 1, 2, 4, 1, 1, 3, 1, 2, 1, 6]
def baseStart_1328671 : Nat := 118140960795 + 1328671 * 2 ^ 59
def prefixEnd_1328671 : Nat := 4983230072969 + 3 ^ 40 * 1328671 * 2
def baseEnd_1328671 : Nat := 682246854690076302302059

theorem tailTrace_1328671 : CollatzResearch.WordTrace tailWord_1328671 prefixEnd_1328671 682246854690076302302059 := by
  unfold tailWord_1328671
  simp only [CollatzResearch.WordTrace]
  refine ⟨48460612569459360785969867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32307075046306240523979911 48460612569459360785969867)
  ·
    refine ⟨72690918854189041178954801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48460612569459360785969867 72690918854189041178954801)
    ·
      refine ⟨54518189140641780884216101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 72690918854189041178954801 54518189140641780884216101)
      ·
        refine ⟨10222160463870333915790519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 54518189140641780884216101 10222160463870333915790519)
        ·
          refine ⟨15333240695805500873685779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10222160463870333915790519 15333240695805500873685779)
          ·
            refine ⟨22999861043708251310528669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15333240695805500873685779 22999861043708251310528669)
            ·
              refine ⟨8624947891390594241448251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22999861043708251310528669 8624947891390594241448251)
              ·
                refine ⟨12937421837085891362172377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8624947891390594241448251 12937421837085891362172377)
                ·
                  refine ⟨9703066377814418521629283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12937421837085891362172377 9703066377814418521629283)
                  ·
                    refine ⟨14554599566721627782443925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9703066377814418521629283 14554599566721627782443925)
                    ·
                      refine ⟨682246854690076302302059, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 14554599566721627782443925 682246854690076302302059)
                      ·
                        rfl

theorem cell23_1328671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 3, 1, 2, 1, 6].length) (baseStart_1328671 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1328671 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1328671 prefixEnd_1328671 := by exact prefixLift 1328671
  have htrace : WordTrace (prefixWord ++ tailWord_1328671) baseStart_1328671 baseEnd_1328671 := by
    simpa [prefixWord, tailWord_1328671, baseEnd_1328671] using wordTrace_append hprefix tailTrace_1328671
  have hstable : (prefixWord ++ tailWord_1328671).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1328671).length < 2 ^ (prefixWord ++ tailWord_1328671).sum := by decide
  have hdescent : baseEnd_1328671 < baseStart_1328671 := by decide
  rcases family_descends (prefixWord ++ tailWord_1328671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1328748 : List Nat := [2, 2, 1, 1, 3, 1, 1, 4, 3, 1, 4]
def baseStart_1328748 : Nat := 118140960795 + 1328748 * 2 ^ 59
def prefixEnd_1328748 : Nat := 4983230072969 + 3 ^ 40 * 1328748 * 2
def baseEnd_1328748 : Nat := 682286392700472501039205

theorem tailTrace_1328748 : CollatzResearch.WordTrace tailWord_1328748 prefixEnd_1328748 682286392700472501039205 := by
  unfold tailWord_1328748
  simp only [CollatzResearch.WordTrace]
  refine ⟨24231710495090201468261449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32308947326786935291015265 24231710495090201468261449)
  ·
    refine ⟨18173782871317651101196087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24231710495090201468261449 18173782871317651101196087)
    ·
      refine ⟨27260674306976476651794131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18173782871317651101196087 27260674306976476651794131)
      ·
        refine ⟨40891011460464714977691197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27260674306976476651794131 40891011460464714977691197)
        ·
          refine ⟨15334129297674268116634199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 40891011460464714977691197 15334129297674268116634199)
          ·
            refine ⟨23001193946511402174951299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15334129297674268116634199 23001193946511402174951299)
            ·
              refine ⟨34501790919767103262426949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23001193946511402174951299 34501790919767103262426949)
              ·
                refine ⟨6469085797456331861705053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 34501790919767103262426949 6469085797456331861705053)
                ·
                  refine ⟨2425907174046124448139395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6469085797456331861705053 2425907174046124448139395)
                  ·
                    refine ⟨3638860761069186672209093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2425907174046124448139395 3638860761069186672209093)
                    ·
                      refine ⟨682286392700472501039205, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3638860761069186672209093 682286392700472501039205)
                      ·
                        rfl

theorem cell23_1328748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 3, 1, 4].length) (baseStart_1328748 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1328748 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1328748 prefixEnd_1328748 := by exact prefixLift 1328748
  have htrace : WordTrace (prefixWord ++ tailWord_1328748) baseStart_1328748 baseEnd_1328748 := by
    simpa [prefixWord, tailWord_1328748, baseEnd_1328748] using wordTrace_append hprefix tailTrace_1328748
  have hstable : (prefixWord ++ tailWord_1328748).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1328748).length < 2 ^ (prefixWord ++ tailWord_1328748).sum := by decide
  have hdescent : baseEnd_1328748 < baseStart_1328748 := by decide
  rcases family_descends (prefixWord ++ tailWord_1328748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1328749 : List Nat := [1, 5, 1, 1, 5, 1, 2, 1, 6]
def baseStart_1328749 : Nat := 118140960795 + 1328749 * 2 ^ 59
def prefixEnd_1328749 : Nat := 4983230072969 + 3 ^ 40 * 1328749 * 2
def baseEnd_1328749 : Nat := 75809656242347444125189

theorem tailTrace_1328749 : CollatzResearch.WordTrace tailWord_1328749 prefixEnd_1328749 75809656242347444125189 := by
  unfold tailWord_1328749
  simp only [CollatzResearch.WordTrace]
  refine ⟨48463457463176780107309301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32308971642117853404872867 48463457463176780107309301)
  ·
    refine ⟨4543449137172823135060247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 48463457463176780107309301 4543449137172823135060247)
    ·
      refine ⟨6815173705759234702590371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4543449137172823135060247 6815173705759234702590371)
      ·
        refine ⟨10222760558638852053885557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6815173705759234702590371 10222760558638852053885557)
        ·
          refine ⟨958383802372392380051771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 10222760558638852053885557 958383802372392380051771)
          ·
            refine ⟨1437575703558588570077657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 958383802372392380051771 1437575703558588570077657)
            ·
              refine ⟨1078181777668941427558243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1437575703558588570077657 1078181777668941427558243)
              ·
                refine ⟨1617272666503412141337365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1078181777668941427558243 1617272666503412141337365)
                ·
                  refine ⟨75809656242347444125189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1617272666503412141337365 75809656242347444125189)
                  ·
                    rfl

theorem cell23_1328749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 5, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 5, 1, 2, 1, 6].length) (baseStart_1328749 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1328749 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1328749 prefixEnd_1328749 := by exact prefixLift 1328749
  have htrace : WordTrace (prefixWord ++ tailWord_1328749) baseStart_1328749 baseEnd_1328749 := by
    simpa [prefixWord, tailWord_1328749, baseEnd_1328749] using wordTrace_append hprefix tailTrace_1328749
  have hstable : (prefixWord ++ tailWord_1328749).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1328749).length < 2 ^ (prefixWord ++ tailWord_1328749).sum := by decide
  have hdescent : baseEnd_1328749 < baseStart_1328749 := by decide
  rcases family_descends (prefixWord ++ tailWord_1328749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1328765 : List Nat := [1, 4, 1, 1, 4, 2, 1, 1, 3, 1, 4]
def baseStart_1328765 : Nat := 118140960795 + 1328765 * 2 ^ 59
def prefixEnd_1328765 : Nat := 4983230072969 + 3 ^ 40 * 1328765 * 2
def baseEnd_1328765 : Nat := 682295121871598934526627

theorem tailTrace_1328765 : CollatzResearch.WordTrace tailWord_1328765 prefixEnd_1328765 682295121871598934526627 := by
  unfold tailWord_1328765
  simp only [CollatzResearch.WordTrace]
  refine ⟨48464041031118814839891749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32309360687412543226594499 48464041031118814839891749)
  ·
    refine ⟨9087007693334777782479703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 48464041031118814839891749 9087007693334777782479703)
    ·
      refine ⟨13630511540002166673719555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9087007693334777782479703 13630511540002166673719555)
      ·
        refine ⟨20445767310003250010579333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13630511540002166673719555 20445767310003250010579333)
        ·
          refine ⟨3833581370625609376983625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 20445767310003250010579333 3833581370625609376983625)
          ·
            refine ⟨2875186027969207032737719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3833581370625609376983625 2875186027969207032737719)
            ·
              refine ⟨4312779041953810549106579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2875186027969207032737719 4312779041953810549106579)
              ·
                refine ⟨6469168562930715823659869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4312779041953810549106579 6469168562930715823659869)
                ·
                  refine ⟨2425938211099018433872451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6469168562930715823659869 2425938211099018433872451)
                  ·
                    refine ⟨3638907316648527650808677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2425938211099018433872451 3638907316648527650808677)
                    ·
                      refine ⟨682295121871598934526627, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3638907316648527650808677 682295121871598934526627)
                      ·
                        rfl

theorem cell23_1328765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 2, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 2, 1, 1, 3, 1, 4].length) (baseStart_1328765 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1328765 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1328765 prefixEnd_1328765 := by exact prefixLift 1328765
  have htrace : WordTrace (prefixWord ++ tailWord_1328765) baseStart_1328765 baseEnd_1328765 := by
    simpa [prefixWord, tailWord_1328765, baseEnd_1328765] using wordTrace_append hprefix tailTrace_1328765
  have hstable : (prefixWord ++ tailWord_1328765).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1328765).length < 2 ^ (prefixWord ++ tailWord_1328765).sum := by decide
  have hdescent : baseEnd_1328765 < baseStart_1328765 := by decide
  rcases family_descends (prefixWord ++ tailWord_1328765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1328788 : List Nat := [2, 4, 2, 2, 13]
def baseStart_1328788 : Nat := 118140960795 + 1328788 * 2 ^ 59
def prefixEnd_1328788 : Nat := 4983230072969 + 3 ^ 40 * 1328788 * 2
def baseEnd_1328788 : Nat := 935949152162760417749

theorem tailTrace_1328788 : CollatzResearch.WordTrace tailWord_1328788 prefixEnd_1328788 935949152162760417749 := by
  unfold tailWord_1328788
  simp only [CollatzResearch.WordTrace]
  refine ⟨24232439955017744883989509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32309919940023659845319345 24232439955017744883989509)
  ·
    refine ⟨4543582491565827165748033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 24232439955017744883989509 4543582491565827165748033)
    ·
      refine ⟨3407686868674370374311025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4543582491565827165748033 3407686868674370374311025)
      ·
        refine ⟨2555765151505777780733269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3407686868674370374311025 2555765151505777780733269)
        ·
          refine ⟨935949152162760417749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 13 2555765151505777780733269 935949152162760417749)
          ·
            rfl

theorem cell23_1328788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 13].length) (baseStart_1328788 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1328788 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1328788 prefixEnd_1328788 := by exact prefixLift 1328788
  have htrace : WordTrace (prefixWord ++ tailWord_1328788) baseStart_1328788 baseEnd_1328788 := by
    simpa [prefixWord, tailWord_1328788, baseEnd_1328788] using wordTrace_append hprefix tailTrace_1328788
  have hstable : (prefixWord ++ tailWord_1328788).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1328788).length < 2 ^ (prefixWord ++ tailWord_1328788).sum := by decide
  have hdescent : baseEnd_1328788 < baseStart_1328788 := by decide
  rcases family_descends (prefixWord ++ tailWord_1328788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1328792 : List Nat := [2, 1, 2, 4, 1, 3, 2, 2, 2, 4]
def baseStart_1328792 : Nat := 118140960795 + 1328792 * 2 ^ 59
def prefixEnd_1328792 : Nat := 4983230072969 + 3 ^ 40 * 1328792 * 2
def baseEnd_1328792 : Nat := 227436328616423442963001

theorem tailTrace_1328792 : CollatzResearch.WordTrace tailWord_1328792 prefixEnd_1328792 227436328616423442963001 := by
  unfold tailWord_1328792
  simp only [CollatzResearch.WordTrace]
  refine ⟨24232512901010499225562315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32310017201347332300749753 24232512901010499225562315)
  ·
    refine ⟨36348769351515748838343473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24232512901010499225562315 36348769351515748838343473)
    ·
      refine ⟨27261577013636811628757605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36348769351515748838343473 27261577013636811628757605)
      ·
        refine ⟨5111545690056902180392051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 27261577013636811628757605 5111545690056902180392051)
        ·
          refine ⟨7667318535085353270588077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5111545690056902180392051 7667318535085353270588077)
          ·
            refine ⟨2875244450657007476470529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7667318535085353270588077 2875244450657007476470529)
            ·
              refine ⟨2156433337992755607352897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2875244450657007476470529 2156433337992755607352897)
              ·
                refine ⟨1617325003494566705514673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2156433337992755607352897 1617325003494566705514673)
                ·
                  refine ⟨1212993752620925029136005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1617325003494566705514673 1212993752620925029136005)
                  ·
                    refine ⟨227436328616423442963001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1212993752620925029136005 227436328616423442963001)
                    ·
                      rfl

theorem cell23_1328792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 3, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 3, 2, 2, 2, 4].length) (baseStart_1328792 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1328792 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1328792 prefixEnd_1328792 := by exact prefixLift 1328792
  have htrace : WordTrace (prefixWord ++ tailWord_1328792) baseStart_1328792 baseEnd_1328792 := by
    simpa [prefixWord, tailWord_1328792, baseEnd_1328792] using wordTrace_append hprefix tailTrace_1328792
  have hstable : (prefixWord ++ tailWord_1328792).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1328792).length < 2 ^ (prefixWord ++ tailWord_1328792).sum := by decide
  have hdescent : baseEnd_1328792 < baseStart_1328792 := by decide
  rcases family_descends (prefixWord ++ tailWord_1328792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1328815 : List Nat := [1, 1, 2, 1, 2, 4, 4, 1, 1, 3, 3]
def baseStart_1328815 : Nat := 118140960795 + 1328815 * 2 ^ 59
def prefixEnd_1328815 : Nat := 4983230072969 + 3 ^ 40 * 1328815 * 2
def baseEnd_1328815 : Nat := 682320795904323738901397

theorem tailTrace_1328815 : CollatzResearch.WordTrace tailWord_1328815 prefixEnd_1328815 682320795904323738901397 := by
  unfold tailWord_1328815
  simp only [CollatzResearch.WordTrace]
  refine ⟨48465864680937673379211899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32310576453958448919474599 48465864680937673379211899)
  ·
    refine ⟨72698797021406510068817849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48465864680937673379211899 72698797021406510068817849)
    ·
      refine ⟨54524097766054882551613387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 72698797021406510068817849 54524097766054882551613387)
      ·
        refine ⟨81786146649082323827420081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54524097766054882551613387 81786146649082323827420081)
        ·
          refine ⟨61339609986811742870565061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 81786146649082323827420081 61339609986811742870565061)
          ·
            refine ⟨11501176872527201788230949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 61339609986811742870565061 11501176872527201788230949)
            ·
              refine ⟨2156470663598850335293303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11501176872527201788230949 2156470663598850335293303)
              ·
                refine ⟨3234705995398275502939955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2156470663598850335293303 3234705995398275502939955)
                ·
                  refine ⟨4852058993097413254409933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3234705995398275502939955 4852058993097413254409933)
                  ·
                    refine ⟨1819522122411529970403725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4852058993097413254409933 1819522122411529970403725)
                    ·
                      refine ⟨682320795904323738901397, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1819522122411529970403725 682320795904323738901397)
                      ·
                        rfl

theorem cell23_1328815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 4, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 4, 1, 1, 3, 3].length) (baseStart_1328815 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1328815 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1328815 prefixEnd_1328815 := by exact prefixLift 1328815
  have htrace : WordTrace (prefixWord ++ tailWord_1328815) baseStart_1328815 baseEnd_1328815 := by
    simpa [prefixWord, tailWord_1328815, baseEnd_1328815] using wordTrace_append hprefix tailTrace_1328815
  have hstable : (prefixWord ++ tailWord_1328815).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1328815).length < 2 ^ (prefixWord ++ tailWord_1328815).sum := by decide
  have hdescent : baseEnd_1328815 < baseStart_1328815 := by decide
  rcases family_descends (prefixWord ++ tailWord_1328815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1328849 : List Nat := [1, 2, 2, 1, 2, 6, 1, 2, 2, 1, 3]
def baseStart_1328849 : Nat := 118140960795 + 1328849 * 2 ^ 59
def prefixEnd_1328849 : Nat := 4983230072969 + 3 ^ 40 * 1328849 * 2
def baseEnd_1328849 : Nat := 682338254246576605876241

theorem tailTrace_1328849 : CollatzResearch.WordTrace tailWord_1328849 prefixEnd_1328849 682338254246576605876241 := by
  unfold tailWord_1328849
  simp only [CollatzResearch.WordTrace]
  refine ⟨48467104762814497185949601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32311403175209664790633067 48467104762814497185949601)
  ·
    refine ⟨36350328572110872889462201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48467104762814497185949601 36350328572110872889462201)
    ·
      refine ⟨27262746429083154667096651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36350328572110872889462201 27262746429083154667096651)
      ·
        refine ⟨40894119643624732000644977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27262746429083154667096651 40894119643624732000644977)
        ·
          refine ⟨30670589732718549000483733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40894119643624732000644977 30670589732718549000483733)
          ·
            refine ⟨1437683893721181984397675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 30670589732718549000483733 1437683893721181984397675)
            ·
              refine ⟨2156525840581772976596513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1437683893721181984397675 2156525840581772976596513)
              ·
                refine ⟨1617394380436329732447385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2156525840581772976596513 1617394380436329732447385)
                ·
                  refine ⟨1213045785327247299335539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1617394380436329732447385 1213045785327247299335539)
                  ·
                    refine ⟨1819568677990870949003309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1213045785327247299335539 1819568677990870949003309)
                    ·
                      refine ⟨682338254246576605876241, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1819568677990870949003309 682338254246576605876241)
                      ·
                        rfl

theorem cell23_1328849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 6, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 6, 1, 2, 2, 1, 3].length) (baseStart_1328849 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1328849 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1328849 prefixEnd_1328849 := by exact prefixLift 1328849
  have htrace : WordTrace (prefixWord ++ tailWord_1328849) baseStart_1328849 baseEnd_1328849 := by
    simpa [prefixWord, tailWord_1328849, baseEnd_1328849] using wordTrace_append hprefix tailTrace_1328849
  have hstable : (prefixWord ++ tailWord_1328849).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1328849).length < 2 ^ (prefixWord ++ tailWord_1328849).sum := by decide
  have hdescent : baseEnd_1328849 < baseStart_1328849 := by decide
  rcases family_descends (prefixWord ++ tailWord_1328849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1328966 : List Nat := [6, 1, 1, 2, 1, 1, 1, 1, 2, 5, 2]
def baseStart_1328966 : Nat := 118140960795 + 1328966 * 2 ^ 59
def prefixEnd_1328966 : Nat := 4983230072969 + 3 ^ 40 * 1328966 * 2
def baseEnd_1328966 : Nat := 682398331483152648113203

theorem tailTrace_1328966 : CollatzResearch.WordTrace tailWord_1328966 prefixEnd_1328966 682398331483152648113203 := by
  unfold tailWord_1328966
  simp only [CollatzResearch.WordTrace]
  refine ⟨1514730378230957067748711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 32314248068927084111972501 1514730378230957067748711)
  ·
    refine ⟨2272095567346435601623067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1514730378230957067748711 2272095567346435601623067)
    ·
      refine ⟨3408143351019653402434601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2272095567346435601623067 3408143351019653402434601)
      ·
        refine ⟨2556107513264740051825951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3408143351019653402434601 2556107513264740051825951)
        ·
          refine ⟨3834161269897110077738927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2556107513264740051825951 3834161269897110077738927)
          ·
            refine ⟨5751241904845665116608391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3834161269897110077738927 5751241904845665116608391)
            ·
              refine ⟨8626862857268497674912587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5751241904845665116608391 8626862857268497674912587)
              ·
                refine ⟨12940294285902746512368881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8626862857268497674912587 12940294285902746512368881)
                ·
                  refine ⟨9705220714427059884276661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12940294285902746512368881 9705220714427059884276661)
                  ·
                    refine ⟨909864441977536864150937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9705220714427059884276661 909864441977536864150937)
                    ·
                      refine ⟨682398331483152648113203, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 909864441977536864150937 682398331483152648113203)
                      ·
                        rfl

theorem cell23_1328966_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 1, 1, 2, 5, 2].length) (baseStart_1328966 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1328966 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1328966 prefixEnd_1328966 := by exact prefixLift 1328966
  have htrace : WordTrace (prefixWord ++ tailWord_1328966) baseStart_1328966 baseEnd_1328966 := by
    simpa [prefixWord, tailWord_1328966, baseEnd_1328966] using wordTrace_append hprefix tailTrace_1328966
  have hstable : (prefixWord ++ tailWord_1328966).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1328966).length < 2 ^ (prefixWord ++ tailWord_1328966).sum := by decide
  have hdescent : baseEnd_1328966 < baseStart_1328966 := by decide
  rcases family_descends (prefixWord ++ tailWord_1328966) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1328985 : List Nat := [1, 2, 1, 2, 2, 3, 1, 5, 6]
def baseStart_1328985 : Nat := 118140960795 + 1328985 * 2 ^ 59
def prefixEnd_1328985 : Nat := 4983230072969 + 3 ^ 40 * 1328985 * 2
def baseEnd_1328985 : Nat := 75823120846176452641735

theorem tailTrace_1328985 : CollatzResearch.WordTrace tailWord_1328985 prefixEnd_1328985 75823120846176452641735 := by
  unfold tailWord_1328985
  simp only [CollatzResearch.WordTrace]
  refine ⟨48472065090321792412900409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32314710060214528275266939 48472065090321792412900409)
  ·
    refine ⟨36354048817741344309675307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48472065090321792412900409 36354048817741344309675307)
    ·
      refine ⟨54531073226612016464512961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36354048817741344309675307 54531073226612016464512961)
      ·
        refine ⟨40898304919959012348384721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54531073226612016464512961 40898304919959012348384721)
        ·
          refine ⟨30673728689969259261288541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40898304919959012348384721 30673728689969259261288541)
          ·
            refine ⟨11502648258738472222983203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30673728689969259261288541 11502648258738472222983203)
            ·
              refine ⟨17253972388107708334474805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11502648258738472222983203 17253972388107708334474805)
              ·
                refine ⟨1617559911385097656357013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 17253972388107708334474805 1617559911385097656357013)
                ·
                  refine ⟨75823120846176452641735, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1617559911385097656357013 75823120846176452641735)
                  ·
                    rfl

theorem cell23_1328985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 1, 5, 6].length) (baseStart_1328985 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1328985 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1328985 prefixEnd_1328985 := by exact prefixLift 1328985
  have htrace : WordTrace (prefixWord ++ tailWord_1328985) baseStart_1328985 baseEnd_1328985 := by
    simpa [prefixWord, tailWord_1328985, baseEnd_1328985] using wordTrace_append hprefix tailTrace_1328985
  have hstable : (prefixWord ++ tailWord_1328985).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1328985).length < 2 ^ (prefixWord ++ tailWord_1328985).sum := by decide
  have hdescent : baseEnd_1328985 < baseStart_1328985 := by decide
  rcases family_descends (prefixWord ++ tailWord_1328985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1328996 : List Nat := [2, 3, 1, 1, 6, 1, 1, 1, 2, 1, 4]
def baseStart_1328996 : Nat := 118140960795 + 1328996 * 2 ^ 59
def prefixEnd_1328996 : Nat := 4983230072969 + 3 ^ 40 * 1328996 * 2
def baseEnd_1328996 : Nat := 682413735902787530738065

theorem tailTrace_1328996 : CollatzResearch.WordTrace tailWord_1328996 prefixEnd_1328996 682413735902787530738065 := by
  unfold tailWord_1328996
  simp only [CollatzResearch.WordTrace]
  refine ⟨24236233146640970645775421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32314977528854627527700561 24236233146640970645775421)
  ·
    refine ⟨9088587429990363992165783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24236233146640970645775421 9088587429990363992165783)
    ·
      refine ⟨13632881144985545988248675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9088587429990363992165783 13632881144985545988248675)
      ·
        refine ⟨20449321717478318982373013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13632881144985545988248675 20449321717478318982373013)
        ·
          refine ⟨958561955506796202298735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 20449321717478318982373013 958561955506796202298735)
          ·
            refine ⟨1437842933260194303448103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 958561955506796202298735 1437842933260194303448103)
            ·
              refine ⟨2156764399890291455172155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1437842933260194303448103 2156764399890291455172155)
              ·
                refine ⟨3235146599835437182758233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2156764399890291455172155 3235146599835437182758233)
                ·
                  refine ⟨2426359949876577887068675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3235146599835437182758233 2426359949876577887068675)
                  ·
                    refine ⟨3639539924814866830603013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2426359949876577887068675 3639539924814866830603013)
                    ·
                      refine ⟨682413735902787530738065, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3639539924814866830603013 682413735902787530738065)
                      ·
                        rfl

theorem cell23_1328996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 6, 1, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 6, 1, 1, 1, 2, 1, 4].length) (baseStart_1328996 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1328996 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1328996 prefixEnd_1328996 := by exact prefixLift 1328996
  have htrace : WordTrace (prefixWord ++ tailWord_1328996) baseStart_1328996 baseEnd_1328996 := by
    simpa [prefixWord, tailWord_1328996, baseEnd_1328996] using wordTrace_append hprefix tailTrace_1328996
  have hstable : (prefixWord ++ tailWord_1328996).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1328996).length < 2 ^ (prefixWord ++ tailWord_1328996).sum := by decide
  have hdescent : baseEnd_1328996 < baseStart_1328996 := by decide
  rcases family_descends (prefixWord ++ tailWord_1328996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1329006 : List Nat := [4, 1, 2, 3, 1, 1, 1, 5, 1, 4]
def baseStart_1329006 : Nat := 118140960795 + 1329006 * 2 ^ 59
def prefixEnd_1329006 : Nat := 4983230072969 + 3 ^ 40 * 1329006 * 2
def baseEnd_1329006 : Nat := 227472956903110830537673

theorem tailTrace_1329006 : CollatzResearch.WordTrace tailWord_1329006 prefixEnd_1329006 227472956903110830537673 := by
  unfold tailWord_1329006
  simp only [CollatzResearch.WordTrace]
  refine ⟨6059103877905714124926859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 32315220682163808666276581 6059103877905714124926859)
  ·
    refine ⟨9088655816858571187390289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6059103877905714124926859 9088655816858571187390289)
    ·
      refine ⟨6816491862643928390542717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9088655816858571187390289 6816491862643928390542717)
      ·
        refine ⟨2556184448491473146453519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6816491862643928390542717 2556184448491473146453519)
        ·
          refine ⟨3834276672737209719680279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2556184448491473146453519 3834276672737209719680279)
          ·
            refine ⟨5751415009105814579520419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3834276672737209719680279 5751415009105814579520419)
            ·
              refine ⟨8627122513658721869280629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5751415009105814579520419 8627122513658721869280629)
              ·
                refine ⟨808792735655505175245059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 8627122513658721869280629 808792735655505175245059)
                ·
                  refine ⟨1213189103483257762867589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 808792735655505175245059 1213189103483257762867589)
                  ·
                    refine ⟨227472956903110830537673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1213189103483257762867589 227472956903110830537673)
                    ·
                      rfl

theorem cell23_1329006_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 1, 5, 1, 4].length) (baseStart_1329006 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1329006 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1329006 prefixEnd_1329006 := by exact prefixLift 1329006
  have htrace : WordTrace (prefixWord ++ tailWord_1329006) baseStart_1329006 baseEnd_1329006 := by
    simpa [prefixWord, tailWord_1329006, baseEnd_1329006] using wordTrace_append hprefix tailTrace_1329006
  have hstable : (prefixWord ++ tailWord_1329006).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1329006).length < 2 ^ (prefixWord ++ tailWord_1329006).sum := by decide
  have hdescent : baseEnd_1329006 < baseStart_1329006 := by decide
  rcases family_descends (prefixWord ++ tailWord_1329006) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1329029 : List Nat := [1, 3, 1, 1, 3, 2, 4, 1, 3, 1, 3]
def baseStart_1329029 : Nat := 118140960795 + 1329029 * 2 ^ 59
def prefixEnd_1329029 : Nat := 4983230072969 + 3 ^ 40 * 1329029 * 2
def baseEnd_1329029 : Nat := 682430680764385901625413

theorem tailTrace_1329029 : CollatzResearch.WordTrace tailWord_1329029 prefixEnd_1329029 682430680764385901625413 := by
  unfold tailWord_1329029
  simp only [CollatzResearch.WordTrace]
  refine ⟨48473669902162387927502141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32315779934774925285001427 48473669902162387927502141)
  ·
    refine ⟨18177626213310895472813303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 48473669902162387927502141 18177626213310895472813303)
    ·
      refine ⟨27266439319966343209219955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18177626213310895472813303 27266439319966343209219955)
      ·
        refine ⟨40899658979949514813829933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27266439319966343209219955 40899658979949514813829933)
        ·
          refine ⟨15337372117481068055186225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 40899658979949514813829933 15337372117481068055186225)
          ·
            refine ⟨11503029088110801041389669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15337372117481068055186225 11503029088110801041389669)
            ·
              refine ⟨2156817954020775195260563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11503029088110801041389669 2156817954020775195260563)
              ·
                refine ⟨3235226931031162792890845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2156817954020775195260563 3235226931031162792890845)
                ·
                  refine ⟨1213210099136686047334067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3235226931031162792890845 1213210099136686047334067)
                  ·
                    refine ⟨1819815148705029071001101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1213210099136686047334067 1819815148705029071001101)
                    ·
                      refine ⟨682430680764385901625413, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1819815148705029071001101 682430680764385901625413)
                      ·
                        rfl

theorem cell23_1329029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 4, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 4, 1, 3, 1, 3].length) (baseStart_1329029 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1329029 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1329029 prefixEnd_1329029 := by exact prefixLift 1329029
  have htrace : WordTrace (prefixWord ++ tailWord_1329029) baseStart_1329029 baseEnd_1329029 := by
    simpa [prefixWord, tailWord_1329029, baseEnd_1329029] using wordTrace_append hprefix tailTrace_1329029
  have hstable : (prefixWord ++ tailWord_1329029).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1329029).length < 2 ^ (prefixWord ++ tailWord_1329029).sum := by decide
  have hdescent : baseEnd_1329029 < baseStart_1329029 := by decide
  rcases family_descends (prefixWord ++ tailWord_1329029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1329063 : List Nat := [1, 1, 6, 1, 2, 1, 3, 3, 1, 1, 3]
def baseStart_1329063 : Nat := 118140960795 + 1329063 * 2 ^ 59
def prefixEnd_1329063 : Nat := 4983230072969 + 3 ^ 40 * 1329063 * 2
def baseEnd_1329063 : Nat := 682448139106638768600257

theorem tailTrace_1329063 : CollatzResearch.WordTrace tailWord_1329063 prefixEnd_1329063 682448139106638768600257 := by
  unfold tailWord_1329063
  simp only [CollatzResearch.WordTrace]
  refine ⟨48474909984039211734239843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32316606656026141156159895 48474909984039211734239843)
  ·
    refine ⟨72712364976058817601359765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48474909984039211734239843 72712364976058817601359765)
    ·
      refine ⟨3408392108252757075063739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 72712364976058817601359765 3408392108252757075063739)
      ·
        refine ⟨5112588162379135612595609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3408392108252757075063739 5112588162379135612595609)
        ·
          refine ⟨3834441121784351709446707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5112588162379135612595609 3834441121784351709446707)
          ·
            refine ⟨5751661682676527564170061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3834441121784351709446707 5751661682676527564170061)
            ·
              refine ⟨2156873131003697836563773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5751661682676527564170061 2156873131003697836563773)
              ·
                refine ⟨808827424126386688711415, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2156873131003697836563773 808827424126386688711415)
                ·
                  refine ⟨1213241136189580033067123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 808827424126386688711415 1213241136189580033067123)
                  ·
                    refine ⟨1819861704284370049600685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1213241136189580033067123 1819861704284370049600685)
                    ·
                      refine ⟨682448139106638768600257, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1819861704284370049600685 682448139106638768600257)
                      ·
                        rfl

theorem cell23_1329063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 3, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 3, 3, 1, 1, 3].length) (baseStart_1329063 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1329063 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1329063 prefixEnd_1329063 := by exact prefixLift 1329063
  have htrace : WordTrace (prefixWord ++ tailWord_1329063) baseStart_1329063 baseEnd_1329063 := by
    simpa [prefixWord, tailWord_1329063, baseEnd_1329063] using wordTrace_append hprefix tailTrace_1329063
  have hstable : (prefixWord ++ tailWord_1329063).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1329063).length < 2 ^ (prefixWord ++ tailWord_1329063).sum := by decide
  have hdescent : baseEnd_1329063 < baseStart_1329063 := by decide
  rcases family_descends (prefixWord ++ tailWord_1329063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1329095 : List Nat := [1, 1, 4, 1, 1, 2, 1, 1, 1, 4, 6]
def baseStart_1329095 : Nat := 118140960795 + 1329095 * 2 ^ 59
def prefixEnd_1329095 : Nat := 4983230072969 + 3 ^ 40 * 1329095 * 2
def baseEnd_1329095 : Nat := 682464570487582643400109

theorem tailTrace_1329095 : CollatzResearch.WordTrace tailWord_1329095 prefixEnd_1329095 682464570487582643400109 := by
  unfold tailWord_1329095
  simp only [CollatzResearch.WordTrace]
  refine ⟨48476077119923281199404739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32317384746615520799603159 48476077119923281199404739)
  ·
    refine ⟨72714115679884921799107109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48476077119923281199404739 72714115679884921799107109)
    ·
      refine ⟨13633896689978422837332583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 72714115679884921799107109 13633896689978422837332583)
      ·
        refine ⟨20450845034967634255998875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13633896689978422837332583 20450845034967634255998875)
        ·
          refine ⟨30676267552451451383998313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20450845034967634255998875 30676267552451451383998313)
          ·
            refine ⟨23007200664338588537998735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30676267552451451383998313 23007200664338588537998735)
            ·
              refine ⟨34510800996507882806998103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23007200664338588537998735 34510800996507882806998103)
              ·
                refine ⟨51766201494761824210497155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34510800996507882806998103 51766201494761824210497155)
                ·
                  refine ⟨77649302242142736315745733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 51766201494761824210497155 77649302242142736315745733)
                  ·
                    refine ⟨14559244170401763059202325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 77649302242142736315745733 14559244170401763059202325)
                    ·
                      refine ⟨682464570487582643400109, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 14559244170401763059202325 682464570487582643400109)
                      ·
                        rfl

theorem cell23_1329095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 1, 1, 1, 4, 6].length) (baseStart_1329095 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1329095 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1329095 prefixEnd_1329095 := by exact prefixLift 1329095
  have htrace : WordTrace (prefixWord ++ tailWord_1329095) baseStart_1329095 baseEnd_1329095 := by
    simpa [prefixWord, tailWord_1329095, baseEnd_1329095] using wordTrace_append hprefix tailTrace_1329095
  have hstable : (prefixWord ++ tailWord_1329095).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1329095).length < 2 ^ (prefixWord ++ tailWord_1329095).sum := by decide
  have hdescent : baseEnd_1329095 < baseStart_1329095 := by decide
  rcases family_descends (prefixWord ++ tailWord_1329095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1329096 : List Nat := [2, 1, 3, 1, 4, 1, 4, 1, 2, 4]
def baseStart_1329096 : Nat := 118140960795 + 1329096 * 2 ^ 59
def prefixEnd_1329096 : Nat := 4983230072969 + 3 ^ 40 * 1329096 * 2
def baseEnd_1329096 : Nat := 227488361322745713162535

theorem tailTrace_1329096 : CollatzResearch.WordTrace tailWord_1329096 prefixEnd_1329096 227488361322745713162535 := by
  unfold tailWord_1329096
  simp only [CollatzResearch.WordTrace]
  refine ⟨24238056796459829185095571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32317409061946438913460761 24238056796459829185095571)
  ·
    refine ⟨36357085194689743777643357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24238056796459829185095571 36357085194689743777643357)
    ·
      refine ⟨13633906948008653916616259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 36357085194689743777643357 13633906948008653916616259)
      ·
        refine ⟨20450860422012980874924389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13633906948008653916616259 20450860422012980874924389)
        ·
          refine ⟨3834536329127433914048323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 20450860422012980874924389 3834536329127433914048323)
          ·
            refine ⟨5751804493691150871072485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3834536329127433914048323 5751804493691150871072485)
            ·
              refine ⟨1078463342567090788326091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5751804493691150871072485 1078463342567090788326091)
              ·
                refine ⟨1617695013850636182489137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1078463342567090788326091 1617695013850636182489137)
                ·
                  refine ⟨1213271260387977136866853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1617695013850636182489137 1213271260387977136866853)
                  ·
                    refine ⟨227488361322745713162535, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1213271260387977136866853 227488361322745713162535)
                    ·
                      rfl

theorem cell23_1329096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 4, 1, 2, 4].length) (baseStart_1329096 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1329096 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1329096 prefixEnd_1329096 := by exact prefixLift 1329096
  have htrace : WordTrace (prefixWord ++ tailWord_1329096) baseStart_1329096 baseEnd_1329096 := by
    simpa [prefixWord, tailWord_1329096, baseEnd_1329096] using wordTrace_append hprefix tailTrace_1329096
  have hstable : (prefixWord ++ tailWord_1329096).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1329096).length < 2 ^ (prefixWord ++ tailWord_1329096).sum := by decide
  have hdescent : baseEnd_1329096 < baseStart_1329096 := by decide
  rcases family_descends (prefixWord ++ tailWord_1329096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1329105 : List Nat := [1, 2, 2, 1, 2, 1, 2, 1, 4, 7]
def baseStart_1329105 : Nat := 118140960795 + 1329105 * 2 ^ 59
def prefixEnd_1329105 : Nat := 4983230072969 + 3 ^ 40 * 1329105 * 2
def baseEnd_1329105 : Nat := 227489901764709201425021

theorem tailTrace_1329105 : CollatzResearch.WordTrace tailWord_1329105 prefixEnd_1329105 227489901764709201425021 := by
  unfold tailWord_1329105
  simp only [CollatzResearch.WordTrace]
  refine ⟨48476441849887052907268769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32317627899924701938179179 48476441849887052907268769)
  ·
    refine ⟨36357331387415289680451577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48476441849887052907268769 36357331387415289680451577)
    ·
      refine ⟨27267998540561467260338683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36357331387415289680451577 27267998540561467260338683)
      ·
        refine ⟨40901997810842200890508025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27267998540561467260338683 40901997810842200890508025)
        ·
          refine ⟨30676498358131650667881019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40901997810842200890508025 30676498358131650667881019)
          ·
            refine ⟨46014747537197476001821529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30676498358131650667881019 46014747537197476001821529)
            ·
              refine ⟨34511060652898107001366147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 46014747537197476001821529 34511060652898107001366147)
              ·
                refine ⟨51766590979347160502049221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34511060652898107001366147 51766590979347160502049221)
                ·
                  refine ⟨9706235808627592594134229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 51766590979347160502049221 9706235808627592594134229)
                  ·
                    refine ⟨227489901764709201425021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 9706235808627592594134229 227489901764709201425021)
                    ·
                      rfl

theorem cell23_1329105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 2, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 2, 1, 4, 7].length) (baseStart_1329105 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1329105 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1329105 prefixEnd_1329105 := by exact prefixLift 1329105
  have htrace : WordTrace (prefixWord ++ tailWord_1329105) baseStart_1329105 baseEnd_1329105 := by
    simpa [prefixWord, tailWord_1329105, baseEnd_1329105] using wordTrace_append hprefix tailTrace_1329105
  have hstable : (prefixWord ++ tailWord_1329105).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1329105).length < 2 ^ (prefixWord ++ tailWord_1329105).sum := by decide
  have hdescent : baseEnd_1329105 < baseStart_1329105 := by decide
  rcases family_descends (prefixWord ++ tailWord_1329105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1329106 : List Nat := [3, 2, 2, 3, 2, 1, 1, 1, 3, 2, 3]
def baseStart_1329106 : Nat := 118140960795 + 1329106 * 2 ^ 59
def prefixEnd_1329106 : Nat := 4983230072969 + 3 ^ 40 * 1329106 * 2
def baseEnd_1329106 : Nat := 682470218774782100362559

theorem tailTrace_1329106 : CollatzResearch.WordTrace tailWord_1329106 prefixEnd_1329106 682470218774782100362559 := by
  unfold tailWord_1329106
  simp only [CollatzResearch.WordTrace]
  refine ⟨12119119580720857519513793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32317652215255620052036781 12119119580720857519513793)
  ·
    refine ⟨9089339685540643139635345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12119119580720857519513793 9089339685540643139635345)
    ·
      refine ⟨6817004764155482354726509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9089339685540643139635345 6817004764155482354726509)
      ·
        refine ⟨2556376786558305883022441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6817004764155482354726509 2556376786558305883022441)
        ·
          refine ⟨1917282589918729412266831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2556376786558305883022441 1917282589918729412266831)
          ·
            refine ⟨2875923884878094118400247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1917282589918729412266831 2875923884878094118400247)
            ·
              refine ⟨4313885827317141177600371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2875923884878094118400247 4313885827317141177600371)
              ·
                refine ⟨6470828740975711766400557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4313885827317141177600371 6470828740975711766400557)
                ·
                  refine ⟨2426560777865891912400209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6470828740975711766400557 2426560777865891912400209)
                  ·
                    refine ⟨1819920583399418934300157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2426560777865891912400209 1819920583399418934300157)
                    ·
                      refine ⟨682470218774782100362559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1819920583399418934300157 682470218774782100362559)
                      ·
                        rfl

theorem cell23_1329106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 2, 1, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 2, 1, 1, 1, 3, 2, 3].length) (baseStart_1329106 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1329106 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1329106 prefixEnd_1329106 := by exact prefixLift 1329106
  have htrace : WordTrace (prefixWord ++ tailWord_1329106) baseStart_1329106 baseEnd_1329106 := by
    simpa [prefixWord, tailWord_1329106, baseEnd_1329106] using wordTrace_append hprefix tailTrace_1329106
  have hstable : (prefixWord ++ tailWord_1329106).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1329106).length < 2 ^ (prefixWord ++ tailWord_1329106).sum := by decide
  have hdescent : baseEnd_1329106 < baseStart_1329106 := by decide
  rcases family_descends (prefixWord ++ tailWord_1329106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1329119 : List Nat := [1, 1, 2, 3, 4, 2, 1, 2, 1, 3, 3]
def baseStart_1329119 : Nat := 118140960795 + 1329119 * 2 ^ 59
def prefixEnd_1329119 : Nat := 4983230072969 + 3 ^ 40 * 1329119 * 2
def baseEnd_1329119 : Nat := 682476894023290549499999

theorem tailTrace_1329119 : CollatzResearch.WordTrace tailWord_1329119 prefixEnd_1329119 682476894023290549499999 := by
  unfold tailWord_1329119
  simp only [CollatzResearch.WordTrace]
  refine ⟨48476952471836333298278411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32317968314557555532185607 48476952471836333298278411)
  ·
    refine ⟨72715428707754499947417617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48476952471836333298278411 72715428707754499947417617)
    ·
      refine ⟨54536571530815874960563213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 72715428707754499947417617 54536571530815874960563213)
      ·
        refine ⟨20451214324055953110211205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 54536571530815874960563213 20451214324055953110211205)
        ·
          refine ⟨3834602685760491208164601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 20451214324055953110211205 3834602685760491208164601)
          ·
            refine ⟨2875952014320368406123451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3834602685760491208164601 2875952014320368406123451)
            ·
              refine ⟨4313928021480552609185177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2875952014320368406123451 4313928021480552609185177)
              ·
                refine ⟨3235446016110414456888883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4313928021480552609185177 3235446016110414456888883)
                ·
                  refine ⟨4853169024165621685333325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3235446016110414456888883 4853169024165621685333325)
                  ·
                    refine ⟨1819938384062108131999997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4853169024165621685333325 1819938384062108131999997)
                    ·
                      refine ⟨682476894023290549499999, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1819938384062108131999997 682476894023290549499999)
                      ·
                        rfl

theorem cell23_1329119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 2, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 2, 1, 2, 1, 3, 3].length) (baseStart_1329119 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1329119 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1329119 prefixEnd_1329119 := by exact prefixLift 1329119
  have htrace : WordTrace (prefixWord ++ tailWord_1329119) baseStart_1329119 baseEnd_1329119 := by
    simpa [prefixWord, tailWord_1329119, baseEnd_1329119] using wordTrace_append hprefix tailTrace_1329119
  have hstable : (prefixWord ++ tailWord_1329119).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1329119).length < 2 ^ (prefixWord ++ tailWord_1329119).sum := by decide
  have hdescent : baseEnd_1329119 < baseStart_1329119 := by decide
  rcases family_descends (prefixWord ++ tailWord_1329119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1329137 : List Nat := [1, 2, 2, 2, 5, 2, 2, 2, 1, 2, 2]
def baseStart_1329137 : Nat := 118140960795 + 1329137 * 2 ^ 59
def prefixEnd_1329137 : Nat := 4983230072969 + 3 ^ 40 * 1329137 * 2
def baseEnd_1329137 : Nat := 682486136675071479074917

theorem tailTrace_1329137 : CollatzResearch.WordTrace tailWord_1329137 prefixEnd_1329137 682486136675071479074917 := by
  unfold tailWord_1329137
  simp only [CollatzResearch.WordTrace]
  refine ⟨48477608985771122372433665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32318405990514081581622443 48477608985771122372433665)
  ·
    refine ⟨36358206739328341779325249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48477608985771122372433665 36358206739328341779325249)
    ·
      refine ⟨27268655054496256334493937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36358206739328341779325249 27268655054496256334493937)
      ·
        refine ⟨20451491290872192250870453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27268655054496256334493937 20451491290872192250870453)
        ·
          refine ⟨1917327308519268023519105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 20451491290872192250870453 1917327308519268023519105)
          ·
            refine ⟨1437995481389451017639329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1917327308519268023519105 1437995481389451017639329)
            ·
              refine ⟨1078496611042088263229497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1437995481389451017639329 1078496611042088263229497)
              ·
                refine ⟨808872458281566197422123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1078496611042088263229497 808872458281566197422123)
                ·
                  refine ⟨1213308687422349296133185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 808872458281566197422123 1213308687422349296133185)
                  ·
                    refine ⟨909981515566761972099889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1213308687422349296133185 909981515566761972099889)
                    ·
                      refine ⟨682486136675071479074917, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 909981515566761972099889 682486136675071479074917)
                      ·
                        rfl

theorem cell23_1329137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 5, 2, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 5, 2, 2, 2, 1, 2, 2].length) (baseStart_1329137 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1329137 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1329137 prefixEnd_1329137 := by exact prefixLift 1329137
  have htrace : WordTrace (prefixWord ++ tailWord_1329137) baseStart_1329137 baseEnd_1329137 := by
    simpa [prefixWord, tailWord_1329137, baseEnd_1329137] using wordTrace_append hprefix tailTrace_1329137
  have hstable : (prefixWord ++ tailWord_1329137).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1329137).length < 2 ^ (prefixWord ++ tailWord_1329137).sum := by decide
  have hdescent : baseEnd_1329137 < baseStart_1329137 := by decide
  rcases family_descends (prefixWord ++ tailWord_1329137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1329176 : List Nat := [2, 1, 2, 3, 2, 1, 2, 2, 4, 2, 2]
def baseStart_1329176 : Nat := 118140960795 + 1329176 * 2 ^ 59
def prefixEnd_1329176 : Nat := 4983230072969 + 3 ^ 40 * 1329176 * 2
def baseEnd_1329176 : Nat := 682506162420596826487237

theorem tailTrace_1329176 : CollatzResearch.WordTrace tailWord_1329176 prefixEnd_1329176 682506162420596826487237 := by
  unfold tailWord_1329176
  simp only [CollatzResearch.WordTrace]
  refine ⟨24239515716314916016551691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32319354288419888022068921 24239515716314916016551691)
  ·
    refine ⟨36359273574472374024827537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24239515716314916016551691 36359273574472374024827537)
    ·
      refine ⟨27269455180854280518620653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36359273574472374024827537 27269455180854280518620653)
      ·
        refine ⟨10226045692820355194482745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27269455180854280518620653 10226045692820355194482745)
        ·
          refine ⟨7669534269615266395862059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10226045692820355194482745 7669534269615266395862059)
          ·
            refine ⟨11504301404422899593793089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7669534269615266395862059 11504301404422899593793089)
            ·
              refine ⟨8628226053317174695344817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11504301404422899593793089 8628226053317174695344817)
              ·
                refine ⟨6471169539987881021508613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8628226053317174695344817 6471169539987881021508613)
                ·
                  refine ⟨1213344288747727691532865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6471169539987881021508613 1213344288747727691532865)
                  ·
                    refine ⟨910008216560795768649649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1213344288747727691532865 910008216560795768649649)
                    ·
                      refine ⟨682506162420596826487237, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 910008216560795768649649 682506162420596826487237)
                      ·
                        rfl

theorem cell23_1329176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 2, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 2, 2, 4, 2, 2].length) (baseStart_1329176 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1329176 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1329176 prefixEnd_1329176 := by exact prefixLift 1329176
  have htrace : WordTrace (prefixWord ++ tailWord_1329176) baseStart_1329176 baseEnd_1329176 := by
    simpa [prefixWord, tailWord_1329176, baseEnd_1329176] using wordTrace_append hprefix tailTrace_1329176
  have hstable : (prefixWord ++ tailWord_1329176).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1329176).length < 2 ^ (prefixWord ++ tailWord_1329176).sum := by decide
  have hdescent : baseEnd_1329176 < baseStart_1329176 := by decide
  rcases family_descends (prefixWord ++ tailWord_1329176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1329180 : List Nat := [2, 2, 3, 1, 3, 3, 2, 1, 1, 3, 2]
def baseStart_1329180 : Nat := 118140960795 + 1329180 * 2 ^ 59
def prefixEnd_1329180 : Nat := 4983230072969 + 3 ^ 40 * 1329180 * 2
def baseEnd_1329180 : Nat := 682508216343214810837219

theorem tailTrace_1329180 : CollatzResearch.WordTrace tailWord_1329180 prefixEnd_1329180 682508216343214810837219 := by
  unfold tailWord_1329180
  simp only [CollatzResearch.WordTrace]
  refine ⟨24239588662307670358124497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32319451549743560477499329 24239588662307670358124497)
  ·
    refine ⟨18179691496730752768593373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24239588662307670358124497 18179691496730752768593373)
    ·
      refine ⟨6817384311274032288222515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18179691496730752768593373 6817384311274032288222515)
      ·
        refine ⟨10226076466911048432333773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6817384311274032288222515 10226076466911048432333773)
        ·
          refine ⟨3834778675091643162125165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10226076466911048432333773 3834778675091643162125165)
          ·
            refine ⟨1438042003159366185796937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3834778675091643162125165 1438042003159366185796937)
            ·
              refine ⟨1078531502369524639347703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1438042003159366185796937 1078531502369524639347703)
              ·
                refine ⟨1617797253554286959021555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1078531502369524639347703 1617797253554286959021555)
                ·
                  refine ⟨2426695880331430438532333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1617797253554286959021555 2426695880331430438532333)
                  ·
                    refine ⟨910010955124286414449625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2426695880331430438532333 910010955124286414449625)
                    ·
                      refine ⟨682508216343214810837219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 910010955124286414449625 682508216343214810837219)
                      ·
                        rfl

theorem cell23_1329180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 3, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 3, 2, 1, 1, 3, 2].length) (baseStart_1329180 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1329180 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1329180 prefixEnd_1329180 := by exact prefixLift 1329180
  have htrace : WordTrace (prefixWord ++ tailWord_1329180) baseStart_1329180 baseEnd_1329180 := by
    simpa [prefixWord, tailWord_1329180, baseEnd_1329180] using wordTrace_append hprefix tailTrace_1329180
  have hstable : (prefixWord ++ tailWord_1329180).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1329180).length < 2 ^ (prefixWord ++ tailWord_1329180).sum := by decide
  have hdescent : baseEnd_1329180 < baseStart_1329180 := by decide
  rcases family_descends (prefixWord ++ tailWord_1329180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1329212 : List Nat := [2, 2, 2, 2, 2, 1, 1, 1, 3, 7]
def baseStart_1329212 : Nat := 118140960795 + 1329212 * 2 ^ 59
def prefixEnd_1329212 : Nat := 4983230072969 + 3 ^ 40 * 1329212 * 2
def baseEnd_1329212 : Nat := 227508215908052895212357

theorem tailTrace_1329212 : CollatzResearch.WordTrace tailWord_1329212 prefixEnd_1329212 227508215908052895212357 := by
  unfold tailWord_1329212
  simp only [CollatzResearch.WordTrace]
  refine ⟨24240172230249705090706945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32320229640332940120942593 24240172230249705090706945)
  ·
    refine ⟨18180129172687278818030209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24240172230249705090706945 18180129172687278818030209)
    ·
      refine ⟨13635096879515459113522657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18180129172687278818030209 13635096879515459113522657)
      ·
        refine ⟨10226322659636594335141993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13635096879515459113522657 10226322659636594335141993)
        ·
          refine ⟨7669741994727445751356495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10226322659636594335141993 7669741994727445751356495)
          ·
            refine ⟨11504612992091168627034743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7669741994727445751356495 11504612992091168627034743)
            ·
              refine ⟨17256919488136752940552115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11504612992091168627034743 17256919488136752940552115)
              ·
                refine ⟨25885379232205129410828173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17256919488136752940552115 25885379232205129410828173)
                ·
                  refine ⟨9707017212076923529060565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25885379232205129410828173 9707017212076923529060565)
                  ·
                    refine ⟨227508215908052895212357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 9707017212076923529060565 227508215908052895212357)
                    ·
                      rfl

theorem cell23_1329212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 1, 1, 3, 7].length) (baseStart_1329212 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1329212 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1329212 prefixEnd_1329212 := by exact prefixLift 1329212
  have htrace : WordTrace (prefixWord ++ tailWord_1329212) baseStart_1329212 baseEnd_1329212 := by
    simpa [prefixWord, tailWord_1329212, baseEnd_1329212] using wordTrace_append hprefix tailTrace_1329212
  have hstable : (prefixWord ++ tailWord_1329212).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1329212).length < 2 ^ (prefixWord ++ tailWord_1329212).sum := by decide
  have hdescent : baseEnd_1329212 < baseStart_1329212 := by decide
  rcases family_descends (prefixWord ++ tailWord_1329212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1329229 : List Nat := [1, 6, 1, 1, 1, 1, 1, 3, 1, 7]
def baseStart_1329229 : Nat := 118140960795 + 1329229 * 2 ^ 59
def prefixEnd_1329229 : Nat := 4983230072969 + 3 ^ 40 * 1329229 * 2
def baseEnd_1329229 : Nat := 227511125631761706374831

theorem tailTrace_1329229 : CollatzResearch.WordTrace tailWord_1329229 prefixEnd_1329229 227511125631761706374831 := by
  unfold tailWord_1329229
  simp only [CollatzResearch.WordTrace]
  refine ⟨48480964501437822084782741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32320643000958548056521827 48480964501437822084782741)
  ·
    refine ⟨2272545211004897910224191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 48480964501437822084782741 2272545211004897910224191)
    ·
      refine ⟨3408817816507346865336287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2272545211004897910224191 3408817816507346865336287)
      ·
        refine ⟨5113226724761020298004431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3408817816507346865336287 5113226724761020298004431)
        ·
          refine ⟨7669840087141530447006647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5113226724761020298004431 7669840087141530447006647)
          ·
            refine ⟨11504760130712295670509971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7669840087141530447006647 11504760130712295670509971)
            ·
              refine ⟨17257140196068443505764957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11504760130712295670509971 17257140196068443505764957)
              ·
                refine ⟨6471427573525666314661859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17257140196068443505764957 6471427573525666314661859)
                ·
                  refine ⟨9707141360288499471992789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6471427573525666314661859 9707141360288499471992789)
                  ·
                    refine ⟨227511125631761706374831, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 9707141360288499471992789 227511125631761706374831)
                    ·
                      rfl

theorem cell23_1329229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 1, 3, 1, 7].length) (baseStart_1329229 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1329229 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1329229 prefixEnd_1329229 := by exact prefixLift 1329229
  have htrace : WordTrace (prefixWord ++ tailWord_1329229) baseStart_1329229 baseEnd_1329229 := by
    simpa [prefixWord, tailWord_1329229, baseEnd_1329229] using wordTrace_append hprefix tailTrace_1329229
  have hstable : (prefixWord ++ tailWord_1329229).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1329229).length < 2 ^ (prefixWord ++ tailWord_1329229).sum := by decide
  have hdescent : baseEnd_1329229 < baseStart_1329229 := by decide
  rcases family_descends (prefixWord ++ tailWord_1329229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1329250 : List Nat := [3, 3, 2, 2, 2, 1, 3, 2, 5]
def baseStart_1329250 : Nat := 118140960795 + 1329250 * 2 ^ 59
def prefixEnd_1329250 : Nat := 4983230072969 + 3 ^ 40 * 1329250 * 2
def baseEnd_1329250 : Nat := 75838239998781059662433

theorem tailTrace_1329250 : CollatzResearch.WordTrace tailWord_1329250 prefixEnd_1329250 75838239998781059662433 := by
  unfold tailWord_1329250
  simp only [CollatzResearch.WordTrace]
  refine ⟨12120432608590435667824301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32321153622907828447531469 12120432608590435667824301)
  ·
    refine ⟨4545162228221413375434113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12120432608590435667824301 4545162228221413375434113)
    ·
      refine ⟨3408871671166060031575585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4545162228221413375434113 3408871671166060031575585)
      ·
        refine ⟨2556653753374545023681689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3408871671166060031575585 2556653753374545023681689)
        ·
          refine ⟨1917490315030908767761267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2556653753374545023681689 1917490315030908767761267)
          ·
            refine ⟨2876235472546363151641901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1917490315030908767761267 2876235472546363151641901)
            ·
              refine ⟨1078588302204886181865713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2876235472546363151641901 1078588302204886181865713)
              ·
                refine ⟨808941226653664636399285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1078588302204886181865713 808941226653664636399285)
                ·
                  refine ⟨75838239998781059662433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 808941226653664636399285 75838239998781059662433)
                  ·
                    rfl

theorem cell23_1329250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 2, 1, 3, 2, 5].length) (baseStart_1329250 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1329250 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1329250 prefixEnd_1329250 := by exact prefixLift 1329250
  have htrace : WordTrace (prefixWord ++ tailWord_1329250) baseStart_1329250 baseEnd_1329250 := by
    simpa [prefixWord, tailWord_1329250, baseEnd_1329250] using wordTrace_append hprefix tailTrace_1329250
  have hstable : (prefixWord ++ tailWord_1329250).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1329250).length < 2 ^ (prefixWord ++ tailWord_1329250).sum := by decide
  have hdescent : baseEnd_1329250 < baseStart_1329250 := by decide
  rcases family_descends (prefixWord ++ tailWord_1329250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1329292 : List Nat := [2, 2, 1, 2, 1, 1, 1, 1, 3, 1, 8]
def baseStart_1329292 : Nat := 118140960795 + 1329292 * 2 ^ 59
def prefixEnd_1329292 : Nat := 4983230072969 + 3 ^ 40 * 1329292 * 2
def baseEnd_1329292 : Nat := 682565726176518372636703

theorem tailTrace_1329292 : CollatzResearch.WordTrace tailWord_1329292 prefixEnd_1329292 682565726176518372636703 := by
  unfold tailWord_1329292
  simp only [CollatzResearch.WordTrace]
  refine ⟨24241631150104791922163065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32322174866806389229550753 24241631150104791922163065)
  ·
    refine ⟨18181223362578593941622299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24241631150104791922163065 18181223362578593941622299)
    ·
      refine ⟨27271835043867890912433449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18181223362578593941622299 27271835043867890912433449)
      ·
        refine ⟨20453876282900918184325087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27271835043867890912433449 20453876282900918184325087)
        ·
          refine ⟨30680814424351377276487631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20453876282900918184325087 30680814424351377276487631)
          ·
            refine ⟨46021221636527065914731447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30680814424351377276487631 46021221636527065914731447)
            ·
              refine ⟨69031832454790598872097171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46021221636527065914731447 69031832454790598872097171)
              ·
                refine ⟨103547748682185898308145757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 69031832454790598872097171 103547748682185898308145757)
                ·
                  refine ⟨38830405755819711865554659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 103547748682185898308145757 38830405755819711865554659)
                  ·
                    refine ⟨58245608633729567798331989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 38830405755819711865554659 58245608633729567798331989)
                    ·
                      refine ⟨682565726176518372636703, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 58245608633729567798331989 682565726176518372636703)
                      ·
                        rfl

theorem cell23_1329292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 1, 3, 1, 8].length) (baseStart_1329292 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1329292 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1329292 prefixEnd_1329292 := by exact prefixLift 1329292
  have htrace : WordTrace (prefixWord ++ tailWord_1329292) baseStart_1329292 baseEnd_1329292 := by
    simpa [prefixWord, tailWord_1329292, baseEnd_1329292] using wordTrace_append hprefix tailTrace_1329292
  have hstable : (prefixWord ++ tailWord_1329292).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1329292).length < 2 ^ (prefixWord ++ tailWord_1329292).sum := by decide
  have hdescent : baseEnd_1329292 < baseStart_1329292 := by decide
  rcases family_descends (prefixWord ++ tailWord_1329292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1329339 : List Nat := [1, 1, 1, 1, 1, 2, 5, 3, 3, 1, 4]
def baseStart_1329339 : Nat := 118140960795 + 1329339 * 2 ^ 59
def prefixEnd_1329339 : Nat := 4983230072969 + 3 ^ 40 * 1329339 * 2
def baseEnd_1329339 : Nat := 682589859767279688748987

theorem tailTrace_1329339 : CollatzResearch.WordTrace tailWord_1329339 prefixEnd_1329339 682589859767279688748987 := by
  unfold tailWord_1329339
  simp only [CollatzResearch.WordTrace]
  refine ⟨48484976531039310871287071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32323317687359540580858047 48484976531039310871287071)
  ·
    refine ⟨72727464796558966306930607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48484976531039310871287071 72727464796558966306930607)
    ·
      refine ⟨109091197194838449460395911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72727464796558966306930607 109091197194838449460395911)
      ·
        refine ⟨163636795792257674190593867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 109091197194838449460395911 163636795792257674190593867)
        ·
          refine ⟨245455193688386511285890801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 163636795792257674190593867 245455193688386511285890801)
          ·
            refine ⟨184091395266289883464418101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 245455193688386511285890801 184091395266289883464418101)
            ·
              refine ⟨17258568306214676574789197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 184091395266289883464418101 17258568306214676574789197)
              ·
                refine ⟨6471963114830503715545949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17258568306214676574789197 6471963114830503715545949)
                ·
                  refine ⟨2426986168061438893329731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6471963114830503715545949 2426986168061438893329731)
                  ·
                    refine ⟨3640479252092158339994597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2426986168061438893329731 3640479252092158339994597)
                    ·
                      refine ⟨682589859767279688748987, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3640479252092158339994597 682589859767279688748987)
                      ·
                        rfl

theorem cell23_1329339_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 5, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 5, 3, 3, 1, 4].length) (baseStart_1329339 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1329339 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1329339 prefixEnd_1329339 := by exact prefixLift 1329339
  have htrace : WordTrace (prefixWord ++ tailWord_1329339) baseStart_1329339 baseEnd_1329339 := by
    simpa [prefixWord, tailWord_1329339, baseEnd_1329339] using wordTrace_append hprefix tailTrace_1329339
  have hstable : (prefixWord ++ tailWord_1329339).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1329339).length < 2 ^ (prefixWord ++ tailWord_1329339).sum := by decide
  have hdescent : baseEnd_1329339 < baseStart_1329339 := by decide
  rcases family_descends (prefixWord ++ tailWord_1329339) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1329349 : List Nat := [1, 3, 1, 1, 1, 1, 6, 2, 1, 6]
def baseStart_1329349 : Nat := 118140960795 + 1329349 * 2 ^ 59
def prefixEnd_1329349 : Nat := 4983230072969 + 3 ^ 40 * 1329349 * 2
def baseEnd_1329349 : Nat := 227531664857941549874647

theorem tailTrace_1329349 : CollatzResearch.WordTrace tailWord_1329349 prefixEnd_1329349 227531664857941549874647 := by
  unfold tailWord_1329349
  simp only [CollatzResearch.WordTrace]
  refine ⟨48485341261003082579151101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32323560840668721719434067 48485341261003082579151101)
  ·
    refine ⟨18182002972876155967181663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 48485341261003082579151101 18182002972876155967181663)
    ·
      refine ⟨27273004459314233950772495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18182002972876155967181663 27273004459314233950772495)
      ·
        refine ⟨40909506688971350926158743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27273004459314233950772495 40909506688971350926158743)
        ·
          refine ⟨61364260033457026389238115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40909506688971350926158743 61364260033457026389238115)
          ·
            refine ⟨92046390050185539583857173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61364260033457026389238115 92046390050185539583857173)
            ·
              refine ⟨4314674533602447167993305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 92046390050185539583857173 4314674533602447167993305)
              ·
                refine ⟨3236005900201835375994979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4314674533602447167993305 3236005900201835375994979)
                ·
                  refine ⟨4854008850302753063992469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3236005900201835375994979 4854008850302753063992469)
                  ·
                    refine ⟨227531664857941549874647, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4854008850302753063992469 227531664857941549874647)
                    ·
                      rfl

theorem cell23_1329349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 6, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 6, 2, 1, 6].length) (baseStart_1329349 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1329349 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1329349 prefixEnd_1329349 := by exact prefixLift 1329349
  have htrace : WordTrace (prefixWord ++ tailWord_1329349) baseStart_1329349 baseEnd_1329349 := by
    simpa [prefixWord, tailWord_1329349, baseEnd_1329349] using wordTrace_append hprefix tailTrace_1329349
  have hstable : (prefixWord ++ tailWord_1329349).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1329349).length < 2 ^ (prefixWord ++ tailWord_1329349).sum := by decide
  have hdescent : baseEnd_1329349 < baseStart_1329349 := by decide
  rcases family_descends (prefixWord ++ tailWord_1329349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1329359 : List Nat := [1, 1, 2, 1, 1, 3, 4, 3, 1, 1, 5]
def baseStart_1329359 : Nat := 118140960795 + 1329359 * 2 ^ 59
def prefixEnd_1329359 : Nat := 4983230072969 + 3 ^ 40 * 1329359 * 2
def baseEnd_1329359 : Nat := 682600129380369610498895

theorem tailTrace_1329359 : CollatzResearch.WordTrace tailWord_1329359 prefixEnd_1329359 682600129380369610498895 := by
  unfold tailWord_1329359
  simp only [CollatzResearch.WordTrace]
  refine ⟨48485705990966854287015131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32323803993977902858010087 48485705990966854287015131)
  ·
    refine ⟨72728558986450281430522697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48485705990966854287015131 72728558986450281430522697)
    ·
      refine ⟨54546419239837711072892023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 72728558986450281430522697 54546419239837711072892023)
      ·
        refine ⟨81819628859756566609338035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54546419239837711072892023 81819628859756566609338035)
        ·
          refine ⟨122729443289634849914007053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 81819628859756566609338035 122729443289634849914007053)
          ·
            refine ⟨46023541233613068717752645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 122729443289634849914007053 46023541233613068717752645)
            ·
              refine ⟨8629413981302450384578621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 46023541233613068717752645 8629413981302450384578621)
              ·
                refine ⟨3236030242988418894216983, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8629413981302450384578621 3236030242988418894216983)
                ·
                  refine ⟨4854045364482628341325475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3236030242988418894216983 4854045364482628341325475)
                  ·
                    refine ⟨7281068046723942511988213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4854045364482628341325475 7281068046723942511988213)
                    ·
                      refine ⟨682600129380369610498895, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7281068046723942511988213 682600129380369610498895)
                      ·
                        rfl

theorem cell23_1329359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 4, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 4, 3, 1, 1, 5].length) (baseStart_1329359 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1329359 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1329359 prefixEnd_1329359 := by exact prefixLift 1329359
  have htrace : WordTrace (prefixWord ++ tailWord_1329359) baseStart_1329359 baseEnd_1329359 := by
    simpa [prefixWord, tailWord_1329359, baseEnd_1329359] using wordTrace_append hprefix tailTrace_1329359
  have hstable : (prefixWord ++ tailWord_1329359).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1329359).length < 2 ^ (prefixWord ++ tailWord_1329359).sum := by decide
  have hdescent : baseEnd_1329359 < baseStart_1329359 := by decide
  rcases family_descends (prefixWord ++ tailWord_1329359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1329369 : List Nat := [1, 2, 1, 2, 3, 1, 2, 2, 3, 2, 4]
def baseStart_1329369 : Nat := 118140960795 + 1329369 * 2 ^ 59
def prefixEnd_1329369 : Nat := 4983230072969 + 3 ^ 40 * 1329369 * 2
def baseEnd_1329369 : Nat := 682605264186914571373849

theorem tailTrace_1329369 : CollatzResearch.WordTrace tailWord_1329369 prefixEnd_1329369 682605264186914571373849 := by
  unfold tailWord_1329369
  simp only [CollatzResearch.WordTrace]
  refine ⟨48486070720930625994879161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32324047147287083996586107 48486070720930625994879161)
  ·
    refine ⟨36364553040697969496159371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48486070720930625994879161 36364553040697969496159371)
    ·
      refine ⟨54546829561046954244239057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36364553040697969496159371 54546829561046954244239057)
      ·
        refine ⟨40910122170785215683179293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54546829561046954244239057 40910122170785215683179293)
        ·
          refine ⟨15341295814044455881192235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 40910122170785215683179293 15341295814044455881192235)
          ·
            refine ⟨23011943721066683821788353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15341295814044455881192235 23011943721066683821788353)
            ·
              refine ⟨17258957790800012866341265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23011943721066683821788353 17258957790800012866341265)
              ·
                refine ⟨12944218343100009649755949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17258957790800012866341265 12944218343100009649755949)
                ·
                  refine ⟨4854081878662503618658481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12944218343100009649755949 4854081878662503618658481)
                  ·
                    refine ⟨3640561408996877713993861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4854081878662503618658481 3640561408996877713993861)
                    ·
                      refine ⟨682605264186914571373849, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3640561408996877713993861 682605264186914571373849)
                      ·
                        rfl

theorem cell23_1329369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 2, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 2, 2, 3, 2, 4].length) (baseStart_1329369 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1329369 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1329369 prefixEnd_1329369 := by exact prefixLift 1329369
  have htrace : WordTrace (prefixWord ++ tailWord_1329369) baseStart_1329369 baseEnd_1329369 := by
    simpa [prefixWord, tailWord_1329369, baseEnd_1329369] using wordTrace_append hprefix tailTrace_1329369
  have hstable : (prefixWord ++ tailWord_1329369).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1329369).length < 2 ^ (prefixWord ++ tailWord_1329369).sum := by decide
  have hdescent : baseEnd_1329369 < baseStart_1329369 := by decide
  rcases family_descends (prefixWord ++ tailWord_1329369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1329383 : List Nat := [1, 1, 5, 3, 1, 3, 1, 1, 1, 6]
def baseStart_1329383 : Nat := 118140960795 + 1329383 * 2 ^ 59
def prefixEnd_1329383 : Nat := 4983230072969 + 3 ^ 40 * 1329383 * 2
def baseEnd_1329383 : Nat := 227537484305359172199595

theorem tailTrace_1329383 : CollatzResearch.WordTrace tailWord_1329383 prefixEnd_1329383 227537484305359172199595 := by
  unfold tailWord_1329383
  simp only [CollatzResearch.WordTrace]
  refine ⟨48486581342879906385888803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32324387561919937590592535 48486581342879906385888803)
  ·
    refine ⟨72729872014319859578833205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48486581342879906385888803 72729872014319859578833205)
    ·
      refine ⟨6818425501342486835515613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 72729872014319859578833205 6818425501342486835515613)
      ·
        refine ⟨2556909563003432563318355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6818425501342486835515613 2556909563003432563318355)
        ·
          refine ⟨3835364344505148844977533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2556909563003432563318355 3835364344505148844977533)
          ·
            refine ⟨1438261629189430816866575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3835364344505148844977533 1438261629189430816866575)
            ·
              refine ⟨2157392443784146225299863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1438261629189430816866575 2157392443784146225299863)
              ·
                refine ⟨3236088665676219337949795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2157392443784146225299863 3236088665676219337949795)
                ·
                  refine ⟨4854132998514329006924693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3236088665676219337949795 4854132998514329006924693)
                  ·
                    refine ⟨227537484305359172199595, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4854132998514329006924693 227537484305359172199595)
                    ·
                      rfl

theorem cell23_1329383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 3, 1, 1, 1, 6].length) (baseStart_1329383 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1329383 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1329383 prefixEnd_1329383 := by exact prefixLift 1329383
  have htrace : WordTrace (prefixWord ++ tailWord_1329383) baseStart_1329383 baseEnd_1329383 := by
    simpa [prefixWord, tailWord_1329383, baseEnd_1329383] using wordTrace_append hprefix tailTrace_1329383
  have hstable : (prefixWord ++ tailWord_1329383).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1329383).length < 2 ^ (prefixWord ++ tailWord_1329383).sum := by decide
  have hdescent : baseEnd_1329383 < baseStart_1329383 := by decide
  rcases family_descends (prefixWord ++ tailWord_1329383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1329410 : List Nat := [3, 4, 1, 1, 2, 1, 2, 3, 1, 2, 3]
def baseStart_1329410 : Nat := 118140960795 + 1329410 * 2 ^ 59
def prefixEnd_1329410 : Nat := 4983230072969 + 3 ^ 40 * 1329410 * 2
def baseEnd_1329410 : Nat := 682626316893748910961161

theorem tailTrace_1329410 : CollatzResearch.WordTrace tailWord_1329410 prefixEnd_1329410 682626316893748910961161 := by
  unfold tailWord_1329410
  simp only [CollatzResearch.WordTrace]
  refine ⟨12121891528445522499280421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32325044075854726664747789 12121891528445522499280421)
  ·
    refine ⟨2272854661583535468615079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 12121891528445522499280421 2272854661583535468615079)
    ·
      refine ⟨3409281992375303202922619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2272854661583535468615079 3409281992375303202922619)
      ·
        refine ⟨5113922988562954804383929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3409281992375303202922619 5113922988562954804383929)
        ·
          refine ⟨3835442241422216103287947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5113922988562954804383929 3835442241422216103287947)
          ·
            refine ⟨5753163362133324154931921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3835442241422216103287947 5753163362133324154931921)
            ·
              refine ⟨4314872521599993116198941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5753163362133324154931921 4314872521599993116198941)
              ·
                refine ⟨1618077195599997418574603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4314872521599993116198941 1618077195599997418574603)
                ·
                  refine ⟨2427115793399996127861905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1618077195599997418574603 2427115793399996127861905)
                  ·
                    refine ⟨1820336845049997095896429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2427115793399996127861905 1820336845049997095896429)
                    ·
                      refine ⟨682626316893748910961161, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1820336845049997095896429 682626316893748910961161)
                      ·
                        rfl

theorem cell23_1329410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 2, 3, 1, 2, 3].length) (baseStart_1329410 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1329410 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1329410 prefixEnd_1329410 := by exact prefixLift 1329410
  have htrace : WordTrace (prefixWord ++ tailWord_1329410) baseStart_1329410 baseEnd_1329410 := by
    simpa [prefixWord, tailWord_1329410, baseEnd_1329410] using wordTrace_append hprefix tailTrace_1329410
  have hstable : (prefixWord ++ tailWord_1329410).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1329410).length < 2 ^ (prefixWord ++ tailWord_1329410).sum := by decide
  have hdescent : baseEnd_1329410 < baseStart_1329410 := by decide
  rcases family_descends (prefixWord ++ tailWord_1329410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1329419 : List Nat := [1, 1, 1, 1, 5, 2, 1, 2, 2, 2, 5]
def baseStart_1329419 : Nat := 118140960795 + 1329419 * 2 ^ 59
def prefixEnd_1329419 : Nat := 4983230072969 + 3 ^ 40 * 1329419 * 2
def baseEnd_1329419 : Nat := 682630938219639375748619

theorem tailTrace_1329419 : CollatzResearch.WordTrace tailWord_1329419 prefixEnd_1329419 682630938219639375748619 := by
  unfold tailWord_1329419
  simp only [CollatzResearch.WordTrace]
  refine ⟨48487894370749484534199311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32325262913832989689466207 48487894370749484534199311)
  ·
    refine ⟨72731841556124226801298967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48487894370749484534199311 72731841556124226801298967)
    ·
      refine ⟨109097762334186340201948451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72731841556124226801298967 109097762334186340201948451)
      ·
        refine ⟨163646643501279510302922677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 109097762334186340201948451 163646643501279510302922677)
        ·
          refine ⟨15341872828244954090899001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 163646643501279510302922677 15341872828244954090899001)
          ·
            refine ⟨11506404621183715568174251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15341872828244954090899001 11506404621183715568174251)
            ·
              refine ⟨17259606931775573352261377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11506404621183715568174251 17259606931775573352261377)
              ·
                refine ⟨12944705198831680014196033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17259606931775573352261377 12944705198831680014196033)
                ·
                  refine ⟨9708528899123760010647025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12944705198831680014196033 9708528899123760010647025)
                  ·
                    refine ⟨7281396674342820007985269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9708528899123760010647025 7281396674342820007985269)
                    ·
                      refine ⟨682630938219639375748619, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7281396674342820007985269 682630938219639375748619)
                      ·
                        rfl

theorem cell23_1329419_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 1, 2, 2, 2, 5].length) (baseStart_1329419 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1329419 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1329419 prefixEnd_1329419 := by exact prefixLift 1329419
  have htrace : WordTrace (prefixWord ++ tailWord_1329419) baseStart_1329419 baseEnd_1329419 := by
    simpa [prefixWord, tailWord_1329419, baseEnd_1329419] using wordTrace_append hprefix tailTrace_1329419
  have hstable : (prefixWord ++ tailWord_1329419).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1329419).length < 2 ^ (prefixWord ++ tailWord_1329419).sum := by decide
  have hdescent : baseEnd_1329419 < baseStart_1329419 := by decide
  rcases family_descends (prefixWord ++ tailWord_1329419) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1329440 : List Nat := [2, 1, 1, 5, 2, 2, 1, 3, 2, 1, 3]
def baseStart_1329440 : Nat := 118140960795 + 1329440 * 2 ^ 59
def prefixEnd_1329440 : Nat := 4983230072969 + 3 ^ 40 * 1329440 * 2
def baseEnd_1329440 : Nat := 682641721313383793586023

theorem tailTrace_1329440 : CollatzResearch.WordTrace tailWord_1329440 prefixEnd_1329440 682641721313383793586023 := by
  unfold tailWord_1329440
  simp only [CollatzResearch.WordTrace]
  refine ⟨24244330151836702560356887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32325773535782270080475849 24244330151836702560356887)
  ·
    refine ⟨36366495227755053840535331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24244330151836702560356887 36366495227755053840535331)
    ·
      refine ⟨54549742841632580760802997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36366495227755053840535331 54549742841632580760802997)
      ·
        refine ⟨5114038391403054446325281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 54549742841632580760802997 5114038391403054446325281)
        ·
          refine ⟨3835528793552290834743961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5114038391403054446325281 3835528793552290834743961)
          ·
            refine ⟨2876646595164218126057971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3835528793552290834743961 2876646595164218126057971)
            ·
              refine ⟨4314969892746327189086957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2876646595164218126057971 4314969892746327189086957)
              ·
                refine ⟨1618113709779872695907609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4314969892746327189086957 1618113709779872695907609)
                ·
                  refine ⟨1213585282334904521930707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1618113709779872695907609 1213585282334904521930707)
                  ·
                    refine ⟨1820377923502356782896061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1213585282334904521930707 1820377923502356782896061)
                    ·
                      refine ⟨682641721313383793586023, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1820377923502356782896061 682641721313383793586023)
                      ·
                        rfl

theorem cell23_1329440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 2, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 2, 1, 3, 2, 1, 3].length) (baseStart_1329440 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1329440 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1329440 prefixEnd_1329440 := by exact prefixLift 1329440
  have htrace : WordTrace (prefixWord ++ tailWord_1329440) baseStart_1329440 baseEnd_1329440 := by
    simpa [prefixWord, tailWord_1329440, baseEnd_1329440] using wordTrace_append hprefix tailTrace_1329440
  have hstable : (prefixWord ++ tailWord_1329440).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1329440).length < 2 ^ (prefixWord ++ tailWord_1329440).sum := by decide
  have hdescent : baseEnd_1329440 < baseStart_1329440 := by decide
  rcases family_descends (prefixWord ++ tailWord_1329440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1329463 : List Nat := [1, 1, 3, 1, 2, 1, 1, 3, 6, 2, 2]
def baseStart_1329463 : Nat := 118140960795 + 1329463 * 2 ^ 59
def prefixEnd_1329463 : Nat := 4983230072969 + 3 ^ 40 * 1329463 * 2
def baseEnd_1329463 : Nat := 682653531368437203598417

theorem tailTrace_1329463 : CollatzResearch.WordTrace tailWord_1329463 prefixEnd_1329463 682653531368437203598417 := by
  unfold tailWord_1329463
  simp only [CollatzResearch.WordTrace]
  refine ⟨48489499182590080048801043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32326332788393386699200695 48489499182590080048801043)
  ·
    refine ⟨72734248773885120073201565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48489499182590080048801043 72734248773885120073201565)
    ·
      refine ⟨27275343290206920027450587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 72734248773885120073201565 27275343290206920027450587)
      ·
        refine ⟨40913014935310380041175881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27275343290206920027450587 40913014935310380041175881)
        ·
          refine ⟨30684761201482785030881911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40913014935310380041175881 30684761201482785030881911)
          ·
            refine ⟨46027141802224177546322867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30684761201482785030881911 46027141802224177546322867)
            ·
              refine ⟨69040712703336266319484301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46027141802224177546322867 69040712703336266319484301)
              ·
                refine ⟨25890267263751099869806613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 69040712703336266319484301 25890267263751099869806613)
                ·
                  refine ⟨1213606277988332806397185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 25890267263751099869806613 1213606277988332806397185)
                  ·
                    refine ⟨910204708491249604797889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1213606277988332806397185 910204708491249604797889)
                    ·
                      refine ⟨682653531368437203598417, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 910204708491249604797889 682653531368437203598417)
                      ·
                        rfl

theorem cell23_1329463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 3, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 3, 6, 2, 2].length) (baseStart_1329463 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1329463 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1329463 prefixEnd_1329463 := by exact prefixLift 1329463
  have htrace : WordTrace (prefixWord ++ tailWord_1329463) baseStart_1329463 baseEnd_1329463 := by
    simpa [prefixWord, tailWord_1329463, baseEnd_1329463] using wordTrace_append hprefix tailTrace_1329463
  have hstable : (prefixWord ++ tailWord_1329463).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1329463).length < 2 ^ (prefixWord ++ tailWord_1329463).sum := by decide
  have hdescent : baseEnd_1329463 < baseStart_1329463 := by decide
  rcases family_descends (prefixWord ++ tailWord_1329463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1329466 : List Nat := [3, 1, 1, 1, 4, 2, 2, 1, 2, 1, 5]
def baseStart_1329466 : Nat := 118140960795 + 1329466 * 2 ^ 59
def prefixEnd_1329466 : Nat := 4983230072969 + 3 ^ 40 * 1329466 * 2
def baseEnd_1329466 : Nat := 682655071810400691860903

theorem tailTrace_1329466 : CollatzResearch.WordTrace tailWord_1329466 prefixEnd_1329466 682655071810400691860903 := by
  unfold tailWord_1329466
  simp only [CollatzResearch.WordTrace]
  refine ⟨12122402150394802890290063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32326405734386141040773501 12122402150394802890290063)
  ·
    refine ⟨18183603225592204335435095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12122402150394802890290063 18183603225592204335435095)
    ·
      refine ⟨27275404838388306503152643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18183603225592204335435095 27275404838388306503152643)
      ·
        refine ⟨40913107257582459754728965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27275404838388306503152643 40913107257582459754728965)
        ·
          refine ⟨7671207610796711204011681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 40913107257582459754728965 7671207610796711204011681)
          ·
            refine ⟨5753405708097533403008761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7671207610796711204011681 5753405708097533403008761)
            ·
              refine ⟨4315054281073150052256571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5753405708097533403008761 4315054281073150052256571)
              ·
                refine ⟨6472581421609725078384857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4315054281073150052256571 6472581421609725078384857)
                ·
                  refine ⟨4854436066207293808788643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6472581421609725078384857 4854436066207293808788643)
                  ·
                    refine ⟨7281654099310940713182965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4854436066207293808788643 7281654099310940713182965)
                    ·
                      refine ⟨682655071810400691860903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7281654099310940713182965 682655071810400691860903)
                      ·
                        rfl

theorem cell23_1329466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 2, 1, 2, 1, 5].length) (baseStart_1329466 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1329466 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1329466 prefixEnd_1329466 := by exact prefixLift 1329466
  have htrace : WordTrace (prefixWord ++ tailWord_1329466) baseStart_1329466 baseEnd_1329466 := by
    simpa [prefixWord, tailWord_1329466, baseEnd_1329466] using wordTrace_append hprefix tailTrace_1329466
  have hstable : (prefixWord ++ tailWord_1329466).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1329466).length < 2 ^ (prefixWord ++ tailWord_1329466).sum := by decide
  have hdescent : baseEnd_1329466 < baseStart_1329466 := by decide
  rcases family_descends (prefixWord ++ tailWord_1329466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1329480 : List Nat := [2, 1, 3, 1, 1, 2, 3, 4, 2, 2, 2]
def baseStart_1329480 : Nat := 118140960795 + 1329480 * 2 ^ 59
def prefixEnd_1329480 : Nat := 4983230072969 + 3 ^ 40 * 1329480 * 2
def baseEnd_1329480 : Nat := 682662260539563637085839

theorem tailTrace_1329480 : CollatzResearch.WordTrace tailWord_1329480 prefixEnd_1329480 682662260539563637085839 := by
  unfold tailWord_1329480
  simp only [CollatzResearch.WordTrace]
  refine ⟨24245059611764245976084947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32326746149018994634779929 24245059611764245976084947)
  ·
    refine ⟨36367589417646368964127421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24245059611764245976084947 36367589417646368964127421)
    ·
      refine ⟨13637846031617388361547783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 36367589417646368964127421 13637846031617388361547783)
      ·
        refine ⟨20456769047426082542321675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13637846031617388361547783 20456769047426082542321675)
        ·
          refine ⟨30685153571139123813482513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20456769047426082542321675 30685153571139123813482513)
          ·
            refine ⟨23013865178354342860111885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30685153571139123813482513 23013865178354342860111885)
            ·
              refine ⟨8630199441882878572541957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23013865178354342860111885 8630199441882878572541957)
              ·
                refine ⟨1618162395353039732351617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8630199441882878572541957 1618162395353039732351617)
                ·
                  refine ⟨1213621796514779799263713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1618162395353039732351617 1213621796514779799263713)
                  ·
                    refine ⟨910216347386084849447785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1213621796514779799263713 910216347386084849447785)
                    ·
                      refine ⟨682662260539563637085839, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 910216347386084849447785 682662260539563637085839)
                      ·
                        rfl

theorem cell23_1329480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 3, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 3, 4, 2, 2, 2].length) (baseStart_1329480 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1329480 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1329480 prefixEnd_1329480 := by exact prefixLift 1329480
  have htrace : WordTrace (prefixWord ++ tailWord_1329480) baseStart_1329480 baseEnd_1329480 := by
    simpa [prefixWord, tailWord_1329480, baseEnd_1329480] using wordTrace_append hprefix tailTrace_1329480
  have hstable : (prefixWord ++ tailWord_1329480).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1329480).length < 2 ^ (prefixWord ++ tailWord_1329480).sum := by decide
  have hdescent : baseEnd_1329480 < baseStart_1329480 := by decide
  rcases family_descends (prefixWord ++ tailWord_1329480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1329493 : List Nat := [1, 3, 2, 2, 4, 1, 1, 1, 2, 2, 4]
def baseStart_1329493 : Nat := 118140960795 + 1329493 * 2 ^ 59
def prefixEnd_1329493 : Nat := 4983230072969 + 3 ^ 40 * 1329493 * 2
def baseEnd_1329493 : Nat := 682668935788072086223279

theorem tailTrace_1329493 : CollatzResearch.WordTrace tailWord_1329493 prefixEnd_1329493 682668935788072086223279 := by
  unfold tailWord_1329493
  simp only [CollatzResearch.WordTrace]
  refine ⟨48490593372481395172393133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32327062248320930114928755 48490593372481395172393133)
  ·
    refine ⟨18183972514680523189647425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 48490593372481395172393133 18183972514680523189647425)
    ·
      refine ⟨13637979386010392392235569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18183972514680523189647425 13637979386010392392235569)
      ·
        refine ⟨10228484539507794294176677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13637979386010392392235569 10228484539507794294176677)
        ·
          refine ⟨1917840851157711430158127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10228484539507794294176677 1917840851157711430158127)
          ·
            refine ⟨2876761276736567145237191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1917840851157711430158127 2876761276736567145237191)
            ·
              refine ⟨4315141915104850717855787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2876761276736567145237191 4315141915104850717855787)
              ·
                refine ⟨6472712872657276076783681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4315141915104850717855787 6472712872657276076783681)
                ·
                  refine ⟨4854534654492957057587761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6472712872657276076783681 4854534654492957057587761)
                  ·
                    refine ⟨3640900990869717793190821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4854534654492957057587761 3640900990869717793190821)
                    ·
                      refine ⟨682668935788072086223279, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3640900990869717793190821 682668935788072086223279)
                      ·
                        rfl

theorem cell23_1329493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 4, 1, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 4, 1, 1, 1, 2, 2, 4].length) (baseStart_1329493 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1329493 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1329493 prefixEnd_1329493 := by exact prefixLift 1329493
  have htrace : WordTrace (prefixWord ++ tailWord_1329493) baseStart_1329493 baseEnd_1329493 := by
    simpa [prefixWord, tailWord_1329493, baseEnd_1329493] using wordTrace_append hprefix tailTrace_1329493
  have hstable : (prefixWord ++ tailWord_1329493).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1329493).length < 2 ^ (prefixWord ++ tailWord_1329493).sum := by decide
  have hdescent : baseEnd_1329493 < baseStart_1329493 := by decide
  rcases family_descends (prefixWord ++ tailWord_1329493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1329573 : List Nat := [1, 3, 1, 2, 1, 1, 4, 3, 2, 2, 3]
def baseStart_1329573 : Nat := 118140960795 + 1329573 * 2 ^ 59
def prefixEnd_1329573 : Nat := 4983230072969 + 3 ^ 40 * 1329573 * 2
def baseEnd_1329573 : Nat := 682710014240431773222911

theorem tailTrace_1329573 : CollatzResearch.WordTrace tailWord_1329573 prefixEnd_1329573 682710014240431773222911 := by
  unfold tailWord_1329573
  simp only [CollatzResearch.WordTrace]
  refine ⟨48493511212191568835305373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32329007474794379223536915 48493511212191568835305373)
  ·
    refine ⟨18185066704571838313239515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 48493511212191568835305373 18185066704571838313239515)
    ·
      refine ⟨27277600056857757469859273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18185066704571838313239515 27277600056857757469859273)
      ·
        refine ⟨20458200042643318102394455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27277600056857757469859273 20458200042643318102394455)
        ·
          refine ⟨30687300063964977153591683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20458200042643318102394455 30687300063964977153591683)
          ·
            refine ⟨46030950095947465730387525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30687300063964977153591683 46030950095947465730387525)
            ·
              refine ⟨8630803142990149824447661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 46030950095947465730387525 8630803142990149824447661)
              ·
                refine ⟨3236551178621306184167873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8630803142990149824447661 3236551178621306184167873)
                ·
                  refine ⟨2427413383965979638125905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3236551178621306184167873 2427413383965979638125905)
                  ·
                    refine ⟨1820560037974484728594429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2427413383965979638125905 1820560037974484728594429)
                    ·
                      refine ⟨682710014240431773222911, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1820560037974484728594429 682710014240431773222911)
                      ·
                        rfl

theorem cell23_1329573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 4, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 4, 3, 2, 2, 3].length) (baseStart_1329573 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1329573 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1329573 prefixEnd_1329573 := by exact prefixLift 1329573
  have htrace : WordTrace (prefixWord ++ tailWord_1329573) baseStart_1329573 baseEnd_1329573 := by
    simpa [prefixWord, tailWord_1329573, baseEnd_1329573] using wordTrace_append hprefix tailTrace_1329573
  have hstable : (prefixWord ++ tailWord_1329573).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1329573).length < 2 ^ (prefixWord ++ tailWord_1329573).sum := by decide
  have hdescent : baseEnd_1329573 < baseStart_1329573 := by decide
  rcases family_descends (prefixWord ++ tailWord_1329573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1329654 : List Nat := [5, 1, 1, 1, 2, 1, 3, 4, 1, 1, 3]
def baseStart_1329654 : Nat := 118140960795 + 1329654 * 2 ^ 59
def prefixEnd_1329654 : Nat := 4983230072969 + 3 ^ 40 * 1329654 * 2
def baseEnd_1329654 : Nat := 682751606173445956310039

theorem tailTrace_1329654 : CollatzResearch.WordTrace tailWord_1329654 prefixEnd_1329654 682751606173445956310039 := by
  unfold tailWord_1329654
  simp only [CollatzResearch.WordTrace]
  refine ⟨3031029095306132479312751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 32330977016598746446002677 3031029095306132479312751)
  ·
    refine ⟨4546543642959198718969127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3031029095306132479312751 4546543642959198718969127)
    ·
      refine ⟨6819815464438798078453691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4546543642959198718969127 6819815464438798078453691)
      ·
        refine ⟨10229723196658197117680537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6819815464438798078453691 10229723196658197117680537)
        ·
          refine ⟨7672292397493647838260403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10229723196658197117680537 7672292397493647838260403)
          ·
            refine ⟨11508438596240471757390605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7672292397493647838260403 11508438596240471757390605)
            ·
              refine ⟨4315664473590176909021477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11508438596240471757390605 4315664473590176909021477)
              ·
                refine ⟨809187088798158170441527, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4315664473590176909021477 809187088798158170441527)
                ·
                  refine ⟨1213780633197237255662291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 809187088798158170441527 1213780633197237255662291)
                  ·
                    refine ⟨1820670949795855883493437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1213780633197237255662291 1820670949795855883493437)
                    ·
                      refine ⟨682751606173445956310039, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1820670949795855883493437 682751606173445956310039)
                      ·
                        rfl

theorem cell23_1329654_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 3, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 3, 4, 1, 1, 3].length) (baseStart_1329654 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1329654 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1329654 prefixEnd_1329654 := by exact prefixLift 1329654
  have htrace : WordTrace (prefixWord ++ tailWord_1329654) baseStart_1329654 baseEnd_1329654 := by
    simpa [prefixWord, tailWord_1329654, baseEnd_1329654] using wordTrace_append hprefix tailTrace_1329654
  have hstable : (prefixWord ++ tailWord_1329654).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1329654).length < 2 ^ (prefixWord ++ tailWord_1329654).sum := by decide
  have hdescent : baseEnd_1329654 < baseStart_1329654 := by decide
  rcases family_descends (prefixWord ++ tailWord_1329654) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1329663 : List Nat := [1, 1, 2, 2, 1, 2, 3, 1, 5, 2, 3]
def baseStart_1329663 : Nat := 118140960795 + 1329663 * 2 ^ 59
def prefixEnd_1329663 : Nat := 4983230072969 + 3 ^ 40 * 1329663 * 2
def baseEnd_1329663 : Nat := 682756227499336421097497

theorem tailTrace_1329663 : CollatzResearch.WordTrace tailWord_1329663 prefixEnd_1329663 682756227499336421097497 := by
  unfold tailWord_1329663
  simp only [CollatzResearch.WordTrace]
  refine ⟨48496793781865514206081643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32331195854577009470721095 48496793781865514206081643)
  ·
    refine ⟨72745190672798271309122465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48496793781865514206081643 72745190672798271309122465)
    ·
      refine ⟨54558893004598703481841849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 72745190672798271309122465 54558893004598703481841849)
      ·
        refine ⟨40919169753449027611381387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54558893004598703481841849 40919169753449027611381387)
        ·
          refine ⟨61378754630173541417072081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40919169753449027611381387 61378754630173541417072081)
          ·
            refine ⟨46034065972630156062804061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 61378754630173541417072081 46034065972630156062804061)
            ·
              refine ⟨17262774739736308523551523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 46034065972630156062804061 17262774739736308523551523)
              ·
                refine ⟨25894162109604462785327285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17262774739736308523551523 25894162109604462785327285)
                ·
                  refine ⟨2427577697775418386124433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 25894162109604462785327285 2427577697775418386124433)
                  ·
                    refine ⟨1820683273331563789593325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2427577697775418386124433 1820683273331563789593325)
                    ·
                      refine ⟨682756227499336421097497, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1820683273331563789593325 682756227499336421097497)
                      ·
                        rfl

theorem cell23_1329663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 3, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 3, 1, 5, 2, 3].length) (baseStart_1329663 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1329663 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1329663 prefixEnd_1329663 := by exact prefixLift 1329663
  have htrace : WordTrace (prefixWord ++ tailWord_1329663) baseStart_1329663 baseEnd_1329663 := by
    simpa [prefixWord, tailWord_1329663, baseEnd_1329663] using wordTrace_append hprefix tailTrace_1329663
  have hstable : (prefixWord ++ tailWord_1329663).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1329663).length < 2 ^ (prefixWord ++ tailWord_1329663).sum := by decide
  have hdescent : baseEnd_1329663 < baseStart_1329663 := by decide
  rcases family_descends (prefixWord ++ tailWord_1329663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1329683 : List Nat := [1, 1, 1, 2, 1, 5, 5, 7]
def baseStart_1329683 : Nat := 118140960795 + 1329683 * 2 ^ 59
def prefixEnd_1329683 : Nat := 4983230072969 + 3 ^ 40 * 1329683 * 2
def baseEnd_1329683 : Nat := 25287648041200975661015

theorem tailTrace_1329683 : CollatzResearch.WordTrace tailWord_1329683 prefixEnd_1329683 25287648041200975661015 := by
  unfold tailWord_1329683
  simp only [CollatzResearch.WordTrace]
  refine ⟨48497523241793057621809703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32331682161195371747873135 48497523241793057621809703)
  ·
    refine ⟨72746284862689586432714555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48497523241793057621809703 72746284862689586432714555)
    ·
      refine ⟨109119427294034379649071833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72746284862689586432714555 109119427294034379649071833)
      ·
        refine ⟨81839570470525784736803875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 109119427294034379649071833 81839570470525784736803875)
        ·
          refine ⟨122759355705788677105205813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 81839570470525784736803875 122759355705788677105205813)
          ·
            refine ⟨11508689597417688478613045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 122759355705788677105205813 11508689597417688478613045)
            ·
              refine ⟨1078939649757908294869973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 11508689597417688478613045 1078939649757908294869973)
              ·
                refine ⟨25287648041200975661015, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1078939649757908294869973 25287648041200975661015)
                ·
                  rfl

theorem cell23_1329683_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 5, 7].length) (baseStart_1329683 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1329683 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1329683 prefixEnd_1329683 := by exact prefixLift 1329683
  have htrace : WordTrace (prefixWord ++ tailWord_1329683) baseStart_1329683 baseEnd_1329683 := by
    simpa [prefixWord, tailWord_1329683, baseEnd_1329683] using wordTrace_append hprefix tailTrace_1329683
  have hstable : (prefixWord ++ tailWord_1329683).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1329683).length < 2 ^ (prefixWord ++ tailWord_1329683).sum := by decide
  have hdescent : baseEnd_1329683 < baseStart_1329683 := by decide
  rcases family_descends (prefixWord ++ tailWord_1329683) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1329700 : List Nat := [2, 3, 1, 5, 1, 1, 10]
def baseStart_1329700 : Nat := 118140960795 + 1329700 * 2 ^ 59
def prefixEnd_1329700 : Nat := 4983230072969 + 3 ^ 40 * 1329700 * 2
def baseEnd_1329700 : Nat := 8429323781278429337467

theorem tailTrace_1329700 : CollatzResearch.WordTrace tailWord_1329700 prefixEnd_1329700 8429323781278429337467 := by
  unfold tailWord_1329700
  simp only [CollatzResearch.WordTrace]
  refine ⟨24249071641365734762589277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32332095521820979683452369 24249071641365734762589277)
  ·
    refine ⟨9093401865512150535970979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24249071641365734762589277 9093401865512150535970979)
    ·
      refine ⟨13640102798268225803956469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9093401865512150535970979 13640102798268225803956469)
      ·
        refine ⟨1278759637337646169120919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 13640102798268225803956469 1278759637337646169120919)
        ·
          refine ⟨1918139456006469253681379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1278759637337646169120919 1918139456006469253681379)
          ·
            refine ⟨2877209184009703880522069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1918139456006469253681379 2877209184009703880522069)
            ·
              refine ⟨8429323781278429337467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 2877209184009703880522069 8429323781278429337467)
              ·
                rfl

theorem cell23_1329700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 1, 1, 10].length) (baseStart_1329700 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1329700 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1329700 prefixEnd_1329700 := by exact prefixLift 1329700
  have htrace : WordTrace (prefixWord ++ tailWord_1329700) baseStart_1329700 baseEnd_1329700 := by
    simpa [prefixWord, tailWord_1329700, baseEnd_1329700] using wordTrace_append hprefix tailTrace_1329700
  have hstable : (prefixWord ++ tailWord_1329700).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1329700).length < 2 ^ (prefixWord ++ tailWord_1329700).sum := by decide
  have hdescent : baseEnd_1329700 < baseStart_1329700 := by decide
  rcases family_descends (prefixWord ++ tailWord_1329700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1329704 : List Nat := [2, 1, 5, 2, 1, 3, 1, 2, 2, 4]
def baseStart_1329704 : Nat := 118140960795 + 1329704 * 2 ^ 59
def prefixEnd_1329704 : Nat := 4983230072969 + 3 ^ 40 * 1329704 * 2
def baseEnd_1329704 : Nat := 227592426735390253561603

theorem tailTrace_1329704 : CollatzResearch.WordTrace tailWord_1329704 prefixEnd_1329704 227592426735390253561603 := by
  unfold tailWord_1329704
  simp only [CollatzResearch.WordTrace]
  refine ⟨24249144587358489104162083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32332192783144652138882777 24249144587358489104162083)
  ·
    refine ⟨36373716881037733656243125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24249144587358489104162083 36373716881037733656243125)
    ·
      refine ⟨3410035957597287530272793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 36373716881037733656243125 3410035957597287530272793)
      ·
        refine ⟨2557526968197965647704595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3410035957597287530272793 2557526968197965647704595)
        ·
          refine ⟨3836290452296948471556893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2557526968197965647704595 3836290452296948471556893)
          ·
            refine ⟨1438608919611355676833835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3836290452296948471556893 1438608919611355676833835)
            ·
              refine ⟨2157913379417033515250753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1438608919611355676833835 2157913379417033515250753)
              ·
                refine ⟨1618435034562775136438065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2157913379417033515250753 1618435034562775136438065)
                ·
                  refine ⟨1213826275922081352328549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1618435034562775136438065 1213826275922081352328549)
                  ·
                    refine ⟨227592426735390253561603, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1213826275922081352328549 227592426735390253561603)
                    ·
                      rfl

theorem cell23_1329704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 3, 1, 2, 2, 4].length) (baseStart_1329704 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1329704 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1329704 prefixEnd_1329704 := by exact prefixLift 1329704
  have htrace : WordTrace (prefixWord ++ tailWord_1329704) baseStart_1329704 baseEnd_1329704 := by
    simpa [prefixWord, tailWord_1329704, baseEnd_1329704] using wordTrace_append hprefix tailTrace_1329704
  have hstable : (prefixWord ++ tailWord_1329704).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1329704).length < 2 ^ (prefixWord ++ tailWord_1329704).sum := by decide
  have hdescent : baseEnd_1329704 < baseStart_1329704 := by decide
  rcases family_descends (prefixWord ++ tailWord_1329704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1329734 : List Nat := [6, 1, 1, 1, 2, 3, 2, 7]
def baseStart_1329734 : Nat := 118140960795 + 1329734 * 2 ^ 59
def prefixEnd_1329734 : Nat := 4983230072969 + 3 ^ 40 * 1329734 * 2
def baseEnd_1329734 : Nat := 25288617949103912715173

theorem tailTrace_1329734 : CollatzResearch.WordTrace tailWord_1329734 prefixEnd_1329734 25288617949103912715173 := by
  unfold tailWord_1329734
  simp only [CollatzResearch.WordTrace]
  refine ⟨1515605730144009166622383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 32332922243072195554610837 1515605730144009166622383)
  ·
    refine ⟨2273408595216013749933575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1515605730144009166622383 2273408595216013749933575)
    ·
      refine ⟨3410112892824020624900363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2273408595216013749933575 3410112892824020624900363)
      ·
        refine ⟨5115169339236030937350545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3410112892824020624900363 5115169339236030937350545)
        ·
          refine ⟨3836377004427023203012909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5115169339236030937350545 3836377004427023203012909)
          ·
            refine ⟨1438641376660133701129841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3836377004427023203012909 1438641376660133701129841)
            ·
              refine ⟨1078981032495100275847381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1438641376660133701129841 1078981032495100275847381)
              ·
                refine ⟨25288617949103912715173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1078981032495100275847381 25288617949103912715173)
                ·
                  rfl

theorem cell23_1329734_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 3, 2, 7].length) (baseStart_1329734 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1329734 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1329734 prefixEnd_1329734 := by exact prefixLift 1329734
  have htrace : WordTrace (prefixWord ++ tailWord_1329734) baseStart_1329734 baseEnd_1329734 := by
    simpa [prefixWord, tailWord_1329734, baseEnd_1329734] using wordTrace_append hprefix tailTrace_1329734
  have hstable : (prefixWord ++ tailWord_1329734).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1329734).length < 2 ^ (prefixWord ++ tailWord_1329734).sum := by decide
  have hdescent : baseEnd_1329734 < baseStart_1329734 := by decide
  rcases family_descends (prefixWord ++ tailWord_1329734) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1329753 : List Nat := [1, 2, 1, 2, 2, 1, 1, 1, 3, 6, 3]
def baseStart_1329753 : Nat := 118140960795 + 1329753 * 2 ^ 59
def prefixEnd_1329753 : Nat := 4983230072969 + 3 ^ 40 * 1329753 * 2
def baseEnd_1329753 : Nat := 682802440758241068972083

theorem tailTrace_1329753 : CollatzResearch.WordTrace tailWord_1329753 prefixEnd_1329753 682802440758241068972083 := by
  unfold tailWord_1329753
  simp only [CollatzResearch.WordTrace]
  refine ⟨48500076351539459576857913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32333384234359639717905275 48500076351539459576857913)
  ·
    refine ⟨36375057263654594682643435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48500076351539459576857913 36375057263654594682643435)
    ·
      refine ⟨54562585895481892023965153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36375057263654594682643435 54562585895481892023965153)
      ·
        refine ⟨40921939421611419017973865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54562585895481892023965153 40921939421611419017973865)
        ·
          refine ⟨30691454566208564263480399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40921939421611419017973865 30691454566208564263480399)
          ·
            refine ⟨46037181849312846395220599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30691454566208564263480399 46037181849312846395220599)
            ·
              refine ⟨69055772773969269592830899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46037181849312846395220599 69055772773969269592830899)
              ·
                refine ⟨103583659160953904389246349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 69055772773969269592830899 103583659160953904389246349)
                ·
                  refine ⟨38843872185357714145967381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 103583659160953904389246349 38843872185357714145967381)
                  ·
                    refine ⟨1820806508688642850592221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 38843872185357714145967381 1820806508688642850592221)
                    ·
                      refine ⟨682802440758241068972083, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1820806508688642850592221 682802440758241068972083)
                      ·
                        rfl

theorem cell23_1329753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 1, 3, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 1, 3, 6, 3].length) (baseStart_1329753 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1329753 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1329753 prefixEnd_1329753 := by exact prefixLift 1329753
  have htrace : WordTrace (prefixWord ++ tailWord_1329753) baseStart_1329753 baseEnd_1329753 := by
    simpa [prefixWord, tailWord_1329753, baseEnd_1329753] using wordTrace_append hprefix tailTrace_1329753
  have hstable : (prefixWord ++ tailWord_1329753).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1329753).length < 2 ^ (prefixWord ++ tailWord_1329753).sum := by decide
  have hdescent : baseEnd_1329753 < baseStart_1329753 := by decide
  rcases family_descends (prefixWord ++ tailWord_1329753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1329770 : List Nat := [3, 1, 3, 2, 1, 1, 2, 1, 2, 4, 3]
def baseStart_1329770 : Nat := 118140960795 + 1329770 * 2 ^ 59
def prefixEnd_1329770 : Nat := 4983230072969 + 3 ^ 40 * 1329770 * 2
def baseEnd_1329770 : Nat := 682811169929367502459505

theorem tailTrace_1329770 : CollatzResearch.WordTrace tailWord_1329770 prefixEnd_1329770 682811169929367502459505 := by
  unfold tailWord_1329770
  simp only [CollatzResearch.WordTrace]
  refine ⟨12125174098119467870056691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32333797594985247653484509 12125174098119467870056691)
  ·
    refine ⟨18187761147179201805085037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12125174098119467870056691 18187761147179201805085037)
    ·
      refine ⟨6820410430192200676906889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18187761147179201805085037 6820410430192200676906889)
      ·
        refine ⟨5115307822644150507680167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6820410430192200676906889 5115307822644150507680167)
        ·
          refine ⟨7672961733966225761520251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5115307822644150507680167 7672961733966225761520251)
          ·
            refine ⟨11509442600949338642280377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7672961733966225761520251 11509442600949338642280377)
            ·
              refine ⟨8632081950712003981710283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11509442600949338642280377 8632081950712003981710283)
              ·
                refine ⟨12948122926068005972565425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8632081950712003981710283 12948122926068005972565425)
                ·
                  refine ⟨9711092194551004479424069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12948122926068005972565425 9711092194551004479424069)
                  ·
                    refine ⟨1820829786478313339892013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9711092194551004479424069 1820829786478313339892013)
                    ·
                      refine ⟨682811169929367502459505, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1820829786478313339892013 682811169929367502459505)
                      ·
                        rfl

theorem cell23_1329770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 2, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 2, 1, 2, 4, 3].length) (baseStart_1329770 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1329770 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1329770 prefixEnd_1329770 := by exact prefixLift 1329770
  have htrace : WordTrace (prefixWord ++ tailWord_1329770) baseStart_1329770 baseEnd_1329770 := by
    simpa [prefixWord, tailWord_1329770, baseEnd_1329770] using wordTrace_append hprefix tailTrace_1329770
  have hstable : (prefixWord ++ tailWord_1329770).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1329770).length < 2 ^ (prefixWord ++ tailWord_1329770).sum := by decide
  have hdescent : baseEnd_1329770 < baseStart_1329770 := by decide
  rcases family_descends (prefixWord ++ tailWord_1329770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1329778 : List Nat := [3, 2, 1, 2, 5, 1, 2, 1, 2, 1, 3]
def baseStart_1329778 : Nat := 118140960795 + 1329778 * 2 ^ 59
def prefixEnd_1329778 : Nat := 4983230072969 + 3 ^ 40 * 1329778 * 2
def baseEnd_1329778 : Nat := 682815277774603471159469

theorem tailTrace_1329778 : CollatzResearch.WordTrace tailWord_1329778 prefixEnd_1329778 682815277774603471159469 := by
  unfold tailWord_1329778
  simp only [CollatzResearch.WordTrace]
  refine ⟨12125247044112222211629497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32333992117632592564345325 12125247044112222211629497)
  ·
    refine ⟨9093935283084166658722123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12125247044112222211629497 9093935283084166658722123)
    ·
      refine ⟨13640902924626249988083185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9093935283084166658722123 13640902924626249988083185)
      ·
        refine ⟨10230677193469687491062389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13640902924626249988083185 10230677193469687491062389)
        ·
          refine ⟨959125986887783202287099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 10230677193469687491062389 959125986887783202287099)
          ·
            refine ⟨1438688980331674803430649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 959125986887783202287099 1438688980331674803430649)
            ·
              refine ⟨1079016735248756102572987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1438688980331674803430649 1079016735248756102572987)
              ·
                refine ⟨1618525102873134153859481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1079016735248756102572987 1618525102873134153859481)
                ·
                  refine ⟨1213893827154850615394611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1618525102873134153859481 1213893827154850615394611)
                  ·
                    refine ⟨1820840740732275923091917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1213893827154850615394611 1820840740732275923091917)
                    ·
                      refine ⟨682815277774603471159469, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1820840740732275923091917 682815277774603471159469)
                      ·
                        rfl

theorem cell23_1329778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 5, 1, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 5, 1, 2, 1, 2, 1, 3].length) (baseStart_1329778 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1329778 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1329778 prefixEnd_1329778 := by exact prefixLift 1329778
  have htrace : WordTrace (prefixWord ++ tailWord_1329778) baseStart_1329778 baseEnd_1329778 := by
    simpa [prefixWord, tailWord_1329778, baseEnd_1329778] using wordTrace_append hprefix tailTrace_1329778
  have hstable : (prefixWord ++ tailWord_1329778).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1329778).length < 2 ^ (prefixWord ++ tailWord_1329778).sum := by decide
  have hdescent : baseEnd_1329778 < baseStart_1329778 := by decide
  rcases family_descends (prefixWord ++ tailWord_1329778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1329818 : List Nat := [3, 1, 1, 6, 1, 1, 2, 2, 2, 2, 2]
def baseStart_1329818 : Nat := 118140960795 + 1329818 * 2 ^ 59
def prefixEnd_1329818 : Nat := 4983230072969 + 3 ^ 40 * 1329818 * 2
def baseEnd_1329818 : Nat := 682835817000783314659285

theorem tailTrace_1329818 : CollatzResearch.WordTrace tailWord_1329818 prefixEnd_1329818 682835817000783314659285 := by
  unfold tailWord_1329818
  simp only [CollatzResearch.WordTrace]
  refine ⟨12125611774075993919493527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32334964730869317118649405 12125611774075993919493527)
  ·
    refine ⟨18188417661113990879240291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12125611774075993919493527 18188417661113990879240291)
    ·
      refine ⟨27282626491670986318860437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18188417661113990879240291 27282626491670986318860437)
      ·
        refine ⟨1278873116797077483696583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 27282626491670986318860437 1278873116797077483696583)
        ·
          refine ⟨1918309675195616225544875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1278873116797077483696583 1918309675195616225544875)
          ·
            refine ⟨2877464512793424338317313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1918309675195616225544875 2877464512793424338317313)
            ·
              refine ⟨2158098384595068253737985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2877464512793424338317313 2158098384595068253737985)
              ·
                refine ⟨1618573788446301190303489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2158098384595068253737985 1618573788446301190303489)
                ·
                  refine ⟨1213930341334725892727617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1618573788446301190303489 1213930341334725892727617)
                  ·
                    refine ⟨910447756001044419545713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1213930341334725892727617 910447756001044419545713)
                    ·
                      refine ⟨682835817000783314659285, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 910447756001044419545713 682835817000783314659285)
                      ·
                        rfl

theorem cell23_1329818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 1, 1, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 1, 1, 2, 2, 2, 2, 2].length) (baseStart_1329818 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1329818 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1329818 prefixEnd_1329818 := by exact prefixLift 1329818
  have htrace : WordTrace (prefixWord ++ tailWord_1329818) baseStart_1329818 baseEnd_1329818 := by
    simpa [prefixWord, tailWord_1329818, baseEnd_1329818] using wordTrace_append hprefix tailTrace_1329818
  have hstable : (prefixWord ++ tailWord_1329818).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1329818).length < 2 ^ (prefixWord ++ tailWord_1329818).sum := by decide
  have hdescent : baseEnd_1329818 < baseStart_1329818 := by decide
  rcases family_descends (prefixWord ++ tailWord_1329818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1329870 : List Nat := [4, 1, 1, 1, 3, 2, 1, 1, 2, 1, 6]
def baseStart_1329870 : Nat := 118140960795 + 1329870 * 2 ^ 59
def prefixEnd_1329870 : Nat := 4983230072969 + 3 ^ 40 * 1329870 * 2
def baseEnd_1329870 : Nat := 682862517994817111209045

theorem tailTrace_1329870 : CollatzResearch.WordTrace tailWord_1329870 prefixEnd_1329870 682862517994817111209045 := by
  unfold tailWord_1329870
  simp only [CollatzResearch.WordTrace]
  refine ⟨6063042961514448569858383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 32336229128077059039244709 6063042961514448569858383)
  ·
    refine ⟨9094564442271672854787575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6063042961514448569858383 9094564442271672854787575)
    ·
      refine ⟨13641846663407509282181363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9094564442271672854787575 13641846663407509282181363)
      ·
        refine ⟨20462769995111263923272045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13641846663407509282181363 20462769995111263923272045)
        ·
          refine ⟨7673538748166723971227017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20462769995111263923272045 7673538748166723971227017)
          ·
            refine ⟨5755154061125042978420263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7673538748166723971227017 5755154061125042978420263)
            ·
              refine ⟨8632731091687564467630395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5755154061125042978420263 8632731091687564467630395)
              ·
                refine ⟨12949096637531346701445593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8632731091687564467630395 12949096637531346701445593)
                ·
                  refine ⟨9711822478148510026084195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12949096637531346701445593 9711822478148510026084195)
                  ·
                    refine ⟨14567733717222765039126293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9711822478148510026084195 14567733717222765039126293)
                    ·
                      refine ⟨682862517994817111209045, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 14567733717222765039126293 682862517994817111209045)
                      ·
                        rfl

theorem cell23_1329870_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 1, 1, 2, 1, 6].length) (baseStart_1329870 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1329870 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1329870 prefixEnd_1329870 := by exact prefixLift 1329870
  have htrace : WordTrace (prefixWord ++ tailWord_1329870) baseStart_1329870 baseEnd_1329870 := by
    simpa [prefixWord, tailWord_1329870, baseEnd_1329870] using wordTrace_append hprefix tailTrace_1329870
  have hstable : (prefixWord ++ tailWord_1329870).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1329870).length < 2 ^ (prefixWord ++ tailWord_1329870).sum := by decide
  have hdescent : baseEnd_1329870 < baseStart_1329870 := by decide
  rcases family_descends (prefixWord ++ tailWord_1329870) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1329880 : List Nat := [2, 1, 2, 2, 3, 3, 1, 1, 8]
def baseStart_1329880 : Nat := 118140960795 + 1329880 * 2 ^ 59
def prefixEnd_1329880 : Nat := 4983230072969 + 3 ^ 40 * 1329880 * 2
def baseEnd_1329880 : Nat := 75874183644595785787111

theorem tailTrace_1329880 : CollatzResearch.WordTrace tailWord_1329880 prefixEnd_1329880 75874183644595785787111 := by
  unfold tailWord_1329880
  simp only [CollatzResearch.WordTrace]
  refine ⟨24252354211039680133365547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32336472281386240177820729 24252354211039680133365547)
  ·
    refine ⟨36378531316559520200048321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24252354211039680133365547 36378531316559520200048321)
    ·
      refine ⟨27283898487419640150036241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36378531316559520200048321 27283898487419640150036241)
      ·
        refine ⟨20462923865564730112527181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27283898487419640150036241 20462923865564730112527181)
        ·
          refine ⟨7673596449586773792197693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20462923865564730112527181 7673596449586773792197693)
          ·
            refine ⟨2877598668595040172074135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7673596449586773792197693 2877598668595040172074135)
            ·
              refine ⟨4316398002892560258111203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2877598668595040172074135 4316398002892560258111203)
              ·
                refine ⟨6474597004338840387166805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4316398002892560258111203 6474597004338840387166805)
                ·
                  refine ⟨75874183644595785787111, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 6474597004338840387166805 75874183644595785787111)
                  ·
                    rfl

theorem cell23_1329880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 3, 1, 1, 8].length) (baseStart_1329880 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1329880 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1329880 prefixEnd_1329880 := by exact prefixLift 1329880
  have htrace : WordTrace (prefixWord ++ tailWord_1329880) baseStart_1329880 baseEnd_1329880 := by
    simpa [prefixWord, tailWord_1329880, baseEnd_1329880] using wordTrace_append hprefix tailTrace_1329880
  have hstable : (prefixWord ++ tailWord_1329880).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1329880).length < 2 ^ (prefixWord ++ tailWord_1329880).sum := by decide
  have hdescent : baseEnd_1329880 < baseStart_1329880 := by decide
  rcases family_descends (prefixWord ++ tailWord_1329880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1329884 : List Nat := [2, 2, 5, 1, 1, 1, 1, 3, 3, 4]
def baseStart_1329884 : Nat := 118140960795 + 1329884 * 2 ^ 59
def prefixEnd_1329884 : Nat := 4983230072969 + 3 ^ 40 * 1329884 * 2
def baseEnd_1329884 : Nat := 227623235574660018811327

theorem tailTrace_1329884 : CollatzResearch.WordTrace tailWord_1329884 prefixEnd_1329884 227623235574660018811327 := by
  unfold tailWord_1329884
  simp only [CollatzResearch.WordTrace]
  refine ⟨24252427157032434474938353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32336569542709912633251137 24252427157032434474938353)
  ·
    refine ⟨18189320367774325856203765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24252427157032434474938353 18189320367774325856203765)
    ·
      refine ⟨1705248784478843049019103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 18189320367774325856203765 1705248784478843049019103)
      ·
        refine ⟨2557873176718264573528655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1705248784478843049019103 2557873176718264573528655)
        ·
          refine ⟨3836809765077396860292983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2557873176718264573528655 3836809765077396860292983)
          ·
            refine ⟨5755214647616095290439475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3836809765077396860292983 5755214647616095290439475)
            ·
              refine ⟨8632821971424142935659213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5755214647616095290439475 8632821971424142935659213)
              ·
                refine ⟨3237308239284053600872205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8632821971424142935659213 3237308239284053600872205)
                ·
                  refine ⟨1213990589731520100327077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3237308239284053600872205 1213990589731520100327077)
                  ·
                    refine ⟨227623235574660018811327, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1213990589731520100327077 227623235574660018811327)
                    ·
                      rfl

theorem cell23_1329884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 1, 3, 3, 4].length) (baseStart_1329884 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1329884 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1329884 prefixEnd_1329884 := by exact prefixLift 1329884
  have htrace : WordTrace (prefixWord ++ tailWord_1329884) baseStart_1329884 baseEnd_1329884 := by
    simpa [prefixWord, tailWord_1329884, baseEnd_1329884] using wordTrace_append hprefix tailTrace_1329884
  have hstable : (prefixWord ++ tailWord_1329884).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1329884).length < 2 ^ (prefixWord ++ tailWord_1329884).sum := by decide
  have hdescent : baseEnd_1329884 < baseStart_1329884 := by decide
  rcases family_descends (prefixWord ++ tailWord_1329884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1329917 : List Nat := [1, 4, 1, 1, 1, 1, 3, 3, 1, 5, 2]
def baseStart_1329917 : Nat := 118140960795 + 1329917 * 2 ^ 59
def prefixEnd_1329917 : Nat := 4983230072969 + 3 ^ 40 * 1329917 * 2
def baseEnd_1329917 : Nat := 682886651585578427321329

theorem tailTrace_1329917 : CollatzResearch.WordTrace tailWord_1329917 prefixEnd_1329917 682886651585578427321329 := by
  unfold tailWord_1329917
  simp only [CollatzResearch.WordTrace]
  refine ⟨48506057922945315585828005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32337371948630210390552003 48506057922945315585828005)
  ·
    refine ⟨9094885860552246672342751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 48506057922945315585828005 9094885860552246672342751)
    ·
      refine ⟨13642328790828370008514127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9094885860552246672342751 13642328790828370008514127)
      ·
        refine ⟨20463493186242555012771191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13642328790828370008514127 20463493186242555012771191)
        ·
          refine ⟨30695239779363832519156787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20463493186242555012771191 30695239779363832519156787)
          ·
            refine ⟨46042859669045748778735181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30695239779363832519156787 46042859669045748778735181)
            ·
              refine ⟨17266072375892155792025693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 46042859669045748778735181 17266072375892155792025693)
              ·
                refine ⟨6474777140959558422009635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17266072375892155792025693 6474777140959558422009635)
                ·
                  refine ⟨9712165711439337633014453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6474777140959558422009635 9712165711439337633014453)
                  ·
                    refine ⟨910515535447437903095105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9712165711439337633014453 910515535447437903095105)
                    ·
                      refine ⟨682886651585578427321329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 910515535447437903095105 682886651585578427321329)
                      ·
                        rfl

theorem cell23_1329917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 3, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 3, 3, 1, 5, 2].length) (baseStart_1329917 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1329917 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1329917 prefixEnd_1329917 := by exact prefixLift 1329917
  have htrace : WordTrace (prefixWord ++ tailWord_1329917) baseStart_1329917 baseEnd_1329917 := by
    simpa [prefixWord, tailWord_1329917, baseEnd_1329917] using wordTrace_append hprefix tailTrace_1329917
  have hstable : (prefixWord ++ tailWord_1329917).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1329917).length < 2 ^ (prefixWord ++ tailWord_1329917).sum := by decide
  have hdescent : baseEnd_1329917 < baseStart_1329917 := by decide
  rcases family_descends (prefixWord ++ tailWord_1329917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1329918 : List Nat := [4, 2, 2, 1, 2, 3, 1, 3, 1, 4]
def baseStart_1329918 : Nat := 118140960795 + 1329918 * 2 ^ 59
def prefixEnd_1329918 : Nat := 4983230072969 + 3 ^ 40 * 1329918 * 2
def baseEnd_1329918 : Nat := 227629055022077641136275

theorem tailTrace_1329918 : CollatzResearch.WordTrace tailWord_1329918 prefixEnd_1329918 227629055022077641136275 := by
  unfold tailWord_1329918
  simp only [CollatzResearch.WordTrace]
  refine ⟨6063261799492711594576801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 32337396263961128504409605 6063261799492711594576801)
  ·
    refine ⟨4547446349619533695932601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6063261799492711594576801 4547446349619533695932601)
    ·
      refine ⟨3410584762214650271949451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4547446349619533695932601 3410584762214650271949451)
      ·
        refine ⟨5115877143321975407924177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3410584762214650271949451 5115877143321975407924177)
        ·
          refine ⟨3836907857491481555943133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5115877143321975407924177 3836907857491481555943133)
          ·
            refine ⟨1438840446559305583478675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3836907857491481555943133 1438840446559305583478675)
            ·
              refine ⟨2158260669838958375218013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1438840446559305583478675 2158260669838958375218013)
              ·
                refine ⟨809347751189609390706755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2158260669838958375218013 809347751189609390706755)
                ·
                  refine ⟨1214021626784414086060133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 809347751189609390706755 1214021626784414086060133)
                  ·
                    refine ⟨227629055022077641136275, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1214021626784414086060133 227629055022077641136275)
                    ·
                      rfl

theorem cell23_1329918_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 3, 1, 3, 1, 4].length) (baseStart_1329918 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1329918 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1329918 prefixEnd_1329918 := by exact prefixLift 1329918
  have htrace : WordTrace (prefixWord ++ tailWord_1329918) baseStart_1329918 baseEnd_1329918 := by
    simpa [prefixWord, tailWord_1329918, baseEnd_1329918] using wordTrace_append hprefix tailTrace_1329918
  have hstable : (prefixWord ++ tailWord_1329918).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1329918).length < 2 ^ (prefixWord ++ tailWord_1329918).sum := by decide
  have hdescent : baseEnd_1329918 < baseStart_1329918 := by decide
  rcases family_descends (prefixWord ++ tailWord_1329918) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1329964 : List Nat := [2, 2, 1, 1, 1, 4, 2, 1, 5, 2, 2]
def baseStart_1329964 : Nat := 118140960795 + 1329964 * 2 ^ 59
def prefixEnd_1329964 : Nat := 4983230072969 + 3 ^ 40 * 1329964 * 2
def baseEnd_1329964 : Nat := 682910785176339743433613

theorem tailTrace_1329964 : CollatzResearch.WordTrace tailWord_1329964 prefixEnd_1329964 682910785176339743433613 := by
  unfold tailWord_1329964
  simp only [CollatzResearch.WordTrace]
  refine ⟨24253886076887521306394473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32338514769183361741859297 24253886076887521306394473)
  ·
    refine ⟨18190414557665640979795855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24253886076887521306394473 18190414557665640979795855)
    ·
      refine ⟨27285621836498461469693783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18190414557665640979795855 27285621836498461469693783)
      ·
        refine ⟨40928432754747692204540675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27285621836498461469693783 40928432754747692204540675)
        ·
          refine ⟨61392649132121538306811013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40928432754747692204540675 61392649132121538306811013)
          ·
            refine ⟨11511121712272788432527065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 61392649132121538306811013 11511121712272788432527065)
            ·
              refine ⟨8633341284204591324395299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11511121712272788432527065 8633341284204591324395299)
              ·
                refine ⟨12950011926306886986592949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8633341284204591324395299 12950011926306886986592949)
                ·
                  refine ⟨1214063618091270654993089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 12950011926306886986592949 1214063618091270654993089)
                  ·
                    refine ⟨910547713568452991244817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1214063618091270654993089 910547713568452991244817)
                    ·
                      refine ⟨682910785176339743433613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 910547713568452991244817 682910785176339743433613)
                      ·
                        rfl

theorem cell23_1329964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 5, 2, 2].length) (baseStart_1329964 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1329964 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1329964 prefixEnd_1329964 := by exact prefixLift 1329964
  have htrace : WordTrace (prefixWord ++ tailWord_1329964) baseStart_1329964 baseEnd_1329964 := by
    simpa [prefixWord, tailWord_1329964, baseEnd_1329964] using wordTrace_append hprefix tailTrace_1329964
  have hstable : (prefixWord ++ tailWord_1329964).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1329964).length < 2 ^ (prefixWord ++ tailWord_1329964).sum := by decide
  have hdescent : baseEnd_1329964 < baseStart_1329964 := by decide
  rcases family_descends (prefixWord ++ tailWord_1329964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1329970 : List Nat := [3, 2, 1, 1, 3, 1, 1, 11]
def baseStart_1329970 : Nat := 118140960795 + 1329970 * 2 ^ 59
def prefixEnd_1329970 : Nat := 4983230072969 + 3 ^ 40 * 1329970 * 2
def baseEnd_1329970 : Nat := 25293106150380248887355

theorem tailTrace_1329970 : CollatzResearch.WordTrace tailWord_1329970 prefixEnd_1329970 25293106150380248887355 := by
  unfold tailWord_1329970
  simp only [CollatzResearch.WordTrace]
  refine ⟨12126997747938326409376841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32338660661168870425004909 12126997747938326409376841)
  ·
    refine ⟨9095248310953744807032631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12126997747938326409376841 9095248310953744807032631)
    ·
      refine ⟨13642872466430617210548947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9095248310953744807032631 13642872466430617210548947)
      ·
        refine ⟨20464308699645925815823421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13642872466430617210548947 20464308699645925815823421)
        ·
          refine ⟨7674115762367222180933783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20464308699645925815823421 7674115762367222180933783)
          ·
            refine ⟨11511173643550833271400675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7674115762367222180933783 11511173643550833271400675)
            ·
              refine ⟨17266760465326249907101013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11511173643550833271400675 17266760465326249907101013)
              ·
                refine ⟨25293106150380248887355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 17266760465326249907101013 25293106150380248887355)
                ·
                  rfl

theorem cell23_1329970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 1, 11].length) (baseStart_1329970 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1329970 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1329970 prefixEnd_1329970 := by exact prefixLift 1329970
  have htrace : WordTrace (prefixWord ++ tailWord_1329970) baseStart_1329970 baseEnd_1329970 := by
    simpa [prefixWord, tailWord_1329970, baseEnd_1329970] using wordTrace_append hprefix tailTrace_1329970
  have hstable : (prefixWord ++ tailWord_1329970).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1329970).length < 2 ^ (prefixWord ++ tailWord_1329970).sum := by decide
  have hdescent : baseEnd_1329970 < baseStart_1329970 := by decide
  rcases family_descends (prefixWord ++ tailWord_1329970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1330000 : List Nat := [2, 1, 1, 1, 1, 4, 3, 1, 2, 7]
def baseStart_1330000 : Nat := 118140960795 + 1330000 * 2 ^ 59
def prefixEnd_1330000 : Nat := 4983230072969 + 3 ^ 40 * 1330000 * 2
def baseEnd_1330000 : Nat := 227643090159967200861149

theorem tailTrace_1330000 : CollatzResearch.WordTrace tailWord_1330000 prefixEnd_1330000 227643090159967200861149 := by
  unfold tailWord_1330000
  simp only [CollatzResearch.WordTrace]
  refine ⟨24254542590822310380549727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32339390121096413840732969 24254542590822310380549727)
  ·
    refine ⟨36381813886233465570824591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24254542590822310380549727 36381813886233465570824591)
    ·
      refine ⟨54572720829350198356236887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36381813886233465570824591 54572720829350198356236887)
      ·
        refine ⟨81859081244025297534355331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54572720829350198356236887 81859081244025297534355331)
        ·
          refine ⟨122788621866037946301532997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 81859081244025297534355331 122788621866037946301532997)
          ·
            refine ⟨23022866599882114931537437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 122788621866037946301532997 23022866599882114931537437)
            ·
              refine ⟨8633574974955793099326539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23022866599882114931537437 8633574974955793099326539)
              ·
                refine ⟨12950362462433689648989809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8633574974955793099326539 12950362462433689648989809)
                ·
                  refine ⟨9712771846825267236742357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12950362462433689648989809 9712771846825267236742357)
                  ·
                    refine ⟨227643090159967200861149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 9712771846825267236742357 227643090159967200861149)
                    ·
                      rfl

theorem cell23_1330000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 3, 1, 2, 7].length) (baseStart_1330000 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1330000 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1330000 prefixEnd_1330000 := by exact prefixLift 1330000
  have htrace : WordTrace (prefixWord ++ tailWord_1330000) baseStart_1330000 baseEnd_1330000 := by
    simpa [prefixWord, tailWord_1330000, baseEnd_1330000] using wordTrace_append hprefix tailTrace_1330000
  have hstable : (prefixWord ++ tailWord_1330000).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1330000).length < 2 ^ (prefixWord ++ tailWord_1330000).sum := by decide
  have hdescent : baseEnd_1330000 < baseStart_1330000 := by decide
  rcases family_descends (prefixWord ++ tailWord_1330000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1330004 : List Nat := [2, 4, 1, 1, 4, 2, 1, 8]
def baseStart_1330004 : Nat := 118140960795 + 1330004 * 2 ^ 59
def prefixEnd_1330004 : Nat := 4983230072969 + 3 ^ 40 * 1330004 * 2
def baseEnd_1330004 : Nat := 25293752755648873590127

theorem tailTrace_1330004 : CollatzResearch.WordTrace tailWord_1330004 prefixEnd_1330004 25293752755648873590127 := by
  unfold tailWord_1330004
  simp only [CollatzResearch.WordTrace]
  refine ⟨24254615536815064722122533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32339487382420086296163377 24254615536815064722122533)
  ·
    refine ⟨4547740413152824635397975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 24254615536815064722122533 4547740413152824635397975)
    ·
      refine ⟨6821610619729236953096963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4547740413152824635397975 6821610619729236953096963)
      ·
        refine ⟨10232415929593855429645445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6821610619729236953096963 10232415929593855429645445)
        ·
          refine ⟨1918577986798847893058521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10232415929593855429645445 1918577986798847893058521)
          ·
            refine ⟨1438933490099135919793891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1918577986798847893058521 1438933490099135919793891)
            ·
              refine ⟨2158400235148703879690837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1438933490099135919793891 2158400235148703879690837)
              ·
                refine ⟨25293752755648873590127, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 2158400235148703879690837 25293752755648873590127)
                ·
                  rfl

theorem cell23_1330004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 4, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 4, 2, 1, 8].length) (baseStart_1330004 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1330004 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1330004 prefixEnd_1330004 := by exact prefixLift 1330004
  have htrace : WordTrace (prefixWord ++ tailWord_1330004) baseStart_1330004 baseEnd_1330004 := by
    simpa [prefixWord, tailWord_1330004, baseEnd_1330004] using wordTrace_append hprefix tailTrace_1330004
  have hstable : (prefixWord ++ tailWord_1330004).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1330004).length < 2 ^ (prefixWord ++ tailWord_1330004).sum := by decide
  have hdescent : baseEnd_1330004 < baseStart_1330004 := by decide
  rcases family_descends (prefixWord ++ tailWord_1330004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1330041 : List Nat := [1, 2, 1, 3, 2, 4, 1, 3, 1, 3, 2]
def baseStart_1330041 : Nat := 118140960795 + 1330041 * 2 ^ 59
def prefixEnd_1330041 : Nat := 4983230072969 + 3 ^ 40 * 1330041 * 2
def baseEnd_1330041 : Nat := 682950323186735942170759

theorem tailTrace_1330041 : CollatzResearch.WordTrace tailWord_1330041 prefixEnd_1330041 682950323186735942170759 := by
  unfold tailWord_1330041
  simp only [CollatzResearch.WordTrace]
  refine ⟨48510580574496084763341977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32340387049664056508894651 48510580574496084763341977)
  ·
    refine ⟨36382935430872063572506483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48510580574496084763341977 36382935430872063572506483)
    ·
      refine ⟨54574403146308095358759725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36382935430872063572506483 54574403146308095358759725)
      ·
        refine ⟨20465401179865535759534897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 54574403146308095358759725 20465401179865535759534897)
        ·
          refine ⟨15349050884899151819651173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20465401179865535759534897 15349050884899151819651173)
          ·
            refine ⟨2877947040918590966184595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 15349050884899151819651173 2877947040918590966184595)
            ·
              refine ⟨4316920561377886449276893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2877947040918590966184595 4316920561377886449276893)
              ·
                refine ⟨1618845210516707418478835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4316920561377886449276893 1618845210516707418478835)
                ·
                  refine ⟨2428267815775061127718253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1618845210516707418478835 2428267815775061127718253)
                  ·
                    refine ⟨910600430915647922894345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2428267815775061127718253 910600430915647922894345)
                    ·
                      refine ⟨682950323186735942170759, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 910600430915647922894345 682950323186735942170759)
                      ·
                        rfl

theorem cell23_1330041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 4, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 4, 1, 3, 1, 3, 2].length) (baseStart_1330041 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1330041 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1330041 prefixEnd_1330041 := by exact prefixLift 1330041
  have htrace : WordTrace (prefixWord ++ tailWord_1330041) baseStart_1330041 baseEnd_1330041 := by
    simpa [prefixWord, tailWord_1330041, baseEnd_1330041] using wordTrace_append hprefix tailTrace_1330041
  have hstable : (prefixWord ++ tailWord_1330041).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1330041).length < 2 ^ (prefixWord ++ tailWord_1330041).sum := by decide
  have hdescent : baseEnd_1330041 < baseStart_1330041 := by decide
  rcases family_descends (prefixWord ++ tailWord_1330041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1330077 : List Nat := [1, 4, 2, 1, 2, 1, 1, 4, 7]
def baseStart_1330077 : Nat := 118140960795 + 1330077 * 2 ^ 59
def prefixEnd_1330077 : Nat := 4983230072969 + 3 ^ 40 * 1330077 * 2
def baseEnd_1330077 : Nat := 75885423165588644591177

theorem tailTrace_1330077 : CollatzResearch.WordTrace tailWord_1330077 prefixEnd_1330077 75885423165588644591177 := by
  unfold tailWord_1330077
  simp only [CollatzResearch.WordTrace]
  refine ⟨48511893602365662911652485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32341262401577108607768323 48511893602365662911652485)
  ·
    refine ⟨9095980050443561795934841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 48511893602365662911652485 9095980050443561795934841)
    ·
      refine ⟨6821985037832671346951131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9095980050443561795934841 6821985037832671346951131)
      ·
        refine ⟨10232977556749007020426697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6821985037832671346951131 10232977556749007020426697)
        ·
          refine ⟨7674733167561755265320023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10232977556749007020426697 7674733167561755265320023)
          ·
            refine ⟨11512099751342632897980035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7674733167561755265320023 11512099751342632897980035)
            ·
              refine ⟨17268149627013949346970053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11512099751342632897980035 17268149627013949346970053)
              ·
                refine ⟨3237778055065115502556885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17268149627013949346970053 3237778055065115502556885)
                ·
                  refine ⟨75885423165588644591177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3237778055065115502556885 75885423165588644591177)
                  ·
                    rfl

theorem cell23_1330077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 1, 4, 7].length) (baseStart_1330077 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1330077 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1330077 prefixEnd_1330077 := by exact prefixLift 1330077
  have htrace : WordTrace (prefixWord ++ tailWord_1330077) baseStart_1330077 baseEnd_1330077 := by
    simpa [prefixWord, tailWord_1330077, baseEnd_1330077] using wordTrace_append hprefix tailTrace_1330077
  have hstable : (prefixWord ++ tailWord_1330077).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1330077).length < 2 ^ (prefixWord ++ tailWord_1330077).sum := by decide
  have hdescent : baseEnd_1330077 < baseStart_1330077 := by decide
  rcases family_descends (prefixWord ++ tailWord_1330077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1330141 : List Nat := [1, 4, 3, 1, 2, 2, 2, 1, 2, 5]
def baseStart_1330141 : Nat := 118140960795 + 1330141 * 2 ^ 59
def prefixEnd_1330141 : Nat := 4983230072969 + 3 ^ 40 * 1330141 * 2
def baseEnd_1330141 : Nat := 227667223750728516973433

theorem tailTrace_1330141 : CollatzResearch.WordTrace tailWord_1330141 prefixEnd_1330141 227667223750728516973433 := by
  unfold tailWord_1330141
  simp only [CollatzResearch.WordTrace]
  refine ⟨48514227874133801841982277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32342818582755867894654851 48514227874133801841982277)
  ·
    refine ⟨9096417726400087845371677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 48514227874133801841982277 9096417726400087845371677)
    ·
      refine ⟨3411156647400032942014379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9096417726400087845371677 3411156647400032942014379)
      ·
        refine ⟨5116734971100049413021569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3411156647400032942014379 5116734971100049413021569)
        ·
          refine ⟨3837551228325037059766177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5116734971100049413021569 3837551228325037059766177)
          ·
            refine ⟨2878163421243777794824633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3837551228325037059766177 2878163421243777794824633)
            ·
              refine ⟨2158622565932833346118475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2878163421243777794824633 2158622565932833346118475)
              ·
                refine ⟨3237933848899250019177713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2158622565932833346118475 3237933848899250019177713)
                ·
                  refine ⟨2428450386674437514383285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3237933848899250019177713 2428450386674437514383285)
                  ·
                    refine ⟨227667223750728516973433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2428450386674437514383285 227667223750728516973433)
                    ·
                      rfl

theorem cell23_1330141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 2, 2, 1, 2, 5].length) (baseStart_1330141 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1330141 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1330141 prefixEnd_1330141 := by exact prefixLift 1330141
  have htrace : WordTrace (prefixWord ++ tailWord_1330141) baseStart_1330141 baseEnd_1330141 := by
    simpa [prefixWord, tailWord_1330141, baseEnd_1330141] using wordTrace_append hprefix tailTrace_1330141
  have hstable : (prefixWord ++ tailWord_1330141).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1330141).length < 2 ^ (prefixWord ++ tailWord_1330141).sum := by decide
  have hdescent : baseEnd_1330141 < baseStart_1330141 := by decide
  rcases family_descends (prefixWord ++ tailWord_1330141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1330144 : List Nat := [2, 1, 1, 3, 1, 1, 1, 1, 6, 4, 2]
def baseStart_1330144 : Nat := 118140960795 + 1330144 * 2 ^ 59
def prefixEnd_1330144 : Nat := 4983230072969 + 3 ^ 40 * 1330144 * 2
def baseEnd_1330144 : Nat := 683003211694149039182785

theorem tailTrace_1330144 : CollatzResearch.WordTrace tailWord_1330144 prefixEnd_1330144 683003211694149039182785 := by
  unfold tailWord_1330144
  simp only [CollatzResearch.WordTrace]
  refine ⟨24257168646561466677170743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32342891528748622236227657 24257168646561466677170743)
  ·
    refine ⟨36385752969842200015756115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24257168646561466677170743 36385752969842200015756115)
    ·
      refine ⟨54578629454763300023634173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36385752969842200015756115 54578629454763300023634173)
      ·
        refine ⟨20466986045536237508862815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 54578629454763300023634173 20466986045536237508862815)
        ·
          refine ⟨30700479068304356263294223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20466986045536237508862815 30700479068304356263294223)
          ·
            refine ⟨46050718602456534394941335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30700479068304356263294223 46050718602456534394941335)
            ·
              refine ⟨69076077903684801592412003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46050718602456534394941335 69076077903684801592412003)
              ·
                refine ⟨103614116855527202388618005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 69076077903684801592412003 103614116855527202388618005)
                ·
                  refine ⟨4856911727602837611966469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 103614116855527202388618005 4856911727602837611966469)
                  ·
                    refine ⟨910670948925532052243713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4856911727602837611966469 910670948925532052243713)
                    ·
                      refine ⟨683003211694149039182785, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 910670948925532052243713 683003211694149039182785)
                      ·
                        rfl

theorem cell23_1330144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 1, 6, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 1, 6, 4, 2].length) (baseStart_1330144 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1330144 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1330144 prefixEnd_1330144 := by exact prefixLift 1330144
  have htrace : WordTrace (prefixWord ++ tailWord_1330144) baseStart_1330144 baseEnd_1330144 := by
    simpa [prefixWord, tailWord_1330144, baseEnd_1330144] using wordTrace_append hprefix tailTrace_1330144
  have hstable : (prefixWord ++ tailWord_1330144).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1330144).length < 2 ^ (prefixWord ++ tailWord_1330144).sum := by decide
  have hdescent : baseEnd_1330144 < baseStart_1330144 := by decide
  rcases family_descends (prefixWord ++ tailWord_1330144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1330162 : List Nat := [3, 2, 1, 5, 2, 1, 2, 2, 5]
def baseStart_1330162 : Nat := 118140960795 + 1330162 * 2 ^ 59
def prefixEnd_1330162 : Nat := 4983230072969 + 3 ^ 40 * 1330162 * 2
def baseEnd_1330162 : Nat := 75890272705103329861967

theorem tailTrace_1330162 : CollatzResearch.WordTrace tailWord_1330162 prefixEnd_1330162 75890272705103329861967 := by
  unfold tailWord_1330162
  simp only [CollatzResearch.WordTrace]
  refine ⟨12128748451764430607124185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32343329204705148285664493 12128748451764430607124185)
  ·
    refine ⟨9096561338823322955343139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12128748451764430607124185 9096561338823322955343139)
    ·
      refine ⟨13644842008234984433014709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9096561338823322955343139 13644842008234984433014709)
      ·
        refine ⟨1279203938272029790595129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 13644842008234984433014709 1279203938272029790595129)
        ·
          refine ⟨959402953704022342946347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1279203938272029790595129 959402953704022342946347)
          ·
            refine ⟨1439104430556033514419521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 959402953704022342946347 1439104430556033514419521)
            ·
              refine ⟨1079328322917025135814641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1439104430556033514419521 1079328322917025135814641)
              ·
                refine ⟨809496242187768851860981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1079328322917025135814641 809496242187768851860981)
                ·
                  refine ⟨75890272705103329861967, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 809496242187768851860981 75890272705103329861967)
                  ·
                    rfl

theorem cell23_1330162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 2, 1, 2, 2, 5].length) (baseStart_1330162 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1330162 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1330162 prefixEnd_1330162 := by exact prefixLift 1330162
  have htrace : WordTrace (prefixWord ++ tailWord_1330162) baseStart_1330162 baseEnd_1330162 := by
    simpa [prefixWord, tailWord_1330162, baseEnd_1330162] using wordTrace_append hprefix tailTrace_1330162
  have hstable : (prefixWord ++ tailWord_1330162).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1330162).length < 2 ^ (prefixWord ++ tailWord_1330162).sum := by decide
  have hdescent : baseEnd_1330162 < baseStart_1330162 := by decide
  rcases family_descends (prefixWord ++ tailWord_1330162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1330184 : List Nat := [2, 1, 3, 2, 1, 3, 2, 3, 6]
def baseStart_1330184 : Nat := 118140960795 + 1330184 * 2 ^ 59
def prefixEnd_1330184 : Nat := 4983230072969 + 3 ^ 40 * 1330184 * 2
def baseEnd_1330184 : Nat := 75891527880036542520289

theorem tailTrace_1330184 : CollatzResearch.WordTrace tailWord_1330184 prefixEnd_1330184 75891527880036542520289 := by
  unfold tailWord_1330184
  simp only [CollatzResearch.WordTrace]
  refine ⟨24257898106489010092898803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32343864141985346790531737 24257898106489010092898803)
  ·
    refine ⟨36386847159733515139348205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24257898106489010092898803 36386847159733515139348205)
    ·
      refine ⟨13645067684900068177255577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 36386847159733515139348205 13645067684900068177255577)
      ·
        refine ⟨10233800763675051132941683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13645067684900068177255577 10233800763675051132941683)
        ·
          refine ⟨15350701145512576699412525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10233800763675051132941683 15350701145512576699412525)
          ·
            refine ⟨5756512929567216262279697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15350701145512576699412525 5756512929567216262279697)
            ·
              refine ⟨4317384697175412196709773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5756512929567216262279697 4317384697175412196709773)
              ·
                refine ⟨1619019261440779573766165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4317384697175412196709773 1619019261440779573766165)
                ·
                  refine ⟨75891527880036542520289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1619019261440779573766165 75891527880036542520289)
                  ·
                    rfl

theorem cell23_1330184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 2, 3, 6].length) (baseStart_1330184 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1330184 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1330184 prefixEnd_1330184 := by exact prefixLift 1330184
  have htrace : WordTrace (prefixWord ++ tailWord_1330184) baseStart_1330184 baseEnd_1330184 := by
    simpa [prefixWord, tailWord_1330184, baseEnd_1330184] using wordTrace_append hprefix tailTrace_1330184
  have hstable : (prefixWord ++ tailWord_1330184).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1330184).length < 2 ^ (prefixWord ++ tailWord_1330184).sum := by decide
  have hdescent : baseEnd_1330184 < baseStart_1330184 := by decide
  rcases family_descends (prefixWord ++ tailWord_1330184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1330205 : List Nat := [1, 4, 2, 2, 3, 1, 2, 3, 1, 4]
def baseStart_1330205 : Nat := 118140960795 + 1330205 * 2 ^ 59
def prefixEnd_1330205 : Nat := 4983230072969 + 3 ^ 40 * 1330205 * 2
def baseEnd_1330205 : Nat := 227678178004691100173335

theorem tailTrace_1330205 : CollatzResearch.WordTrace tailWord_1330205 prefixEnd_1330205 227678178004691100173335 := by
  unfold tailWord_1330205
  simp only [CollatzResearch.WordTrace]
  refine ⟨48516562145901940772312069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32344374763934627181541379 48516562145901940772312069)
  ·
    refine ⟨9096855402356613894808513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 48516562145901940772312069 9096855402356613894808513)
    ·
      refine ⟨6822641551767460421106385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9096855402356613894808513 6822641551767460421106385)
      ·
        refine ⟨5116981163825595315829789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6822641551767460421106385 5116981163825595315829789)
        ·
          refine ⟨1918867936434598243436171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5116981163825595315829789 1918867936434598243436171)
          ·
            refine ⟨2878301904651897365154257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1918867936434598243436171 2878301904651897365154257)
            ·
              refine ⟨2158726428488923023865693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2878301904651897365154257 2158726428488923023865693)
              ·
                refine ⟨809522410683346133949635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2158726428488923023865693 809522410683346133949635)
                ·
                  refine ⟨1214283616025019200924453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 809522410683346133949635 1214283616025019200924453)
                  ·
                    refine ⟨227678178004691100173335, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1214283616025019200924453 227678178004691100173335)
                    ·
                      rfl

theorem cell23_1330205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 3, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 3, 1, 2, 3, 1, 4].length) (baseStart_1330205 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1330205 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1330205 prefixEnd_1330205 := by exact prefixLift 1330205
  have htrace : WordTrace (prefixWord ++ tailWord_1330205) baseStart_1330205 baseEnd_1330205 := by
    simpa [prefixWord, tailWord_1330205, baseEnd_1330205] using wordTrace_append hprefix tailTrace_1330205
  have hstable : (prefixWord ++ tailWord_1330205).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1330205).length < 2 ^ (prefixWord ++ tailWord_1330205).sum := by decide
  have hdescent : baseEnd_1330205 < baseStart_1330205 := by decide
  rcases family_descends (prefixWord ++ tailWord_1330205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1330218 : List Nat := [3, 1, 4, 1, 3, 2, 1, 2, 6]
def baseStart_1330218 : Nat := 118140960795 + 1330218 * 2 ^ 59
def prefixEnd_1330218 : Nat := 4983230072969 + 3 ^ 40 * 1330218 * 2
def baseEnd_1330218 : Nat := 75893467695842416628605

theorem tailTrace_1330218 : CollatzResearch.WordTrace tailWord_1330218 prefixEnd_1330218 75893467695842416628605 := by
  unfold tailWord_1330218
  simp only [CollatzResearch.WordTrace]
  refine ⟨12129259073713710998133827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32344690863236562661690205 12129259073713710998133827)
  ·
    refine ⟨18193888610570566497200741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12129259073713710998133827 18193888610570566497200741)
    ·
      refine ⟨3411354114481981218225139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 18193888610570566497200741 3411354114481981218225139)
      ·
        refine ⟨5117031171722971827337709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3411354114481981218225139 5117031171722971827337709)
        ·
          refine ⟨1918886689396114435251641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5117031171722971827337709 1918886689396114435251641)
          ·
            refine ⟨1439165017047085826438731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1918886689396114435251641 1439165017047085826438731)
            ·
              refine ⟨2158747525570628739658097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1439165017047085826438731 2158747525570628739658097)
              ·
                refine ⟨1619060644177971554743573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2158747525570628739658097 1619060644177971554743573)
                ·
                  refine ⟨75893467695842416628605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1619060644177971554743573 75893467695842416628605)
                  ·
                    rfl

theorem cell23_1330218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 3, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 3, 2, 1, 2, 6].length) (baseStart_1330218 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1330218 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1330218 prefixEnd_1330218 := by exact prefixLift 1330218
  have htrace : WordTrace (prefixWord ++ tailWord_1330218) baseStart_1330218 baseEnd_1330218 := by
    simpa [prefixWord, tailWord_1330218, baseEnd_1330218] using wordTrace_append hprefix tailTrace_1330218
  have hstable : (prefixWord ++ tailWord_1330218).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1330218).length < 2 ^ (prefixWord ++ tailWord_1330218).sum := by decide
  have hdescent : baseEnd_1330218 < baseStart_1330218 := by decide
  rcases family_descends (prefixWord ++ tailWord_1330218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1330234 : List Nat := [3, 1, 1, 1, 3, 1, 2, 1, 5, 1, 4]
def baseStart_1330234 : Nat := 118140960795 + 1330234 * 2 ^ 59
def prefixEnd_1330234 : Nat := 4983230072969 + 3 ^ 40 * 1330234 * 2
def baseEnd_1330234 : Nat := 683049424953053687057371

theorem tailTrace_1330234 : CollatzResearch.WordTrace tailWord_1330234 prefixEnd_1330234 683049424953053687057371 := by
  unfold tailWord_1330234
  simp only [CollatzResearch.WordTrace]
  refine ⟨12129404965699219681279439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32345079908531252483411837 12129404965699219681279439)
  ·
    refine ⟨18194107448548829521919159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12129404965699219681279439 18194107448548829521919159)
    ·
      refine ⟨27291161172823244282878739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18194107448548829521919159 27291161172823244282878739)
      ·
        refine ⟨40936741759234866424318109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27291161172823244282878739 40936741759234866424318109)
        ·
          refine ⟨15351278159713074909119291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 40936741759234866424318109 15351278159713074909119291)
          ·
            refine ⟨23026917239569612363678937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15351278159713074909119291 23026917239569612363678937)
            ·
              refine ⟨17270187929677209272759203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23026917239569612363678937 17270187929677209272759203)
              ·
                refine ⟨25905281894515813909138805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17270187929677209272759203 25905281894515813909138805)
                ·
                  refine ⟨2428620177610857553981763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 25905281894515813909138805 2428620177610857553981763)
                  ·
                    refine ⟨3642930266416286330972645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2428620177610857553981763 3642930266416286330972645)
                    ·
                      refine ⟨683049424953053687057371, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3642930266416286330972645 683049424953053687057371)
                      ·
                        rfl

theorem cell23_1330234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 2, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 2, 1, 5, 1, 4].length) (baseStart_1330234 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1330234 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1330234 prefixEnd_1330234 := by exact prefixLift 1330234
  have htrace : WordTrace (prefixWord ++ tailWord_1330234) baseStart_1330234 baseEnd_1330234 := by
    simpa [prefixWord, tailWord_1330234, baseEnd_1330234] using wordTrace_append hprefix tailTrace_1330234
  have hstable : (prefixWord ++ tailWord_1330234).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1330234).length < 2 ^ (prefixWord ++ tailWord_1330234).sum := by decide
  have hdescent : baseEnd_1330234 < baseStart_1330234 := by decide
  rcases family_descends (prefixWord ++ tailWord_1330234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1330238 : List Nat := [4, 2, 1, 3, 1, 1, 1, 2, 1, 5, 2]
def baseStart_1330238 : Nat := 118140960795 + 1330238 * 2 ^ 59
def prefixEnd_1330238 : Nat := 4983230072969 + 3 ^ 40 * 1330238 * 2
def baseEnd_1330238 : Nat := 683051478875671671407353

theorem tailTrace_1330238 : CollatzResearch.WordTrace tailWord_1330238 prefixEnd_1330238 683051478875671671407353 := by
  unfold tailWord_1330238
  simp only [CollatzResearch.WordTrace]
  refine ⟨6064720719347798426032921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 32345177169854924938842245 6064720719347798426032921)
  ·
    refine ⟨4548540539510848819524691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6064720719347798426032921 4548540539510848819524691)
    ·
      refine ⟨6822810809266273229287037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4548540539510848819524691 6822810809266273229287037)
      ·
        refine ⟨2558554053474852460982639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6822810809266273229287037 2558554053474852460982639)
        ·
          refine ⟨3837831080212278691473959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2558554053474852460982639 3837831080212278691473959)
          ·
            refine ⟨5756746620318418037210939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3837831080212278691473959 5756746620318418037210939)
            ·
              refine ⟨8635119930477627055816409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5756746620318418037210939 8635119930477627055816409)
              ·
                refine ⟨6476339947858220291862307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8635119930477627055816409 6476339947858220291862307)
                ·
                  refine ⟨9714509921787330437793461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6476339947858220291862307 9714509921787330437793461)
                  ·
                    refine ⟨910735305167562228543137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9714509921787330437793461 910735305167562228543137)
                    ·
                      refine ⟨683051478875671671407353, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 910735305167562228543137 683051478875671671407353)
                      ·
                        rfl

theorem cell23_1330238_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 1, 2, 1, 5, 2].length) (baseStart_1330238 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1330238 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1330238 prefixEnd_1330238 := by exact prefixLift 1330238
  have htrace : WordTrace (prefixWord ++ tailWord_1330238) baseStart_1330238 baseEnd_1330238 := by
    simpa [prefixWord, tailWord_1330238, baseEnd_1330238] using wordTrace_append hprefix tailTrace_1330238
  have hstable : (prefixWord ++ tailWord_1330238).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1330238).length < 2 ^ (prefixWord ++ tailWord_1330238).sum := by decide
  have hdescent : baseEnd_1330238 < baseStart_1330238 := by decide
  rcases family_descends (prefixWord ++ tailWord_1330238) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1330254 : List Nat := [4, 1, 1, 1, 1, 3, 1, 2, 3, 1, 5]
def baseStart_1330254 : Nat := 118140960795 + 1330254 * 2 ^ 59
def prefixEnd_1330254 : Nat := 4983230072969 + 3 ^ 40 * 1330254 * 2
def baseEnd_1330254 : Nat := 683059694566143608807279

theorem tailTrace_1330254 : CollatzResearch.WordTrace tailWord_1330254 prefixEnd_1330254 683059694566143608807279 := by
  unfold tailWord_1330254
  simp only [CollatzResearch.WordTrace]
  refine ⟨6064793665340552767605727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 32345566215149614760563877 6064793665340552767605727)
  ·
    refine ⟨9097190498010829151408591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6064793665340552767605727 9097190498010829151408591)
    ·
      refine ⟨13645785747016243727112887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9097190498010829151408591 13645785747016243727112887)
      ·
        refine ⟨20468678620524365590669331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13645785747016243727112887 20468678620524365590669331)
        ·
          refine ⟨30703017930786548386003997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20468678620524365590669331 30703017930786548386003997)
          ·
            refine ⟨11513631724044955644751499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30703017930786548386003997 11513631724044955644751499)
            ·
              refine ⟨17270447586067433467127249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11513631724044955644751499 17270447586067433467127249)
              ·
                refine ⟨12952835689550575100345437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17270447586067433467127249 12952835689550575100345437)
                ·
                  refine ⟨4857313383581465662629539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12952835689550575100345437 4857313383581465662629539)
                  ·
                    refine ⟨7285970075372198493944309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4857313383581465662629539 7285970075372198493944309)
                    ·
                      refine ⟨683059694566143608807279, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7285970075372198493944309 683059694566143608807279)
                      ·
                        rfl

theorem cell23_1330254_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 1, 2, 3, 1, 5].length) (baseStart_1330254 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1330254 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1330254 prefixEnd_1330254 := by exact prefixLift 1330254
  have htrace : WordTrace (prefixWord ++ tailWord_1330254) baseStart_1330254 baseEnd_1330254 := by
    simpa [prefixWord, tailWord_1330254, baseEnd_1330254] using wordTrace_append hprefix tailTrace_1330254
  have hstable : (prefixWord ++ tailWord_1330254).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1330254).length < 2 ^ (prefixWord ++ tailWord_1330254).sum := by decide
  have hdescent : baseEnd_1330254 < baseStart_1330254 := by decide
  rcases family_descends (prefixWord ++ tailWord_1330254) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1330264 : List Nat := [2, 1, 2, 2, 1, 3, 2, 1, 3, 2, 4]
def baseStart_1330264 : Nat := 118140960795 + 1330264 * 2 ^ 59
def prefixEnd_1330264 : Nat := 4983230072969 + 3 ^ 40 * 1330264 * 2
def baseEnd_1330264 : Nat := 683064829372688569682233

theorem tailTrace_1330264 : CollatzResearch.WordTrace tailWord_1330264 prefixEnd_1330264 683064829372688569682233 := by
  unfold tailWord_1330264
  simp only [CollatzResearch.WordTrace]
  refine ⟨24259357026344096924354923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32345809368458795899139897 24259357026344096924354923)
  ·
    refine ⟨36389035539516145386532385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24259357026344096924354923 36389035539516145386532385)
    ·
      refine ⟨27291776654637109039899289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36389035539516145386532385 27291776654637109039899289)
      ·
        refine ⟨20468832490977831779924467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27291776654637109039899289 20468832490977831779924467)
        ·
          refine ⟨30703248736466747669886701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20468832490977831779924467 30703248736466747669886701)
          ·
            refine ⟨11513718276175030376207513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30703248736466747669886701 11513718276175030376207513)
            ·
              refine ⟨8635288707131272782155635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11513718276175030376207513 8635288707131272782155635)
              ·
                refine ⟨12952933060696909173233453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8635288707131272782155635 12952933060696909173233453)
                ·
                  refine ⟨4857349897761340939962545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12952933060696909173233453 4857349897761340939962545)
                  ·
                    refine ⟨3643012423321005704971909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4857349897761340939962545 3643012423321005704971909)
                    ·
                      refine ⟨683064829372688569682233, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3643012423321005704971909 683064829372688569682233)
                      ·
                        rfl

theorem cell23_1330264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 2, 1, 3, 2, 4].length) (baseStart_1330264 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1330264 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1330264 prefixEnd_1330264 := by exact prefixLift 1330264
  have htrace : WordTrace (prefixWord ++ tailWord_1330264) baseStart_1330264 baseEnd_1330264 := by
    simpa [prefixWord, tailWord_1330264, baseEnd_1330264] using wordTrace_append hprefix tailTrace_1330264
  have hstable : (prefixWord ++ tailWord_1330264).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1330264).length < 2 ^ (prefixWord ++ tailWord_1330264).sum := by decide
  have hdescent : baseEnd_1330264 < baseStart_1330264 := by decide
  rcases family_descends (prefixWord ++ tailWord_1330264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1330271 : List Nat := [1, 1, 2, 3, 1, 1, 3, 5, 1, 2, 3]
def baseStart_1330271 : Nat := 118140960795 + 1330271 * 2 ^ 59
def prefixEnd_1330271 : Nat := 4983230072969 + 3 ^ 40 * 1330271 * 2
def baseEnd_1330271 : Nat := 683068423737270042294701

theorem tailTrace_1330271 : CollatzResearch.WordTrace tailWord_1330271 prefixEnd_1330271 683068423737270042294701 := by
  unfold tailWord_1330271
  simp only [CollatzResearch.WordTrace]
  refine ⟨48518969363662834044214667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32345979575775222696143111 48518969363662834044214667)
  ·
    refine ⟨72778454045494251066322001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48518969363662834044214667 72778454045494251066322001)
    ·
      refine ⟨54583840534120688299741501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 72778454045494251066322001 54583840534120688299741501)
      ·
        refine ⟨20468940200295258112403063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 54583840534120688299741501 20468940200295258112403063)
        ·
          refine ⟨30703410300442887168604595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20468940200295258112403063 30703410300442887168604595)
          ·
            refine ⟨46055115450664330752906893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30703410300442887168604595 46055115450664330752906893)
            ·
              refine ⟨17270668293999124032340085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 46055115450664330752906893 17270668293999124032340085)
              ·
                refine ⟨1619125152562417878031883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 17270668293999124032340085 1619125152562417878031883)
                ·
                  refine ⟨2428687728843626817047825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1619125152562417878031883 2428687728843626817047825)
                  ·
                    refine ⟨1821515796632720112785869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2428687728843626817047825 1821515796632720112785869)
                    ·
                      refine ⟨683068423737270042294701, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1821515796632720112785869 683068423737270042294701)
                      ·
                        rfl

theorem cell23_1330271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 3, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 3, 5, 1, 2, 3].length) (baseStart_1330271 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1330271 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1330271 prefixEnd_1330271 := by exact prefixLift 1330271
  have htrace : WordTrace (prefixWord ++ tailWord_1330271) baseStart_1330271 baseEnd_1330271 := by
    simpa [prefixWord, tailWord_1330271, baseEnd_1330271] using wordTrace_append hprefix tailTrace_1330271
  have hstable : (prefixWord ++ tailWord_1330271).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1330271).length < 2 ^ (prefixWord ++ tailWord_1330271).sum := by decide
  have hdescent : baseEnd_1330271 < baseStart_1330271 := by decide
  rcases family_descends (prefixWord ++ tailWord_1330271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1330285 : List Nat := [1, 5, 1, 1, 2, 2, 3, 1, 3, 2, 2]
def baseStart_1330285 : Nat := 118140960795 + 1330285 * 2 ^ 59
def prefixEnd_1330285 : Nat := 4983230072969 + 3 ^ 40 * 1330285 * 2
def baseEnd_1330285 : Nat := 683075612466432987519637

theorem tailTrace_1330285 : CollatzResearch.WordTrace tailWord_1330285 prefixEnd_1330285 683075612466432987519637 := by
  unfold tailWord_1330285
  simp only [CollatzResearch.WordTrace]
  refine ⟨48519479985612114435224309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32346319990408076290149539 48519479985612114435224309)
  ·
    refine ⟨4548701248651135728302279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 48519479985612114435224309 4548701248651135728302279)
    ·
      refine ⟨6823051872976703592453419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4548701248651135728302279 6823051872976703592453419)
      ·
        refine ⟨10234577809465055388680129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6823051872976703592453419 10234577809465055388680129)
        ·
          refine ⟨7675933357098791541510097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10234577809465055388680129 7675933357098791541510097)
          ·
            refine ⟨5756950017824093656132573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7675933357098791541510097 5756950017824093656132573)
            ·
              refine ⟨2158856256684035121049715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5756950017824093656132573 2158856256684035121049715)
              ·
                refine ⟨3238284385026052681574573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2158856256684035121049715 3238284385026052681574573)
                ·
                  refine ⟨1214356644384769755590465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3238284385026052681574573 1214356644384769755590465)
                  ·
                    refine ⟨910767483288577316692849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1214356644384769755590465 910767483288577316692849)
                    ·
                      refine ⟨683075612466432987519637, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 910767483288577316692849 683075612466432987519637)
                      ·
                        rfl

theorem cell23_1330285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 3, 1, 3, 2, 2].length) (baseStart_1330285 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1330285 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1330285 prefixEnd_1330285 := by exact prefixLift 1330285
  have htrace : WordTrace (prefixWord ++ tailWord_1330285) baseStart_1330285 baseEnd_1330285 := by
    simpa [prefixWord, tailWord_1330285, baseEnd_1330285] using wordTrace_append hprefix tailTrace_1330285
  have hstable : (prefixWord ++ tailWord_1330285).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1330285).length < 2 ^ (prefixWord ++ tailWord_1330285).sum := by decide
  have hdescent : baseEnd_1330285 < baseStart_1330285 := by decide
  rcases family_descends (prefixWord ++ tailWord_1330285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1330301 : List Nat := [1, 4, 1, 1, 3, 1, 2, 3, 1, 3, 3]
def baseStart_1330301 : Nat := 118140960795 + 1330301 * 2 ^ 59
def prefixEnd_1330301 : Nat := 4983230072969 + 3 ^ 40 * 1330301 * 2
def baseEnd_1330301 : Nat := 683083828156904924919563

theorem tailTrace_1330301 : CollatzResearch.WordTrace tailWord_1330301 prefixEnd_1330301 683083828156904924919563 := by
  unfold tailWord_1330301
  simp only [CollatzResearch.WordTrace]
  refine ⟨48520063553554149167806757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32346709035702766111871171 48520063553554149167806757)
  ·
    refine ⟨9097511916291402968963767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 48520063553554149167806757 9097511916291402968963767)
    ·
      refine ⟨13646267874437104453445651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9097511916291402968963767 13646267874437104453445651)
      ·
        refine ⟨20469401811655656680168477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13646267874437104453445651 20469401811655656680168477)
        ·
          refine ⟨7676025679370871255063179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20469401811655656680168477 7676025679370871255063179)
          ·
            refine ⟨11514038519056306882594769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7676025679370871255063179 11514038519056306882594769)
            ·
              refine ⟨8635528889292230161946077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11514038519056306882594769 8635528889292230161946077)
              ·
                refine ⟨3238323333484586310729779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8635528889292230161946077 3238323333484586310729779)
                ·
                  refine ⟨4857485000226879466094669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3238323333484586310729779 4857485000226879466094669)
                  ·
                    refine ⟨1821556875085079799785501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4857485000226879466094669 1821556875085079799785501)
                    ·
                      refine ⟨683083828156904924919563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1821556875085079799785501 683083828156904924919563)
                      ·
                        rfl

theorem cell23_1330301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 2, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 2, 3, 1, 3, 3].length) (baseStart_1330301 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1330301 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1330301 prefixEnd_1330301 := by exact prefixLift 1330301
  have htrace : WordTrace (prefixWord ++ tailWord_1330301) baseStart_1330301 baseEnd_1330301 := by
    simpa [prefixWord, tailWord_1330301, baseEnd_1330301] using wordTrace_append hprefix tailTrace_1330301
  have hstable : (prefixWord ++ tailWord_1330301).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1330301).length < 2 ^ (prefixWord ++ tailWord_1330301).sum := by decide
  have hdescent : baseEnd_1330301 < baseStart_1330301 := by decide
  rcases family_descends (prefixWord ++ tailWord_1330301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1330302 : List Nat := [4, 2, 4, 1, 1, 1, 1, 1, 3, 1, 4]
def baseStart_1330302 : Nat := 118140960795 + 1330302 * 2 ^ 59
def prefixEnd_1330302 : Nat := 4983230072969 + 3 ^ 40 * 1330302 * 2
def baseEnd_1330302 : Nat := 683084341637559421007059

theorem tailTrace_1330302 : CollatzResearch.WordTrace tailWord_1330302 prefixEnd_1330302 683084341637559421007059 := by
  unfold tailWord_1330302
  simp only [CollatzResearch.WordTrace]
  refine ⟨6065012503318815792324145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 32346733351033684225728773 6065012503318815792324145)
  ·
    refine ⟨4548759377489111844243109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6065012503318815792324145 4548759377489111844243109)
    ·
      refine ⟨852892383279208470795583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4548759377489111844243109 852892383279208470795583)
      ·
        refine ⟨1279338574918812706193375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 852892383279208470795583 1279338574918812706193375)
        ·
          refine ⟨1919007862378219059290063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1279338574918812706193375 1919007862378219059290063)
          ·
            refine ⟨2878511793567328588935095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1919007862378219059290063 2878511793567328588935095)
            ·
              refine ⟨4317767690350992883402643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2878511793567328588935095 4317767690350992883402643)
              ·
                refine ⟨6476651535526489325103965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4317767690350992883402643 6476651535526489325103965)
                ·
                  refine ⟨2428744325822433496913987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6476651535526489325103965 2428744325822433496913987)
                  ·
                    refine ⟨3643116488733650245370981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2428744325822433496913987 3643116488733650245370981)
                    ·
                      refine ⟨683084341637559421007059, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3643116488733650245370981 683084341637559421007059)
                      ·
                        rfl

theorem cell23_1330302_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 1, 1, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 1, 1, 1, 1, 3, 1, 4].length) (baseStart_1330302 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1330302 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1330302 prefixEnd_1330302 := by exact prefixLift 1330302
  have htrace : WordTrace (prefixWord ++ tailWord_1330302) baseStart_1330302 baseEnd_1330302 := by
    simpa [prefixWord, tailWord_1330302, baseEnd_1330302] using wordTrace_append hprefix tailTrace_1330302
  have hstable : (prefixWord ++ tailWord_1330302).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1330302).length < 2 ^ (prefixWord ++ tailWord_1330302).sum := by decide
  have hdescent : baseEnd_1330302 < baseStart_1330302 := by decide
  rcases family_descends (prefixWord ++ tailWord_1330302) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1330305 : List Nat := [1, 2, 4, 2, 2, 3, 1, 2, 1, 2, 3]
def baseStart_1330305 : Nat := 118140960795 + 1330305 * 2 ^ 59
def prefixEnd_1330305 : Nat := 4983230072969 + 3 ^ 40 * 1330305 * 2
def baseEnd_1330305 : Nat := 683085882079522909269545

theorem tailTrace_1330305 : CollatzResearch.WordTrace tailWord_1330305 prefixEnd_1330305 683085882079522909269545 := by
  unfold tailWord_1330305
  simp only [CollatzResearch.WordTrace]
  refine ⟨48520209445539657850952369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32346806297026438567301579 48520209445539657850952369)
  ·
    refine ⟨36390157084154743388214277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48520209445539657850952369 36390157084154743388214277)
    ·
      refine ⟨6823154453279014385290177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 36390157084154743388214277 6823154453279014385290177)
      ·
        refine ⟨5117365839959260788967633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6823154453279014385290177 5117365839959260788967633)
        ·
          refine ⟨3838024379969445591725725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5117365839959260788967633 3838024379969445591725725)
          ·
            refine ⟨1439259142488542096897147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3838024379969445591725725 1439259142488542096897147)
            ·
              refine ⟨2158888713732813145345721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1439259142488542096897147 2158888713732813145345721)
              ·
                refine ⟨1619166535299609859009291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2158888713732813145345721 1619166535299609859009291)
                ·
                  refine ⟨2428749802949414788513937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1619166535299609859009291 2428749802949414788513937)
                  ·
                    refine ⟨1821562352212061091385453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2428749802949414788513937 1821562352212061091385453)
                    ·
                      refine ⟨683085882079522909269545, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1821562352212061091385453 683085882079522909269545)
                      ·
                        rfl

theorem cell23_1330305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 3, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 3, 1, 2, 1, 2, 3].length) (baseStart_1330305 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1330305 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1330305 prefixEnd_1330305 := by exact prefixLift 1330305
  have htrace : WordTrace (prefixWord ++ tailWord_1330305) baseStart_1330305 baseEnd_1330305 := by
    simpa [prefixWord, tailWord_1330305, baseEnd_1330305] using wordTrace_append hprefix tailTrace_1330305
  have hstable : (prefixWord ++ tailWord_1330305).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1330305).length < 2 ^ (prefixWord ++ tailWord_1330305).sum := by decide
  have hdescent : baseEnd_1330305 < baseStart_1330305 := by decide
  rcases family_descends (prefixWord ++ tailWord_1330305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1330318 : List Nat := [4, 1, 1, 3, 2, 2, 1, 2, 1, 3, 3]
def baseStart_1330318 : Nat := 118140960795 + 1330318 * 2 ^ 59
def prefixEnd_1330318 : Nat := 4983230072969 + 3 ^ 40 * 1330318 * 2
def baseEnd_1330318 : Nat := 683092557328031358406985

theorem tailTrace_1330318 : CollatzResearch.WordTrace tailWord_1330318 prefixEnd_1330318 683092557328031358406985 := by
  unfold tailWord_1330318
  simp only [CollatzResearch.WordTrace]
  refine ⟨6065085449311570133896951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 32347122396328374047450405 6065085449311570133896951)
  ·
    refine ⟨9097628173967355200845427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6065085449311570133896951 9097628173967355200845427)
    ·
      refine ⟨13646442260951032801268141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9097628173967355200845427 13646442260951032801268141)
      ·
        refine ⟨5117415847856637300475553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13646442260951032801268141 5117415847856637300475553)
        ·
          refine ⟨3838061885892477975356665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5117415847856637300475553 3838061885892477975356665)
          ·
            refine ⟨2878546414419358481517499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3838061885892477975356665 2878546414419358481517499)
            ·
              refine ⟨4317819621629037722276249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2878546414419358481517499 4317819621629037722276249)
              ·
                refine ⟨3238364716221778291707187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4317819621629037722276249 3238364716221778291707187)
                ·
                  refine ⟨4857547074332667437560781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3238364716221778291707187 4857547074332667437560781)
                  ·
                    refine ⟨1821580152874750289085293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4857547074332667437560781 1821580152874750289085293)
                    ·
                      refine ⟨683092557328031358406985, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1821580152874750289085293 683092557328031358406985)
                      ·
                        rfl

theorem cell23_1330318_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 2, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 2, 1, 2, 1, 3, 3].length) (baseStart_1330318 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1330318 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1330318 prefixEnd_1330318 := by exact prefixLift 1330318
  have htrace : WordTrace (prefixWord ++ tailWord_1330318) baseStart_1330318 baseEnd_1330318 := by
    simpa [prefixWord, tailWord_1330318, baseEnd_1330318] using wordTrace_append hprefix tailTrace_1330318
  have hstable : (prefixWord ++ tailWord_1330318).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1330318).length < 2 ^ (prefixWord ++ tailWord_1330318).sum := by decide
  have hdescent : baseEnd_1330318 < baseStart_1330318 := by decide
  rcases family_descends (prefixWord ++ tailWord_1330318) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1330391 : List Nat := [1, 1, 3, 2, 1, 2, 3, 2, 2, 3, 3]
def baseStart_1330391 : Nat := 118140960795 + 1330391 * 2 ^ 59
def prefixEnd_1330391 : Nat := 4983230072969 + 3 ^ 40 * 1330391 * 2
def baseEnd_1330391 : Nat := 683130041415809572794149

theorem tailTrace_1330391 : CollatzResearch.WordTrace tailWord_1330391 prefixEnd_1330391 683130041415809572794149 := by
  unfold tailWord_1330391
  simp only [CollatzResearch.WordTrace]
  refine ⟨48523346123228094538583027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32348897415485396359055351 48523346123228094538583027)
  ·
    refine ⟨72785019184842141807874541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48523346123228094538583027 72785019184842141807874541)
    ·
      refine ⟨27294382194315803177952953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 72785019184842141807874541 27294382194315803177952953)
      ·
        refine ⟨20470786645736852383464715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27294382194315803177952953 20470786645736852383464715)
        ·
          refine ⟨30706179968605278575197073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20470786645736852383464715 30706179968605278575197073)
          ·
            refine ⟨23029634976453958931397805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30706179968605278575197073 23029634976453958931397805)
            ·
              refine ⟨8636113116170234599274177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23029634976453958931397805 8636113116170234599274177)
              ·
                refine ⟨6477084837127675949455633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8636113116170234599274177 6477084837127675949455633)
                ·
                  refine ⟨4857813627845756962091725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6477084837127675949455633 4857813627845756962091725)
                  ·
                    refine ⟨1821680110442158860784397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4857813627845756962091725 1821680110442158860784397)
                    ·
                      refine ⟨683130041415809572794149, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1821680110442158860784397 683130041415809572794149)
                      ·
                        rfl

theorem cell23_1330391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 3, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 3, 2, 2, 3, 3].length) (baseStart_1330391 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1330391 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1330391 prefixEnd_1330391 := by exact prefixLift 1330391
  have htrace : WordTrace (prefixWord ++ tailWord_1330391) baseStart_1330391 baseEnd_1330391 := by
    simpa [prefixWord, tailWord_1330391, baseEnd_1330391] using wordTrace_append hprefix tailTrace_1330391
  have hstable : (prefixWord ++ tailWord_1330391).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1330391).length < 2 ^ (prefixWord ++ tailWord_1330391).sum := by decide
  have hdescent : baseEnd_1330391 < baseStart_1330391 := by decide
  rcases family_descends (prefixWord ++ tailWord_1330391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
