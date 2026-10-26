import V185TrunkScan19Chunk018

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental

namespace V185TrunkScan19Incremental

def tailWord_191682 : List Nat := [3, 5, 1, 1, 2, 2, 5]
def baseStart_191682 : Nat := 118140960795 + 191682 * 2 ^ 59
def prefixEnd_191682 : Nat := 4983230072969 + 3 ^ 40 * 191682 * 2
def baseEnd_191682 : Nat := 19441975074612202862909

theorem tailTrace_191682 : CollatzResearch.WordTrace tailWord_191682 prefixEnd_191682 19441975074612202862909 := by
  unfold tailWord_191682
  simp only [CollatzResearch.WordTrace]
  refine ⟨1747804222894081381102325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4660811261050883682939533 1747804222894081381102325)
  ·
    refine ⟨163856645896320129478343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 1747804222894081381102325 163856645896320129478343)
    ·
      refine ⟨245784968844480194217515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 163856645896320129478343 245784968844480194217515)
      ·
        refine ⟨368677453266720291326273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 245784968844480194217515 368677453266720291326273)
        ·
          refine ⟨276508089950040218494705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 368677453266720291326273 276508089950040218494705)
          ·
            refine ⟨207381067462530163871029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 276508089950040218494705 207381067462530163871029)
            ·
              refine ⟨19441975074612202862909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 207381067462530163871029 19441975074612202862909)
              ·
                rfl

theorem cell19_191682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 2, 2, 5].length) (baseStart_191682 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_191682 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_191682 prefixEnd_191682 := by exact prefixLift 191682
  have htrace : WordTrace (prefixWord ++ tailWord_191682) baseStart_191682 baseEnd_191682 := by
    simpa [prefixWord, tailWord_191682, baseEnd_191682] using wordTrace_append hprefix tailTrace_191682
  have hstable : (prefixWord ++ tailWord_191682).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_191682).length < 2 ^ (prefixWord ++ tailWord_191682).sum := by decide
  have hdescent : baseEnd_191682 < baseStart_191682 := by decide
  rcases family_descends (prefixWord ++ tailWord_191682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_191684 : List Nat := [2, 3, 3, 1, 4, 1, 5]
def baseStart_191684 : Nat := 118140960795 + 191684 * 2 ^ 59
def prefixEnd_191684 : Nat := 4983230072969 + 3 ^ 40 * 191684 * 2
def baseEnd_191684 : Nat := 19442177931167065514759

theorem tailTrace_191684 : CollatzResearch.WordTrace tailWord_191684 prefixEnd_191684 19442177931167065514759 := by
  unfold tailWord_191684
  simp only [CollatzResearch.WordTrace]
  refine ⟨3495644918784539932991053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4660859891712719910654737 3495644918784539932991053)
  ·
    refine ⟨1310866844544202474871645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3495644918784539932991053 1310866844544202474871645)
    ·
      refine ⟨491575066704075928076867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1310866844544202474871645 491575066704075928076867)
      ·
        refine ⟨737362600056113892115301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 491575066704075928076867 737362600056113892115301)
        ·
          refine ⟨138255487510521354771619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 737362600056113892115301 138255487510521354771619)
          ·
            refine ⟨207383231265782032157429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 138255487510521354771619 207383231265782032157429)
            ·
              refine ⟨19442177931167065514759, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 207383231265782032157429 19442177931167065514759)
              ·
                rfl

theorem cell19_191684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 4, 1, 5].length) (baseStart_191684 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_191684 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_191684 prefixEnd_191684 := by exact prefixLift 191684
  have htrace : WordTrace (prefixWord ++ tailWord_191684) baseStart_191684 baseEnd_191684 := by
    simpa [prefixWord, tailWord_191684, baseEnd_191684] using wordTrace_append hprefix tailTrace_191684
  have hstable : (prefixWord ++ tailWord_191684).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_191684).length < 2 ^ (prefixWord ++ tailWord_191684).sum := by decide
  have hdescent : baseEnd_191684 < baseStart_191684 := by decide
  rcases family_descends (prefixWord ++ tailWord_191684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_191726 : List Nat := [4, 1, 2, 1, 1, 1, 4, 5]
def baseStart_191726 : Nat := 118140960795 + 191726 * 2 ^ 59
def prefixEnd_191726 : Nat := 4983230072969 + 3 ^ 40 * 191726 * 2
def baseEnd_191726 : Nat := 58339313756457543610829

theorem tailTrace_191726 : CollatzResearch.WordTrace tailWord_191726 prefixEnd_191726 58339313756457543610829 := by
  unfold tailWord_191726
  simp only [CollatzResearch.WordTrace]
  refine ⟨874102712927115129876379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 4661881135611280692674021 874102712927115129876379)
  ·
    refine ⟨1311154069390672694814569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 874102712927115129876379 1311154069390672694814569)
    ·
      refine ⟨983365552043004521110927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1311154069390672694814569 983365552043004521110927)
      ·
        refine ⟨1475048328064506781666391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 983365552043004521110927 1475048328064506781666391)
        ·
          refine ⟨2212572492096760172499587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1475048328064506781666391 2212572492096760172499587)
          ·
            refine ⟨3318858738145140258749381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2212572492096760172499587 3318858738145140258749381)
            ·
              refine ⟨622286013402213798515509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3318858738145140258749381 622286013402213798515509)
              ·
                refine ⟨58339313756457543610829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 622286013402213798515509 58339313756457543610829)
                ·
                  rfl

theorem cell19_191726_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 4, 5].length) (baseStart_191726 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_191726 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_191726 prefixEnd_191726 := by exact prefixLift 191726
  have htrace : WordTrace (prefixWord ++ tailWord_191726) baseStart_191726 baseEnd_191726 := by
    simpa [prefixWord, tailWord_191726, baseEnd_191726] using wordTrace_append hprefix tailTrace_191726
  have hstable : (prefixWord ++ tailWord_191726).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_191726).length < 2 ^ (prefixWord ++ tailWord_191726).sum := by decide
  have hdescent : baseEnd_191726 < baseStart_191726 := by decide
  rcases family_descends (prefixWord ++ tailWord_191726) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_191747 : List Nat := [1, 1, 1, 3, 2, 11]
def baseStart_191747 : Nat := 118140960795 + 191747 * 2 ^ 59
def prefixEnd_191747 : Nat := 4983230072969 + 3 ^ 40 * 191747 * 2
def baseEnd_191747 : Nat := 6482855970881746349345

theorem tailTrace_191747 : CollatzResearch.WordTrace tailWord_191747 prefixEnd_191747 6482855970881746349345 := by
  unfold tailWord_191747
  simp only [CollatzResearch.WordTrace]
  refine ⟨6993587636340841625525495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4662391757560561083683663 6993587636340841625525495)
  ·
    refine ⟨10490381454511262438288243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6993587636340841625525495 10490381454511262438288243)
    ·
      refine ⟨15735572181766893657432365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10490381454511262438288243 15735572181766893657432365)
      ·
        refine ⟨5900839568162585121537137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15735572181766893657432365 5900839568162585121537137)
        ·
          refine ⟨4425629676121938841152853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5900839568162585121537137 4425629676121938841152853)
          ·
            refine ⟨6482855970881746349345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 4425629676121938841152853 6482855970881746349345)
            ·
              rfl

theorem cell19_191747_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 11].length) (baseStart_191747 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_191747 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_191747 prefixEnd_191747 := by exact prefixLift 191747
  have htrace : WordTrace (prefixWord ++ tailWord_191747) baseStart_191747 baseEnd_191747 := by
    simpa [prefixWord, tailWord_191747, baseEnd_191747] using wordTrace_append hprefix tailTrace_191747
  have hstable : (prefixWord ++ tailWord_191747).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_191747).length < 2 ^ (prefixWord ++ tailWord_191747).sum := by decide
  have hdescent : baseEnd_191747 < baseStart_191747 := by decide
  rcases family_descends (prefixWord ++ tailWord_191747) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_191781 : List Nat := [1, 3, 1, 2, 4, 2, 3, 3]
def baseStart_191781 : Nat := 118140960795 + 191781 * 2 ^ 59
def prefixEnd_191781 : Nat := 4983230072969 + 3 ^ 40 * 191781 * 2
def baseEnd_191781 : Nat := 58356049422233712388457

theorem tailTrace_191781 : CollatzResearch.WordTrace tailWord_191781 prefixEnd_191781 58356049422233712388457 := by
  unfold tailWord_191781
  simp only [CollatzResearch.WordTrace]
  refine ⟨6994827718217665432263197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4663218478811776954842131 6994827718217665432263197)
  ·
    refine ⟨2623060394331624537098699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6994827718217665432263197 2623060394331624537098699)
    ·
      refine ⟨3934590591497436805648049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2623060394331624537098699 3934590591497436805648049)
      ·
        refine ⟨2950942943623077604236037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3934590591497436805648049 2950942943623077604236037)
        ·
          refine ⟨553301801929327050794257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2950942943623077604236037 553301801929327050794257)
          ·
            refine ⟨414976351446995288095693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 553301801929327050794257 414976351446995288095693)
            ·
              refine ⟨155616131792623233035885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 414976351446995288095693 155616131792623233035885)
              ·
                refine ⟨58356049422233712388457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 155616131792623233035885 58356049422233712388457)
                ·
                  rfl

theorem cell19_191781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 2, 3, 3].length) (baseStart_191781 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_191781 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_191781 prefixEnd_191781 := by exact prefixLift 191781
  have htrace : WordTrace (prefixWord ++ tailWord_191781) baseStart_191781 baseEnd_191781 := by
    simpa [prefixWord, tailWord_191781, baseEnd_191781] using wordTrace_append hprefix tailTrace_191781
  have hstable : (prefixWord ++ tailWord_191781).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_191781).length < 2 ^ (prefixWord ++ tailWord_191781).sum := by decide
  have hdescent : baseEnd_191781 < baseStart_191781 := by decide
  rcases family_descends (prefixWord ++ tailWord_191781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_191798 : List Nat := [5, 1, 2, 3, 1, 1, 6]
def baseStart_191798 : Nat := 118140960795 + 191798 * 2 ^ 59
def prefixEnd_191798 : Nat := 4983230072969 + 3 ^ 40 * 191798 * 2
def baseEnd_191798 : Nat := 19453740754794236670211

theorem tailTrace_191798 : CollatzResearch.WordTrace tailWord_191798 prefixEnd_191798 19453740754794236670211 := by
  unfold tailWord_191798
  simp only [CollatzResearch.WordTrace]
  refine ⟨437215484947254833477003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 4663631839437384890421365 437215484947254833477003)
  ·
    refine ⟨655823227420882250215505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 437215484947254833477003 655823227420882250215505)
    ·
      refine ⟨491867420565661687661629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 655823227420882250215505 491867420565661687661629)
      ·
        refine ⟨184450282712123132873111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 491867420565661687661629 184450282712123132873111)
        ·
          refine ⟨276675424068184699309667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 184450282712123132873111 276675424068184699309667)
          ·
            refine ⟨415013136102277048964501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 276675424068184699309667 415013136102277048964501)
            ·
              refine ⟨19453740754794236670211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 415013136102277048964501 19453740754794236670211)
              ·
                rfl

theorem cell19_191798_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 1, 1, 6].length) (baseStart_191798 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_191798 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_191798 prefixEnd_191798 := by exact prefixLift 191798
  have htrace : WordTrace (prefixWord ++ tailWord_191798) baseStart_191798 baseEnd_191798 := by
    simpa [prefixWord, tailWord_191798, baseEnd_191798] using wordTrace_append hprefix tailTrace_191798
  have hstable : (prefixWord ++ tailWord_191798).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_191798).length < 2 ^ (prefixWord ++ tailWord_191798).sum := by decide
  have hdescent : baseEnd_191798 < baseStart_191798 := by decide
  rcases family_descends (prefixWord ++ tailWord_191798) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_191830 : List Nat := [5, 2, 3, 1, 1, 2, 2, 3]
def baseStart_191830 : Nat := 118140960795 + 191830 * 2 ^ 59
def prefixEnd_191830 : Nat := 4983230072969 + 3 ^ 40 * 191830 * 2
def baseEnd_191830 : Nat := 58370959379016117299435

theorem tailTrace_191830 : CollatzResearch.WordTrace tailWord_191830 prefixEnd_191830 58370959379016117299435 := by
  unfold tailWord_191830
  simp only [CollatzResearch.WordTrace]
  refine ⟨437288430940009175049809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 4664409930026764533864629 437288430940009175049809)
  ·
    refine ⟨327966323205006881287357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 437288430940009175049809 327966323205006881287357)
    ·
      refine ⟨122987371201877580482759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 327966323205006881287357 122987371201877580482759)
      ·
        refine ⟨184481056802816370724139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 122987371201877580482759 184481056802816370724139)
        ·
          refine ⟨276721585204224556086209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 184481056802816370724139 276721585204224556086209)
          ·
            refine ⟨207541188903168417064657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 276721585204224556086209 207541188903168417064657)
            ·
              refine ⟨155655891677376312798493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 207541188903168417064657 155655891677376312798493)
              ·
                refine ⟨58370959379016117299435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 155655891677376312798493 58370959379016117299435)
                ·
                  rfl

theorem cell19_191830_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 1, 2, 2, 3].length) (baseStart_191830 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_191830 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_191830 prefixEnd_191830 := by exact prefixLift 191830
  have htrace : WordTrace (prefixWord ++ tailWord_191830) baseStart_191830 baseEnd_191830 := by
    simpa [prefixWord, tailWord_191830, baseEnd_191830] using wordTrace_append hprefix tailTrace_191830
  have hstable : (prefixWord ++ tailWord_191830).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_191830).length < 2 ^ (prefixWord ++ tailWord_191830).sum := by decide
  have hdescent : baseEnd_191830 < baseStart_191830 := by decide
  rcases family_descends (prefixWord ++ tailWord_191830) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_191840 : List Nat := [2, 1, 1, 3, 4, 2, 1, 5]
def baseStart_191840 : Nat := 118140960795 + 191840 * 2 ^ 59
def prefixEnd_191840 : Nat := 4983230072969 + 3 ^ 40 * 191840 * 2
def baseEnd_191840 : Nat := 58374002227339057077185

theorem tailTrace_191840 : CollatzResearch.WordTrace tailWord_191840 prefixEnd_191840 58374002227339057077185 := by
  unfold tailWord_191840
  simp only [CollatzResearch.WordTrace]
  refine ⟨3498489812501959254330487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4664653083335945672440649 3498489812501959254330487)
  ·
    refine ⟨5247734718752938881495731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3498489812501959254330487 5247734718752938881495731)
    ·
      refine ⟨7871602078129408322243597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5247734718752938881495731 7871602078129408322243597)
      ·
        refine ⟨2951850779298528120841349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7871602078129408322243597 2951850779298528120841349)
        ·
          refine ⟨553472021118474022657753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2951850779298528120841349 553472021118474022657753)
          ·
            refine ⟨415104015838855516993315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 553472021118474022657753 415104015838855516993315)
            ·
              refine ⟨622656023758283275489973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 415104015838855516993315 622656023758283275489973)
              ·
                refine ⟨58374002227339057077185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 622656023758283275489973 58374002227339057077185)
                ·
                  rfl

theorem cell19_191840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 2, 1, 5].length) (baseStart_191840 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_191840 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_191840 prefixEnd_191840 := by exact prefixLift 191840
  have htrace : WordTrace (prefixWord ++ tailWord_191840) baseStart_191840 baseEnd_191840 := by
    simpa [prefixWord, tailWord_191840, baseEnd_191840] using wordTrace_append hprefix tailTrace_191840
  have hstable : (prefixWord ++ tailWord_191840).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_191840).length < 2 ^ (prefixWord ++ tailWord_191840).sum := by decide
  have hdescent : baseEnd_191840 < baseStart_191840 := by decide
  rcases family_descends (prefixWord ++ tailWord_191840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_191874 : List Nat := [3, 4, 2, 1, 1, 2, 2, 4]
def baseStart_191874 : Nat := 118140960795 + 191874 * 2 ^ 59
def prefixEnd_191874 : Nat := 4983230072969 + 3 ^ 40 * 191874 * 2
def baseEnd_191874 : Nat := 58384347911637052321537

theorem tailTrace_191874 : CollatzResearch.WordTrace tailWord_191874 prefixEnd_191874 58384347911637052321537 := by
  unfold tailWord_191874
  simp only [CollatzResearch.WordTrace]
  refine ⟨1749554926720185578849669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4665479804587161543599117 1749554926720185578849669)
  ·
    refine ⟨328041548760034796034313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1749554926720185578849669 328041548760034796034313)
    ·
      refine ⟨246031161570026097025735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 328041548760034796034313 246031161570026097025735)
      ·
        refine ⟨369046742355039145538603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 246031161570026097025735 369046742355039145538603)
        ·
          refine ⟨553570113532558718307905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 369046742355039145538603 553570113532558718307905)
          ·
            refine ⟨415177585149419038730929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 553570113532558718307905 415177585149419038730929)
            ·
              refine ⟨311383188862064279048197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 415177585149419038730929 311383188862064279048197)
              ·
                refine ⟨58384347911637052321537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 311383188862064279048197 58384347911637052321537)
                ·
                  rfl

theorem cell19_191874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 2, 2, 4].length) (baseStart_191874 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_191874 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_191874 prefixEnd_191874 := by exact prefixLift 191874
  have htrace : WordTrace (prefixWord ++ tailWord_191874) baseStart_191874 baseEnd_191874 := by
    simpa [prefixWord, tailWord_191874, baseEnd_191874] using wordTrace_append hprefix tailTrace_191874
  have hstable : (prefixWord ++ tailWord_191874).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_191874).length < 2 ^ (prefixWord ++ tailWord_191874).sum := by decide
  have hdescent : baseEnd_191874 < baseStart_191874 := by decide
  rcases family_descends (prefixWord ++ tailWord_191874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_191918 : List Nat := [4, 1, 14]
def baseStart_191918 : Nat := 118140960795 + 191918 * 2 ^ 59
def prefixEnd_191918 : Nat := 4983230072969 + 3 ^ 40 * 191918 * 2
def baseEnd_191918 : Nat := 240319903062790071373

theorem tailTrace_191918 : CollatzResearch.WordTrace tailWord_191918 prefixEnd_191918 240319903062790071373 := by
  unfold tailWord_191918
  simp only [CollatzResearch.WordTrace]
  refine ⟨874978064840167228750051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 4666549679147558553333605 874978064840167228750051)
  ·
    refine ⟨1312467097260250843125077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 874978064840167228750051 1312467097260250843125077)
    ·
      refine ⟨240319903062790071373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 14 1312467097260250843125077 240319903062790071373)
      ·
        rfl

theorem cell19_191918_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 14].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 14].length) (baseStart_191918 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_191918 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_191918 prefixEnd_191918 := by exact prefixLift 191918
  have htrace : WordTrace (prefixWord ++ tailWord_191918) baseStart_191918 baseEnd_191918 := by
    simpa [prefixWord, tailWord_191918, baseEnd_191918] using wordTrace_append hprefix tailTrace_191918
  have hstable : (prefixWord ++ tailWord_191918).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_191918).length < 2 ^ (prefixWord ++ tailWord_191918).sum := by decide
  have hdescent : baseEnd_191918 < baseStart_191918 := by decide
  rcases family_descends (prefixWord ++ tailWord_191918) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_191973 : List Nat := [1, 3, 1, 5, 1, 2, 6]
def baseStart_191973 : Nat := 118140960795 + 191973 * 2 ^ 59
def prefixEnd_191973 : Nat := 4983230072969 + 3 ^ 40 * 191973 * 2
def baseEnd_191973 : Nat := 19471490703344718707089

theorem tailTrace_191973 : CollatzResearch.WordTrace tailWord_191973 prefixEnd_191973 19471490703344718707089 := by
  unfold tailWord_191973
  simp only [CollatzResearch.WordTrace]
  refine ⟨7001830533522082223252573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4667887022348054815501715 7001830533522082223252573)
  ·
    refine ⟨2625686450070780833719715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7001830533522082223252573 2625686450070780833719715)
    ·
      refine ⟨3938529675106171250579573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2625686450070780833719715 3938529675106171250579573)
      ·
        refine ⟨369237157041203554741835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 3938529675106171250579573 369237157041203554741835)
        ·
          refine ⟨553855735561805332112753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 369237157041203554741835 553855735561805332112753)
          ·
            refine ⟨415391801671353999084565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 553855735561805332112753 415391801671353999084565)
            ·
              refine ⟨19471490703344718707089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 415391801671353999084565 19471490703344718707089)
              ·
                rfl

theorem cell19_191973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 2, 6].length) (baseStart_191973 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_191973 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_191973 prefixEnd_191973 := by exact prefixLift 191973
  have htrace : WordTrace (prefixWord ++ tailWord_191973) baseStart_191973 baseEnd_191973 := by
    simpa [prefixWord, tailWord_191973, baseEnd_191973] using wordTrace_append hprefix tailTrace_191973
  have hstable : (prefixWord ++ tailWord_191973).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_191973).length < 2 ^ (prefixWord ++ tailWord_191973).sum := by decide
  have hdescent : baseEnd_191973 < baseStart_191973 := by decide
  rcases family_descends (prefixWord ++ tailWord_191973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_191994 : List Nat := [3, 1, 1, 1, 1, 2, 4, 6]
def baseStart_191994 : Nat := 118140960795 + 191994 * 2 ^ 59
def prefixEnd_191994 : Nat := 4983230072969 + 3 ^ 40 * 191994 * 2
def baseEnd_191994 : Nat := 58420862091512329654543

theorem tailTrace_191994 : CollatzResearch.WordTrace tailWord_191994 prefixEnd_191994 58420862091512329654543 := by
  unfold tailWord_191994
  simp only [CollatzResearch.WordTrace]
  refine ⟨1750649116611500702441759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4668397644297335206511357 1750649116611500702441759)
  ·
    refine ⟨2625973674917251053662639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1750649116611500702441759 2625973674917251053662639)
    ·
      refine ⟨3938960512375876580493959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2625973674917251053662639 3938960512375876580493959)
      ·
        refine ⟨5908440768563814870740939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3938960512375876580493959 5908440768563814870740939)
        ·
          refine ⟨8862661152845722306111409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5908440768563814870740939 8862661152845722306111409)
          ·
            refine ⟨6646995864634291729583557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8862661152845722306111409 6646995864634291729583557)
            ·
              refine ⟨1246311724618929699296917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6646995864634291729583557 1246311724618929699296917)
              ·
                refine ⟨58420862091512329654543, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1246311724618929699296917 58420862091512329654543)
                ·
                  rfl

theorem cell19_191994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 4, 6].length) (baseStart_191994 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_191994 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_191994 prefixEnd_191994 := by exact prefixLift 191994
  have htrace : WordTrace (prefixWord ++ tailWord_191994) baseStart_191994 baseEnd_191994 := by
    simpa [prefixWord, tailWord_191994, baseEnd_191994] using wordTrace_append hprefix tailTrace_191994
  have hstable : (prefixWord ++ tailWord_191994).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_191994).length < 2 ^ (prefixWord ++ tailWord_191994).sum := by decide
  have hdescent : baseEnd_191994 < baseStart_191994 := by decide
  rcases family_descends (prefixWord ++ tailWord_191994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_192011 : List Nat := [1, 1, 1, 1, 8, 1, 1, 5]
def baseStart_192011 : Nat := 118140960795 + 192011 * 2 ^ 59
def prefixEnd_192011 : Nat := 4983230072969 + 3 ^ 40 * 192011 * 2
def baseEnd_192011 : Nat := 58426034933661327276719

theorem tailTrace_192011 : CollatzResearch.WordTrace tailWord_192011 prefixEnd_192011 58426034933661327276719 := by
  unfold tailWord_192011
  simp only [CollatzResearch.WordTrace]
  refine ⟨7003216507384414713135887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4668811004922943142090591 7003216507384414713135887)
  ·
    refine ⟨10504824761076622069703831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7003216507384414713135887 10504824761076622069703831)
    ·
      refine ⟨15757237141614933104555747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10504824761076622069703831 15757237141614933104555747)
      ·
        refine ⟨23635855712422399656833621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15757237141614933104555747 23635855712422399656833621)
        ·
          refine ⟨276982684129949995978519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 23635855712422399656833621 276982684129949995978519)
          ·
            refine ⟨415474026194924993967779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 276982684129949995978519 415474026194924993967779)
            ·
              refine ⟨623211039292387490951669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 415474026194924993967779 623211039292387490951669)
              ·
                refine ⟨58426034933661327276719, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 623211039292387490951669 58426034933661327276719)
                ·
                  rfl

theorem cell19_192011_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 8, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 8, 1, 1, 5].length) (baseStart_192011 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_192011 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_192011 prefixEnd_192011 := by exact prefixLift 192011
  have htrace : WordTrace (prefixWord ++ tailWord_192011) baseStart_192011 baseEnd_192011 := by
    simpa [prefixWord, tailWord_192011, baseEnd_192011] using wordTrace_append hprefix tailTrace_192011
  have hstable : (prefixWord ++ tailWord_192011).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_192011).length < 2 ^ (prefixWord ++ tailWord_192011).sum := by decide
  have hdescent : baseEnd_192011 < baseStart_192011 := by decide
  rcases family_descends (prefixWord ++ tailWord_192011) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_192051 : List Nat := [1, 1, 1, 2, 4, 3, 1, 6]
def baseStart_192051 : Nat := 118140960795 + 192051 * 2 ^ 59
def prefixEnd_192051 : Nat := 4983230072969 + 3 ^ 40 * 192051 * 2
def baseEnd_192051 : Nat := 58438206326953086387721

theorem tailTrace_192051 : CollatzResearch.WordTrace tailWord_192051 prefixEnd_192051 58438206326953086387721 := by
  unfold tailWord_192051
  simp only [CollatzResearch.WordTrace]
  refine ⟨7004675427239501544592007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4669783618159667696394671 7004675427239501544592007)
  ·
    refine ⟨10507013140859252316888011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7004675427239501544592007 10507013140859252316888011)
    ·
      refine ⟨15760519711288878475332017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10507013140859252316888011 15760519711288878475332017)
      ·
        refine ⟨11820389783466658856499013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15760519711288878475332017 11820389783466658856499013)
        ·
          refine ⟨2216323084399998535593565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11820389783466658856499013 2216323084399998535593565)
          ·
            refine ⟨831121156649999450847587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2216323084399998535593565 831121156649999450847587)
            ·
              refine ⟨1246681734974999176271381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 831121156649999450847587 1246681734974999176271381)
              ·
                refine ⟨58438206326953086387721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1246681734974999176271381 58438206326953086387721)
                ·
                  rfl

theorem cell19_192051_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 1, 6].length) (baseStart_192051 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_192051 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_192051 prefixEnd_192051 := by exact prefixLift 192051
  have htrace : WordTrace (prefixWord ++ tailWord_192051) baseStart_192051 baseEnd_192051 := by
    simpa [prefixWord, tailWord_192051, baseEnd_192051] using wordTrace_append hprefix tailTrace_192051
  have hstable : (prefixWord ++ tailWord_192051).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_192051).length < 2 ^ (prefixWord ++ tailWord_192051).sum := by decide
  have hdescent : baseEnd_192051 < baseStart_192051 := by decide
  rcases family_descends (prefixWord ++ tailWord_192051) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_192104 : List Nat := [2, 1, 4, 3, 1, 3, 1, 4]
def baseStart_192104 : Nat := 118140960795 + 192104 * 2 ^ 59
def prefixEnd_192104 : Nat := 4983230072969 + 3 ^ 40 * 192104 * 2
def baseEnd_192104 : Nat := 58454333423064667209799

theorem tailTrace_192104 : CollatzResearch.WordTrace tailWord_192104 prefixEnd_192104 58454333423064667209799 := by
  unfold tailWord_192104
  simp only [CollatzResearch.WordTrace]
  refine ⟨3503304248023745798135683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4671072330698327730847577 3503304248023745798135683)
  ·
    refine ⟨5254956372035618697203525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3503304248023745798135683 5254956372035618697203525)
    ·
      refine ⟨985304319756678505725661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5254956372035618697203525 985304319756678505725661)
      ·
        refine ⟨369489119908754439647123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 985304319756678505725661 369489119908754439647123)
        ·
          refine ⟨554233679863131659470685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 369489119908754439647123 554233679863131659470685)
          ·
            refine ⟨207837629948674372301507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 554233679863131659470685 207837629948674372301507)
            ·
              refine ⟨311756444923011558452261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 207837629948674372301507 311756444923011558452261)
              ·
                refine ⟨58454333423064667209799, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 311756444923011558452261 58454333423064667209799)
                ·
                  rfl

theorem cell19_192104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 3, 1, 4].length) (baseStart_192104 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_192104 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_192104 prefixEnd_192104 := by exact prefixLift 192104
  have htrace : WordTrace (prefixWord ++ tailWord_192104) baseStart_192104 baseEnd_192104 := by
    simpa [prefixWord, tailWord_192104, baseEnd_192104] using wordTrace_append hprefix tailTrace_192104
  have hstable : (prefixWord ++ tailWord_192104).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_192104).length < 2 ^ (prefixWord ++ tailWord_192104).sum := by decide
  have hdescent : baseEnd_192104 < baseStart_192104 := by decide
  rcases family_descends (prefixWord ++ tailWord_192104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_192106 : List Nat := [3, 1, 3, 2, 1, 2, 3, 4]
def baseStart_192106 : Nat := 118140960795 + 192106 * 2 ^ 59
def prefixEnd_192106 : Nat := 4983230072969 + 3 ^ 40 * 192106 * 2
def baseEnd_192106 : Nat := 58454941992729255165349

theorem tailTrace_192106 : CollatzResearch.WordTrace tailWord_192106 prefixEnd_192106 58454941992729255165349 := by
  unfold tailWord_192106
  simp only [CollatzResearch.WordTrace]
  refine ⟨1751670360510061484461043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4671120961360163958562781 1751670360510061484461043)
  ·
    refine ⟨2627505540765092226691565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1751670360510061484461043 2627505540765092226691565)
    ·
      refine ⟨985314577786909585009337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2627505540765092226691565 985314577786909585009337)
      ·
        refine ⟨738985933340182188757003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 985314577786909585009337 738985933340182188757003)
        ·
          refine ⟨1108478900010273283135505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 738985933340182188757003 1108478900010273283135505)
          ·
            refine ⟨831359175007704962351629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1108478900010273283135505 831359175007704962351629)
            ·
              refine ⟨311759690627889360881861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 831359175007704962351629 311759690627889360881861)
              ·
                refine ⟨58454941992729255165349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 311759690627889360881861 58454941992729255165349)
                ·
                  rfl

theorem cell19_192106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 3, 4].length) (baseStart_192106 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_192106 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_192106 prefixEnd_192106 := by exact prefixLift 192106
  have htrace : WordTrace (prefixWord ++ tailWord_192106) baseStart_192106 baseEnd_192106 := by
    simpa [prefixWord, tailWord_192106, baseEnd_192106] using wordTrace_append hprefix tailTrace_192106
  have hstable : (prefixWord ++ tailWord_192106).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_192106).length < 2 ^ (prefixWord ++ tailWord_192106).sum := by decide
  have hdescent : baseEnd_192106 < baseStart_192106 := by decide
  rcases family_descends (prefixWord ++ tailWord_192106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_192241 : List Nat := [1, 2, 2, 2, 2, 3, 2, 5]
def baseStart_192241 : Nat := 118140960795 + 192241 * 2 ^ 59
def prefixEnd_192241 : Nat := 4983230072969 + 3 ^ 40 * 192241 * 2
def baseEnd_192241 : Nat := 58496020445088942164981

theorem tailTrace_192241 : CollatzResearch.WordTrace tailWord_192241 prefixEnd_192241 58496020445088942164981 := by
  unfold tailWord_192241
  simp only [CollatzResearch.WordTrace]
  refine ⟨7011605296551163994008577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4674403531034109329339051 7011605296551163994008577)
  ·
    refine ⟨5258703972413372995506433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7011605296551163994008577 5258703972413372995506433)
    ·
      refine ⟨3944027979310029746629825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5258703972413372995506433 3944027979310029746629825)
      ·
        refine ⟨2958020984482522309972369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3944027979310029746629825 2958020984482522309972369)
        ·
          refine ⟨2218515738361891732479277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2958020984482522309972369 2218515738361891732479277)
          ·
            refine ⟨831943401885709399679729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2218515738361891732479277 831943401885709399679729)
            ·
              refine ⟨623957551414282049759797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 831943401885709399679729 623957551414282049759797)
              ·
                refine ⟨58496020445088942164981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 623957551414282049759797 58496020445088942164981)
                ·
                  rfl

theorem cell19_192241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 2, 5].length) (baseStart_192241 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_192241 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_192241 prefixEnd_192241 := by exact prefixLift 192241
  have htrace : WordTrace (prefixWord ++ tailWord_192241) baseStart_192241 baseEnd_192241 := by
    simpa [prefixWord, tailWord_192241, baseEnd_192241] using wordTrace_append hprefix tailTrace_192241
  have hstable : (prefixWord ++ tailWord_192241).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_192241).length < 2 ^ (prefixWord ++ tailWord_192241).sum := by decide
  have hdescent : baseEnd_192241 < baseStart_192241 := by decide
  rcases family_descends (prefixWord ++ tailWord_192241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_192260 : List Nat := [2, 3, 2, 2, 1, 9]
def baseStart_192260 : Nat := 118140960795 + 192260 * 2 ^ 59
def prefixEnd_192260 : Nat := 4983230072969 + 3 ^ 40 * 192260 * 2
def baseEnd_192260 : Nat := 6500200206322503082523

theorem tailTrace_192260 : CollatzResearch.WordTrace tailWord_192260 prefixEnd_192260 6500200206322503082523 := by
  unfold tailWord_192260
  simp only [CollatzResearch.WordTrace]
  refine ⟨3506149141741165119475117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4674865522321553492633489 3506149141741165119475117)
  ·
    refine ⟨1314805928152936919803169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3506149141741165119475117 1314805928152936919803169)
    ·
      refine ⟨986104446114702689852377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1314805928152936919803169 986104446114702689852377)
      ·
        refine ⟨739578334586027017389283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 986104446114702689852377 739578334586027017389283)
        ·
          refine ⟨1109367501879040526083925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 739578334586027017389283 1109367501879040526083925)
          ·
            refine ⟨6500200206322503082523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 1109367501879040526083925 6500200206322503082523)
            ·
              rfl

theorem cell19_192260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 9].length) (baseStart_192260 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_192260 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_192260 prefixEnd_192260 := by exact prefixLift 192260
  have htrace : WordTrace (prefixWord ++ tailWord_192260) baseStart_192260 baseEnd_192260 := by
    simpa [prefixWord, tailWord_192260, baseEnd_192260] using wordTrace_append hprefix tailTrace_192260
  have hstable : (prefixWord ++ tailWord_192260).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_192260).length < 2 ^ (prefixWord ++ tailWord_192260).sum := by decide
  have hdescent : baseEnd_192260 < baseStart_192260 := by decide
  rcases family_descends (prefixWord ++ tailWord_192260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_192269 : List Nat := [1, 7, 2, 1, 1, 2, 1, 4]
def baseStart_192269 : Nat := 118140960795 + 192269 * 2 ^ 59
def prefixEnd_192269 : Nat := 4983230072969 + 3 ^ 40 * 192269 * 2
def baseEnd_192269 : Nat := 58504540420393173542683

theorem tailTrace_192269 : CollatzResearch.WordTrace tailWord_192269 prefixEnd_192269 58504540420393173542683 := by
  unfold tailWord_192269
  simp only [CollatzResearch.WordTrace]
  refine ⟨7012626540449724776027861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4675084360299816517351907 7012626540449724776027861)
  ·
    refine ⟨164358434541790424438153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 7012626540449724776027861 164358434541790424438153)
    ·
      refine ⟨123268825906342818328615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 164358434541790424438153 123268825906342818328615)
      ·
        refine ⟨184903238859514227492923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 123268825906342818328615 184903238859514227492923)
        ·
          refine ⟨277354858289271341239385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 184903238859514227492923 277354858289271341239385)
          ·
            refine ⟨208016143716953505929539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 277354858289271341239385 208016143716953505929539)
            ·
              refine ⟨312024215575430258894309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 208016143716953505929539 312024215575430258894309)
              ·
                refine ⟨58504540420393173542683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 312024215575430258894309 58504540420393173542683)
                ·
                  rfl

theorem cell19_192269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 1, 2, 1, 4].length) (baseStart_192269 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_192269 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_192269 prefixEnd_192269 := by exact prefixLift 192269
  have htrace : WordTrace (prefixWord ++ tailWord_192269) baseStart_192269 baseEnd_192269 := by
    simpa [prefixWord, tailWord_192269, baseEnd_192269] using wordTrace_append hprefix tailTrace_192269
  have hstable : (prefixWord ++ tailWord_192269).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_192269).length < 2 ^ (prefixWord ++ tailWord_192269).sum := by decide
  have hdescent : baseEnd_192269 < baseStart_192269 := by decide
  rcases family_descends (prefixWord ++ tailWord_192269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_192277 : List Nat := [1, 3, 2, 1, 2, 5, 1, 4]
def baseStart_192277 : Nat := 118140960795 + 192277 * 2 ^ 59
def prefixEnd_192277 : Nat := 4983230072969 + 3 ^ 40 * 192277 * 2
def baseEnd_192277 : Nat := 58506974699051525364883

theorem tailTrace_192277 : CollatzResearch.WordTrace tailWord_192277 prefixEnd_192277 58506974699051525364883 := by
  unfold tailWord_192277
  simp only [CollatzResearch.WordTrace]
  refine ⟨7012918324420742142319085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4675278882947161428212723 7012918324420742142319085)
  ·
    refine ⟨2629844371657778303369657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7012918324420742142319085 2629844371657778303369657)
    ·
      refine ⟨1972383278743333727527243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2629844371657778303369657 1972383278743333727527243)
      ·
        refine ⟨2958574918115000591290865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1972383278743333727527243 2958574918115000591290865)
        ·
          refine ⟨2218931188586250443468149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2958574918115000591290865 2218931188586250443468149)
          ·
            refine ⟨208024798929960979075139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 2218931188586250443468149 208024798929960979075139)
            ·
              refine ⟨312037198394941468612709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 208024798929960979075139 312037198394941468612709)
              ·
                refine ⟨58506974699051525364883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 312037198394941468612709 58506974699051525364883)
                ·
                  rfl

theorem cell19_192277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 5, 1, 4].length) (baseStart_192277 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_192277 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_192277 prefixEnd_192277 := by exact prefixLift 192277
  have htrace : WordTrace (prefixWord ++ tailWord_192277) baseStart_192277 baseEnd_192277 := by
    simpa [prefixWord, tailWord_192277, baseEnd_192277] using wordTrace_append hprefix tailTrace_192277
  have hstable : (prefixWord ++ tailWord_192277).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_192277).length < 2 ^ (prefixWord ++ tailWord_192277).sum := by decide
  have hdescent : baseEnd_192277 < baseStart_192277 := by decide
  rcases family_descends (prefixWord ++ tailWord_192277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_192391 : List Nat := [1, 1, 4, 2, 4, 1, 2, 4]
def baseStart_192391 : Nat := 118140960795 + 192391 * 2 ^ 59
def prefixEnd_192391 : Nat := 4983230072969 + 3 ^ 40 * 192391 * 2
def baseEnd_192391 : Nat := 58541663169933038831239

theorem tailTrace_192391 : CollatzResearch.WordTrace tailWord_192391 prefixEnd_192391 58541663169933038831239 := by
  unfold tailWord_192391
  simp only [CollatzResearch.WordTrace]
  refine ⟨7017076246007739611969027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4678050830671826407979351 7017076246007739611969027)
  ·
    refine ⟨10525614369011609417953541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7017076246007739611969027 10525614369011609417953541)
    ·
      refine ⟨1973552694189676765866289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10525614369011609417953541 1973552694189676765866289)
      ·
        refine ⟨1480164520642257574399717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1973552694189676765866289 1480164520642257574399717)
        ·
          refine ⟨277530847620423295199947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1480164520642257574399717 277530847620423295199947)
          ·
            refine ⟨416296271430634942799921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 277530847620423295199947 416296271430634942799921)
            ·
              refine ⟨312222203572976207099941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 416296271430634942799921 312222203572976207099941)
              ·
                refine ⟨58541663169933038831239, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 312222203572976207099941 58541663169933038831239)
                ·
                  rfl

theorem cell19_192391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 4, 1, 2, 4].length) (baseStart_192391 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_192391 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_192391 prefixEnd_192391 := by exact prefixLift 192391
  have htrace : WordTrace (prefixWord ++ tailWord_192391) baseStart_192391 baseEnd_192391 := by
    simpa [prefixWord, tailWord_192391, baseEnd_192391] using wordTrace_append hprefix tailTrace_192391
  have hstable : (prefixWord ++ tailWord_192391).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_192391).length < 2 ^ (prefixWord ++ tailWord_192391).sum := by decide
  have hdescent : baseEnd_192391 < baseStart_192391 := by decide
  rcases family_descends (prefixWord ++ tailWord_192391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_192393 : List Nat := [1, 2, 1, 1, 5, 1, 4, 4]
def baseStart_192393 : Nat := 118140960795 + 192393 * 2 ^ 59
def prefixEnd_192393 : Nat := 4983230072969 + 3 ^ 40 * 192393 * 2
def baseEnd_192393 : Nat := 58542271739597626786789

theorem tailTrace_192393 : CollatzResearch.WordTrace tailWord_192393 prefixEnd_192393 58542271739597626786789 := by
  unfold tailWord_192393
  simp only [CollatzResearch.WordTrace]
  refine ⟨7017149192000493953541833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4678099461333662635694555 7017149192000493953541833)
  ·
    refine ⟨5262861894000370465156375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7017149192000493953541833 5262861894000370465156375)
    ·
      refine ⟨7894292841000555697734563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5262861894000370465156375 7894292841000555697734563)
      ·
        refine ⟨11841439261500833546601845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7894292841000555697734563 11841439261500833546601845)
        ·
          refine ⟨1110134930765703144993923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 11841439261500833546601845 1110134930765703144993923)
          ·
            refine ⟨1665202396148554717490885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1110134930765703144993923 1665202396148554717490885)
            ·
              refine ⟨312225449277854009529541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1665202396148554717490885 312225449277854009529541)
              ·
                refine ⟨58542271739597626786789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 312225449277854009529541 58542271739597626786789)
                ·
                  rfl

theorem cell19_192393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 4, 4].length) (baseStart_192393 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_192393 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_192393 prefixEnd_192393 := by exact prefixLift 192393
  have htrace : WordTrace (prefixWord ++ tailWord_192393) baseStart_192393 baseEnd_192393 := by
    simpa [prefixWord, tailWord_192393, baseEnd_192393] using wordTrace_append hprefix tailTrace_192393
  have hstable : (prefixWord ++ tailWord_192393).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_192393).length < 2 ^ (prefixWord ++ tailWord_192393).sum := by decide
  have hdescent : baseEnd_192393 < baseStart_192393 := by decide
  rcases family_descends (prefixWord ++ tailWord_192393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_192444 : List Nat := [2, 2, 2, 5, 2, 1, 1, 4]
def baseStart_192444 : Nat := 118140960795 + 192444 * 2 ^ 59
def prefixEnd_192444 : Nat := 4983230072969 + 3 ^ 40 * 192444 * 2
def baseEnd_192444 : Nat := 58557790266044619653317

theorem tailTrace_192444 : CollatzResearch.WordTrace tailWord_192444 prefixEnd_192444 58557790266044619653317 := by
  unfold tailWord_192444
  simp only [CollatzResearch.WordTrace]
  refine ⟨3509504657407864831824193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4679339543210486442432257 3509504657407864831824193)
  ·
    refine ⟨2632128493055898623868145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3509504657407864831824193 2632128493055898623868145)
    ·
      refine ⟨1974096369791923967901109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2632128493055898623868145 1974096369791923967901109)
      ·
        refine ⟨185071534667992871990729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 1974096369791923967901109 185071534667992871990729)
        ·
          refine ⟨138803651000994653993047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 185071534667992871990729 138803651000994653993047)
          ·
            refine ⟨208205476501491980989571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 138803651000994653993047 208205476501491980989571)
            ·
              refine ⟨312308214752237971484357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 208205476501491980989571 312308214752237971484357)
              ·
                refine ⟨58557790266044619653317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 312308214752237971484357 58557790266044619653317)
                ·
                  rfl

theorem cell19_192444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 2, 1, 1, 4].length) (baseStart_192444 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_192444 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_192444 prefixEnd_192444 := by exact prefixLift 192444
  have htrace : WordTrace (prefixWord ++ tailWord_192444) baseStart_192444 baseEnd_192444 := by
    simpa [prefixWord, tailWord_192444, baseEnd_192444] using wordTrace_append hprefix tailTrace_192444
  have hstable : (prefixWord ++ tailWord_192444).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_192444).length < 2 ^ (prefixWord ++ tailWord_192444).sum := by decide
  have hdescent : baseEnd_192444 < baseStart_192444 := by decide
  rcases family_descends (prefixWord ++ tailWord_192444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_192518 : List Nat := [6, 2, 1, 2, 1, 1, 1, 5]
def baseStart_192518 : Nat := 118140960795 + 192518 * 2 ^ 59
def prefixEnd_192518 : Nat := 4983230072969 + 3 ^ 40 * 192518 * 2
def baseEnd_192518 : Nat := 58580307343634374008671

theorem tailTrace_192518 : CollatzResearch.WordTrace tailWord_192518 prefixEnd_192518 58580307343634374008671 := by
  unfold tailWord_192518
  simp only [CollatzResearch.WordTrace]
  refine ⟨219428384892113759432569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 4681138877698426867894805 219428384892113759432569)
  ·
    refine ⟨164571288669085319574427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 219428384892113759432569 164571288669085319574427)
    ·
      refine ⟨246856933003627979361641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 164571288669085319574427 246856933003627979361641)
      ·
        refine ⟨185142699752720984521231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 246856933003627979361641 185142699752720984521231)
        ·
          refine ⟨277714049629081476781847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 185142699752720984521231 277714049629081476781847)
          ·
            refine ⟨416571074443622215172771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 277714049629081476781847 416571074443622215172771)
            ·
              refine ⟨624856611665433322759157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 416571074443622215172771 624856611665433322759157)
              ·
                refine ⟨58580307343634374008671, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 624856611665433322759157 58580307343634374008671)
                ·
                  rfl

theorem cell19_192518_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 1, 1, 1, 5].length) (baseStart_192518 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_192518 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_192518 prefixEnd_192518 := by exact prefixLift 192518
  have htrace : WordTrace (prefixWord ++ tailWord_192518) baseStart_192518 baseEnd_192518 := by
    simpa [prefixWord, tailWord_192518, baseEnd_192518] using wordTrace_append hprefix tailTrace_192518
  have hstable : (prefixWord ++ tailWord_192518).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_192518).length < 2 ^ (prefixWord ++ tailWord_192518).sum := by decide
  have hdescent : baseEnd_192518 < baseStart_192518 := by decide
  rcases family_descends (prefixWord ++ tailWord_192518) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_192522 : List Nat := [3, 1, 2, 2, 4, 2, 2, 3]
def baseStart_192522 : Nat := 118140960795 + 192522 * 2 ^ 59
def prefixEnd_192522 : Nat := 4983230072969 + 3 ^ 40 * 192522 * 2
def baseEnd_192522 : Nat := 58581524482963549919771

theorem tailTrace_192522 : CollatzResearch.WordTrace tailWord_192522 prefixEnd_192522 58581524482963549919771 := by
  unfold tailWord_192522
  simp only [CollatzResearch.WordTrace]
  refine ⟨1755463552133287246246955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4681236139022099323325213 1755463552133287246246955)
  ·
    refine ⟨2633195328199930869370433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1755463552133287246246955 2633195328199930869370433)
    ·
      refine ⟨1974896496149948152027825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2633195328199930869370433 1974896496149948152027825)
      ·
        refine ⟨1481172372112461114020869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1974896496149948152027825 1481172372112461114020869)
        ·
          refine ⟨277719819771086458878913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1481172372112461114020869 277719819771086458878913)
          ·
            refine ⟨208289864828314844159185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 277719819771086458878913 208289864828314844159185)
            ·
              refine ⟨156217398621236133119389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 208289864828314844159185 156217398621236133119389)
              ·
                refine ⟨58581524482963549919771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 156217398621236133119389 58581524482963549919771)
                ·
                  rfl

theorem cell19_192522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 4, 2, 2, 3].length) (baseStart_192522 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_192522 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_192522 prefixEnd_192522 := by exact prefixLift 192522
  have htrace : WordTrace (prefixWord ++ tailWord_192522) baseStart_192522 baseEnd_192522 := by
    simpa [prefixWord, tailWord_192522, baseEnd_192522] using wordTrace_append hprefix tailTrace_192522
  have hstable : (prefixWord ++ tailWord_192522).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_192522).length < 2 ^ (prefixWord ++ tailWord_192522).sum := by decide
  have hdescent : baseEnd_192522 < baseStart_192522 := by decide
  rcases family_descends (prefixWord ++ tailWord_192522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_192526 : List Nat := [4, 1, 1, 2, 2, 1, 3, 5]
def baseStart_192526 : Nat := 118140960795 + 192526 * 2 ^ 59
def prefixEnd_192526 : Nat := 4983230072969 + 3 ^ 40 * 192526 * 2
def baseEnd_192526 : Nat := 58582741622292725830871

theorem tailTrace_192526 : CollatzResearch.WordTrace tailWord_192526 prefixEnd_192526 58582741622292725830871 := by
  unfold tailWord_192526
  simp only [CollatzResearch.WordTrace]
  refine ⟨877750012564832208516679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 4681333400345771778755621 877750012564832208516679)
  ·
    refine ⟨1316625018847248312775019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 877750012564832208516679 1316625018847248312775019)
    ·
      refine ⟨1974937528270872469162529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1316625018847248312775019 1974937528270872469162529)
      ·
        refine ⟨1481203146203154351871897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1974937528270872469162529 1481203146203154351871897)
        ·
          refine ⟨1110902359652365763903923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1481203146203154351871897 1110902359652365763903923)
          ·
            refine ⟨1666353539478548645855885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1110902359652365763903923 1666353539478548645855885)
            ·
              refine ⟨624882577304455742195957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1666353539478548645855885 624882577304455742195957)
              ·
                refine ⟨58582741622292725830871, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 624882577304455742195957 58582741622292725830871)
                ·
                  rfl

theorem cell19_192526_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 3, 5].length) (baseStart_192526 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_192526 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_192526 prefixEnd_192526 := by exact prefixLift 192526
  have htrace : WordTrace (prefixWord ++ tailWord_192526) baseStart_192526 baseEnd_192526 := by
    simpa [prefixWord, tailWord_192526, baseEnd_192526] using wordTrace_append hprefix tailTrace_192526
  have hstable : (prefixWord ++ tailWord_192526).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_192526).length < 2 ^ (prefixWord ++ tailWord_192526).sum := by decide
  have hdescent : baseEnd_192526 < baseStart_192526 := by decide
  rcases family_descends (prefixWord ++ tailWord_192526) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_192528 : List Nat := [2, 1, 1, 1, 1, 1, 1, 11]
def baseStart_192528 : Nat := 118140960795 + 192528 * 2 ^ 59
def prefixEnd_192528 : Nat := 4983230072969 + 3 ^ 40 * 192528 * 2
def baseEnd_192528 : Nat := 58583350191957313786421

theorem tailTrace_192528 : CollatzResearch.WordTrace tailWord_192528 prefixEnd_192528 58583350191957313786421 := by
  unfold tailWord_192528
  simp only [CollatzResearch.WordTrace]
  refine ⟨3511036523255706004853119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4681382031007608006470825 3511036523255706004853119)
  ·
    refine ⟨5266554784883559007279679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3511036523255706004853119 5266554784883559007279679)
    ·
      refine ⟨7899832177325338510919519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5266554784883559007279679 7899832177325338510919519)
      ·
        refine ⟨11849748265988007766379279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7899832177325338510919519 11849748265988007766379279)
        ·
          refine ⟨17774622398982011649568919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11849748265988007766379279 17774622398982011649568919)
          ·
            refine ⟨26661933598473017474353379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17774622398982011649568919 26661933598473017474353379)
            ·
              refine ⟨39992900397709526211530069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26661933598473017474353379 39992900397709526211530069)
              ·
                refine ⟨58583350191957313786421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 39992900397709526211530069 58583350191957313786421)
                ·
                  rfl

theorem cell19_192528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 11].length) (baseStart_192528 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_192528 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_192528 prefixEnd_192528 := by exact prefixLift 192528
  have htrace : WordTrace (prefixWord ++ tailWord_192528) baseStart_192528 baseEnd_192528 := by
    simpa [prefixWord, tailWord_192528, baseEnd_192528] using wordTrace_append hprefix tailTrace_192528
  have hstable : (prefixWord ++ tailWord_192528).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_192528).length < 2 ^ (prefixWord ++ tailWord_192528).sum := by decide
  have hdescent : baseEnd_192528 < baseStart_192528 := by decide
  rcases family_descends (prefixWord ++ tailWord_192528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_192585 : List Nat := [1, 2, 1, 1, 2, 2, 3, 7]
def baseStart_192585 : Nat := 118140960795 + 192585 * 2 ^ 59
def prefixEnd_192585 : Nat := 4983230072969 + 3 ^ 40 * 192585 * 2
def baseEnd_192585 : Nat := 58600694427398070519599

theorem tailTrace_192585 : CollatzResearch.WordTrace tailWord_192585 prefixEnd_192585 58600694427398070519599 := by
  unfold tailWord_192585
  simp only [CollatzResearch.WordTrace]
  refine ⟨7024152007304910744531209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4682768004869940496354139 7024152007304910744531209)
  ·
    refine ⟨5268114005478683058398407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7024152007304910744531209 5268114005478683058398407)
    ·
      refine ⟨7902171008218024587597611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5268114005478683058398407 7902171008218024587597611)
      ·
        refine ⟨11853256512327036881396417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7902171008218024587597611 11853256512327036881396417)
        ·
          refine ⟨8889942384245277661047313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11853256512327036881396417 8889942384245277661047313)
          ·
            refine ⟨6667456788183958245785485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8889942384245277661047313 6667456788183958245785485)
            ·
              refine ⟨2500296295568984342169557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6667456788183958245785485 2500296295568984342169557)
              ·
                refine ⟨58600694427398070519599, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2500296295568984342169557 58600694427398070519599)
                ·
                  rfl

theorem cell19_192585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 3, 7].length) (baseStart_192585 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_192585 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_192585 prefixEnd_192585 := by exact prefixLift 192585
  have htrace : WordTrace (prefixWord ++ tailWord_192585) baseStart_192585 baseEnd_192585 := by
    simpa [prefixWord, tailWord_192585, baseEnd_192585] using wordTrace_append hprefix tailTrace_192585
  have hstable : (prefixWord ++ tailWord_192585).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_192585).length < 2 ^ (prefixWord ++ tailWord_192585).sum := by decide
  have hdescent : baseEnd_192585 < baseStart_192585 := by decide
  rcases family_descends (prefixWord ++ tailWord_192585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_192661 : List Nat := [1, 3, 2, 1, 1, 1, 10]
def baseStart_192661 : Nat := 118140960795 + 192661 * 2 ^ 59
def prefixEnd_192661 : Nat := 4983230072969 + 3 ^ 40 * 192661 * 2
def baseEnd_192661 : Nat := 19541273358217470943501

theorem tailTrace_192661 : CollatzResearch.WordTrace tailWord_192661 prefixEnd_192661 19541273358217470943501 := by
  unfold tailWord_192661
  simp only [CollatzResearch.WordTrace]
  refine ⟨7026923955029575724297837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4684615970019717149531891 7026923955029575724297837)
  ·
    refine ⟨2635096483136090896611689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7026923955029575724297837 2635096483136090896611689)
    ·
      refine ⟨1976322362352068172458767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2635096483136090896611689 1976322362352068172458767)
      ·
        refine ⟨2964483543528102258688151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1976322362352068172458767 2964483543528102258688151)
        ·
          refine ⟨4446725315292153388032227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2964483543528102258688151 4446725315292153388032227)
          ·
            refine ⟨6670087972938230082048341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4446725315292153388032227 6670087972938230082048341)
            ·
              refine ⟨19541273358217470943501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 6670087972938230082048341 19541273358217470943501)
              ·
                rfl

theorem cell19_192661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 10].length) (baseStart_192661 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_192661 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_192661 prefixEnd_192661 := by exact prefixLift 192661
  have htrace : WordTrace (prefixWord ++ tailWord_192661) baseStart_192661 baseEnd_192661 := by
    simpa [prefixWord, tailWord_192661, baseEnd_192661] using wordTrace_append hprefix tailTrace_192661
  have hstable : (prefixWord ++ tailWord_192661).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_192661).length < 2 ^ (prefixWord ++ tailWord_192661).sum := by decide
  have hdescent : baseEnd_192661 < baseStart_192661 := by decide
  rcases family_descends (prefixWord ++ tailWord_192661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_192695 : List Nat := [1, 1, 3, 1, 4, 4, 2, 3]
def baseStart_192695 : Nat := 118140960795 + 192695 * 2 ^ 59
def prefixEnd_192695 : Nat := 4983230072969 + 3 ^ 40 * 192695 * 2
def baseEnd_192695 : Nat := 58634165758950408074855

theorem tailTrace_192695 : CollatzResearch.WordTrace tailWord_192695 prefixEnd_192695 58634165758950408074855 := by
  unfold tailWord_192695
  simp only [CollatzResearch.WordTrace]
  refine ⟨7028164036906399531035539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4685442691270933020690359 7028164036906399531035539)
  ·
    refine ⟨10542246055359599296553309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7028164036906399531035539 10542246055359599296553309)
    ·
      refine ⟨3953342270759849736207491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10542246055359599296553309 3953342270759849736207491)
      ·
        refine ⟨5930013406139774604311237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3953342270759849736207491 5930013406139774604311237)
        ·
          refine ⟨1111877513651207738308357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5930013406139774604311237 1111877513651207738308357)
          ·
            refine ⟨208477033809601450932817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1111877513651207738308357 208477033809601450932817)
            ·
              refine ⟨156357775357201088199613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 208477033809601450932817 156357775357201088199613)
              ·
                refine ⟨58634165758950408074855, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 156357775357201088199613 58634165758950408074855)
                ·
                  rfl

theorem cell19_192695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 4, 2, 3].length) (baseStart_192695 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_192695 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_192695 prefixEnd_192695 := by exact prefixLift 192695
  have htrace : WordTrace (prefixWord ++ tailWord_192695) baseStart_192695 baseEnd_192695 := by
    simpa [prefixWord, tailWord_192695, baseEnd_192695] using wordTrace_append hprefix tailTrace_192695
  have hstable : (prefixWord ++ tailWord_192695).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_192695).length < 2 ^ (prefixWord ++ tailWord_192695).sum := by decide
  have hdescent : baseEnd_192695 < baseStart_192695 := by decide
  rcases family_descends (prefixWord ++ tailWord_192695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_192699 : List Nat := [1, 1, 1, 1, 1, 2, 7, 5]
def baseStart_192699 : Nat := 118140960795 + 192699 * 2 ^ 59
def prefixEnd_192699 : Nat := 4983230072969 + 3 ^ 40 * 192699 * 2
def baseEnd_192699 : Nat := 58635382898279583985955

theorem tailTrace_192699 : CollatzResearch.WordTrace tailWord_192699 prefixEnd_192699 58635382898279583985955 := by
  unfold tailWord_192699
  simp only [CollatzResearch.WordTrace]
  refine ⟨7028309928891908214181151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4685539952594605476120767 7028309928891908214181151)
  ·
    refine ⟨10542464893337862321271727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7028309928891908214181151 10542464893337862321271727)
    ·
      refine ⟨15813697340006793481907591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10542464893337862321271727 15813697340006793481907591)
      ·
        refine ⟨23720546010010190222861387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15813697340006793481907591 23720546010010190222861387)
        ·
          refine ⟨35580819015015285334292081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23720546010010190222861387 35580819015015285334292081)
          ·
            refine ⟨26685614261261464000719061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35580819015015285334292081 26685614261261464000719061)
            ·
              refine ⟨625444084248315562516853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 26685614261261464000719061 625444084248315562516853)
              ·
                refine ⟨58635382898279583985955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 625444084248315562516853 58635382898279583985955)
                ·
                  rfl

theorem cell19_192699_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 7, 5].length) (baseStart_192699 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_192699 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_192699 prefixEnd_192699 := by exact prefixLift 192699
  have htrace : WordTrace (prefixWord ++ tailWord_192699) baseStart_192699 baseEnd_192699 := by
    simpa [prefixWord, tailWord_192699, baseEnd_192699] using wordTrace_append hprefix tailTrace_192699
  have hstable : (prefixWord ++ tailWord_192699).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_192699).length < 2 ^ (prefixWord ++ tailWord_192699).sum := by decide
  have hdescent : baseEnd_192699 < baseStart_192699 := by decide
  rcases family_descends (prefixWord ++ tailWord_192699) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_192733 : List Nat := [1, 4, 3, 2, 1, 2, 2, 4]
def baseStart_192733 : Nat := 118140960795 + 192733 * 2 ^ 59
def prefixEnd_192733 : Nat := 4983230072969 + 3 ^ 40 * 192733 * 2
def baseEnd_192733 : Nat := 58645728582577579230307

theorem tailTrace_192733 : CollatzResearch.WordTrace tailWord_192733 prefixEnd_192733 58645728582577579230307 := by
  unfold tailWord_192733
  simp only [CollatzResearch.WordTrace]
  refine ⟨7029550010768732020918853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4686366673845821347279235 7029550010768732020918853)
  ·
    refine ⟨1318040627019137253922285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7029550010768732020918853 1318040627019137253922285)
    ·
      refine ⟨494265235132176470220857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1318040627019137253922285 494265235132176470220857)
      ·
        refine ⟨370698926349132352665643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 494265235132176470220857 370698926349132352665643)
        ·
          refine ⟨556048389523698528998465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 370698926349132352665643 556048389523698528998465)
          ·
            refine ⟨417036292142773896748849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 556048389523698528998465 417036292142773896748849)
            ·
              refine ⟨312777219107080422561637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 417036292142773896748849 312777219107080422561637)
              ·
                refine ⟨58645728582577579230307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 312777219107080422561637 58645728582577579230307)
                ·
                  rfl

theorem cell19_192733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 2, 2, 4].length) (baseStart_192733 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_192733 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_192733 prefixEnd_192733 := by exact prefixLift 192733
  have htrace : WordTrace (prefixWord ++ tailWord_192733) baseStart_192733 baseEnd_192733 := by
    simpa [prefixWord, tailWord_192733, baseEnd_192733] using wordTrace_append hprefix tailTrace_192733
  have hstable : (prefixWord ++ tailWord_192733).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_192733).length < 2 ^ (prefixWord ++ tailWord_192733).sum := by decide
  have hdescent : baseEnd_192733 < baseStart_192733 := by decide
  rcases family_descends (prefixWord ++ tailWord_192733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_192754 : List Nat := [3, 2, 1, 3, 2, 1, 2, 5]
def baseStart_192754 : Nat := 118140960795 + 192754 * 2 ^ 59
def prefixEnd_192754 : Nat := 4983230072969 + 3 ^ 40 * 192754 * 2
def baseEnd_192754 : Nat := 58652118564055752763583

theorem tailTrace_192754 : CollatzResearch.WordTrace tailWord_192754 prefixEnd_192754 58652118564055752763583 := by
  unfold tailWord_192754
  simp only [CollatzResearch.WordTrace]
  refine ⟨1757578985923163151858329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4686877295795101738288877 1757578985923163151858329)
  ·
    refine ⟨1318184239442372363893747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1757578985923163151858329 1318184239442372363893747)
    ·
      refine ⟨1977276359163558545840621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1318184239442372363893747 1977276359163558545840621)
      ·
        refine ⟨741478634686334454690233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1977276359163558545840621 741478634686334454690233)
        ·
          refine ⟨556108976014750841017675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 741478634686334454690233 556108976014750841017675)
          ·
            refine ⟨834163464022126261526513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 556108976014750841017675 834163464022126261526513)
            ·
              refine ⟨625622598016594696144885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 834163464022126261526513 625622598016594696144885)
              ·
                refine ⟨58652118564055752763583, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 625622598016594696144885 58652118564055752763583)
                ·
                  rfl

theorem cell19_192754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 2, 5].length) (baseStart_192754 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_192754 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_192754 prefixEnd_192754 := by exact prefixLift 192754
  have htrace : WordTrace (prefixWord ++ tailWord_192754) baseStart_192754 baseEnd_192754 := by
    simpa [prefixWord, tailWord_192754, baseEnd_192754] using wordTrace_append hprefix tailTrace_192754
  have hstable : (prefixWord ++ tailWord_192754).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_192754).length < 2 ^ (prefixWord ++ tailWord_192754).sum := by decide
  have hdescent : baseEnd_192754 < baseStart_192754 := by decide
  rcases family_descends (prefixWord ++ tailWord_192754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_192830 : List Nat := [4, 2, 1, 2, 1, 3, 6]
def baseStart_192830 : Nat := 118140960795 + 192830 * 2 ^ 59
def prefixEnd_192830 : Nat := 4983230072969 + 3 ^ 40 * 192830 * 2
def baseEnd_192830 : Nat := 19558414737103365024829

theorem tailTrace_192830 : CollatzResearch.WordTrace tailWord_192830 prefixEnd_192830 19558414737103365024829 := by
  unfold tailWord_192830
  simp only [CollatzResearch.WordTrace]
  refine ⟨879135986427164698399993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 4688725260944878391466629 879135986427164698399993)
  ·
    refine ⟨659351989820373523799995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 879135986427164698399993 659351989820373523799995)
    ·
      refine ⟨989027984730560285699993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 659351989820373523799995 989027984730560285699993)
      ·
        refine ⟨741770988547920214274995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 989027984730560285699993 741770988547920214274995)
        ·
          refine ⟨1112656482821880321412493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 741770988547920214274995 1112656482821880321412493)
          ·
            refine ⟨417246181058205120529685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1112656482821880321412493 417246181058205120529685)
            ·
              refine ⟨19558414737103365024829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 417246181058205120529685 19558414737103365024829)
              ·
                rfl

theorem cell19_192830_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 3, 6].length) (baseStart_192830 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_192830 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_192830 prefixEnd_192830 := by exact prefixLift 192830
  have htrace : WordTrace (prefixWord ++ tailWord_192830) baseStart_192830 baseEnd_192830 := by
    simpa [prefixWord, tailWord_192830, baseEnd_192830] using wordTrace_append hprefix tailTrace_192830
  have hstable : (prefixWord ++ tailWord_192830).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_192830).length < 2 ^ (prefixWord ++ tailWord_192830).sum := by decide
  have hdescent : baseEnd_192830 < baseStart_192830 := by decide
  rcases family_descends (prefixWord ++ tailWord_192830) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_192864 : List Nat := [2, 1, 1, 3, 6, 1, 2, 3]
def baseStart_192864 : Nat := 118140960795 + 192864 * 2 ^ 59
def prefixEnd_192864 : Nat := 4983230072969 + 3 ^ 40 * 192864 * 2
def baseEnd_192864 : Nat := 58685589895608090318839

theorem tailTrace_192864 : CollatzResearch.WordTrace tailWord_192864 prefixEnd_192864 58685589895608090318839 := by
  unfold tailWord_192864
  simp only [CollatzResearch.WordTrace]
  refine ⟨3517163986647070696968823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4689551982196094262625097 3517163986647070696968823)
  ·
    refine ⟨5275745979970606045453235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3517163986647070696968823 5275745979970606045453235)
    ·
      refine ⟨7913618969955909068179853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5275745979970606045453235 7913618969955909068179853)
      ·
        refine ⟨2967607113733465900567445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7913618969955909068179853 2967607113733465900567445)
        ·
          refine ⟨139106583456256214089099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 2967607113733465900567445 139106583456256214089099)
          ·
            refine ⟨208659875184384321133649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 139106583456256214089099 208659875184384321133649)
            ·
              refine ⟨156494906388288240850237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 208659875184384321133649 156494906388288240850237)
              ·
                refine ⟨58685589895608090318839, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 156494906388288240850237 58685589895608090318839)
                ·
                  rfl

theorem cell19_192864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 6, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 6, 1, 2, 3].length) (baseStart_192864 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_192864 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_192864 prefixEnd_192864 := by exact prefixLift 192864
  have htrace : WordTrace (prefixWord ++ tailWord_192864) baseStart_192864 baseEnd_192864 := by
    simpa [prefixWord, tailWord_192864, baseEnd_192864] using wordTrace_append hprefix tailTrace_192864
  have hstable : (prefixWord ++ tailWord_192864).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_192864).length < 2 ^ (prefixWord ++ tailWord_192864).sum := by decide
  have hdescent : baseEnd_192864 < baseStart_192864 := by decide
  rcases family_descends (prefixWord ++ tailWord_192864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_192866 : List Nat := [3, 3, 2, 1, 1, 2, 4, 3]
def baseStart_192866 : Nat := 118140960795 + 192866 * 2 ^ 59
def prefixEnd_192866 : Nat := 4983230072969 + 3 ^ 40 * 192866 * 2
def baseEnd_192866 : Nat := 58686198465272678274389

theorem tailTrace_192866 : CollatzResearch.WordTrace tailWord_192866 prefixEnd_192866 58686198465272678274389 := by
  unfold tailWord_192866
  simp only [CollatzResearch.WordTrace]
  refine ⟨1758600229821723933877613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4689600612857930490340301 1758600229821723933877613)
  ·
    refine ⟨659475086183146475204105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1758600229821723933877613 659475086183146475204105)
    ·
      refine ⟨494606314637359856403079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 659475086183146475204105 494606314637359856403079)
      ·
        refine ⟨741909471956039784604619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 494606314637359856403079 741909471956039784604619)
        ·
          refine ⟨1112864207934059676906929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 741909471956039784604619 1112864207934059676906929)
          ·
            refine ⟨834648155950544757680197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1112864207934059676906929 834648155950544757680197)
            ·
              refine ⟨156496529240727142065037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 834648155950544757680197 156496529240727142065037)
              ·
                refine ⟨58686198465272678274389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 156496529240727142065037 58686198465272678274389)
                ·
                  rfl

theorem cell19_192866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 4, 3].length) (baseStart_192866 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_192866 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_192866 prefixEnd_192866 := by exact prefixLift 192866
  have htrace : WordTrace (prefixWord ++ tailWord_192866) baseStart_192866 baseEnd_192866 := by
    simpa [prefixWord, tailWord_192866, baseEnd_192866] using wordTrace_append hprefix tailTrace_192866
  have hstable : (prefixWord ++ tailWord_192866).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_192866).length < 2 ^ (prefixWord ++ tailWord_192866).sum := by decide
  have hdescent : baseEnd_192866 < baseStart_192866 := by decide
  rcases family_descends (prefixWord ++ tailWord_192866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_192908 : List Nat := [2, 2, 1, 2, 1, 4, 1, 6]
def baseStart_192908 : Nat := 118140960795 + 192908 * 2 ^ 59
def prefixEnd_192908 : Nat := 4983230072969 + 3 ^ 40 * 192908 * 2
def baseEnd_192908 : Nat := 58698978428229025340941

theorem tailTrace_192908 : CollatzResearch.WordTrace tailWord_192908 prefixEnd_192908 58698978428229025340941 := by
  unfold tailWord_192908
  simp only [CollatzResearch.WordTrace]
  refine ⟨3517966392567368454269689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4690621856756491272359585 3517966392567368454269689)
  ·
    refine ⟨2638474794425526340702267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3517966392567368454269689 2638474794425526340702267)
    ·
      refine ⟨3957712191638289511053401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2638474794425526340702267 3957712191638289511053401)
      ·
        refine ⟨2968284143728717133290051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3957712191638289511053401 2968284143728717133290051)
        ·
          refine ⟨4452426215593075699935077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2968284143728717133290051 4452426215593075699935077)
          ·
            refine ⟨834829915423701693737827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4452426215593075699935077 834829915423701693737827)
            ·
              refine ⟨1252244873135552540606741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 834829915423701693737827 1252244873135552540606741)
              ·
                refine ⟨58698978428229025340941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1252244873135552540606741 58698978428229025340941)
                ·
                  rfl

theorem cell19_192908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 1, 6].length) (baseStart_192908 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_192908 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_192908 prefixEnd_192908 := by exact prefixLift 192908
  have htrace : WordTrace (prefixWord ++ tailWord_192908) baseStart_192908 baseEnd_192908 := by
    simpa [prefixWord, tailWord_192908, baseEnd_192908] using wordTrace_append hprefix tailTrace_192908
  have hstable : (prefixWord ++ tailWord_192908).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_192908).length < 2 ^ (prefixWord ++ tailWord_192908).sum := by decide
  have hdescent : baseEnd_192908 < baseStart_192908 := by decide
  rcases family_descends (prefixWord ++ tailWord_192908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_192927 : List Nat := [1, 1, 2, 5, 1, 1, 1, 7]
def baseStart_192927 : Nat := 118140960795 + 192927 * 2 ^ 59
def prefixEnd_192927 : Nat := 4983230072969 + 3 ^ 40 * 192927 * 2
def baseEnd_192927 : Nat := 58704759840042610918667

theorem tailTrace_192927 : CollatzResearch.WordTrace tailWord_192927 prefixEnd_192927 58704759840042610918667 := by
  unfold tailWord_192927
  simp only [CollatzResearch.WordTrace]
  refine ⟨7036625772065903153481035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4691083848043935435654023 7036625772065903153481035)
  ·
    refine ⟨10554938658098854730221553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7036625772065903153481035 10554938658098854730221553)
    ·
      refine ⟨7916203993574141047666165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10554938658098854730221553 7916203993574141047666165)
      ·
        refine ⟨742144124397575723218703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 7916203993574141047666165 742144124397575723218703)
        ·
          refine ⟨1113216186596363584828055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 742144124397575723218703 1113216186596363584828055)
          ·
            refine ⟨1669824279894545377242083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1113216186596363584828055 1669824279894545377242083)
            ·
              refine ⟨2504736419841818065863125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1669824279894545377242083 2504736419841818065863125)
              ·
                refine ⟨58704759840042610918667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2504736419841818065863125 58704759840042610918667)
                ·
                  rfl

theorem cell19_192927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 1, 7].length) (baseStart_192927 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_192927 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_192927 prefixEnd_192927 := by exact prefixLift 192927
  have htrace : WordTrace (prefixWord ++ tailWord_192927) baseStart_192927 baseEnd_192927 := by
    simpa [prefixWord, tailWord_192927, baseEnd_192927] using wordTrace_append hprefix tailTrace_192927
  have hstable : (prefixWord ++ tailWord_192927).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_192927).length < 2 ^ (prefixWord ++ tailWord_192927).sum := by decide
  have hdescent : baseEnd_192927 < baseStart_192927 := by decide
  rcases family_descends (prefixWord ++ tailWord_192927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_192978 : List Nat := [3, 2, 2, 4, 1, 1, 3, 3]
def baseStart_192978 : Nat := 118140960795 + 192978 * 2 ^ 59
def prefixEnd_192978 : Nat := 4983230072969 + 3 ^ 40 * 192978 * 2
def baseEnd_192978 : Nat := 58720278366489603785195

theorem tailTrace_192978 : CollatzResearch.WordTrace tailWord_192978 prefixEnd_192978 58720278366489603785195 := by
  unfold tailWord_192978
  simp only [CollatzResearch.WordTrace]
  refine ⟨1759621473720284715896897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4692323929920759242391725 1759621473720284715896897)
  ·
    refine ⟨1319716105290213536922673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1759621473720284715896897 1319716105290213536922673)
    ·
      refine ⟨989787078967660152692005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1319716105290213536922673 989787078967660152692005)
      ·
        refine ⟨185585077306436278629751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 989787078967660152692005 185585077306436278629751)
        ·
          refine ⟨278377615959654417944627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 185585077306436278629751 278377615959654417944627)
          ·
            refine ⟨417566423939481626916941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 278377615959654417944627 417566423939481626916941)
            ·
              refine ⟨156587408977305610093853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 417566423939481626916941 156587408977305610093853)
              ·
                refine ⟨58720278366489603785195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 156587408977305610093853 58720278366489603785195)
                ·
                  rfl

theorem cell19_192978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 1, 1, 3, 3].length) (baseStart_192978 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_192978 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_192978 prefixEnd_192978 := by exact prefixLift 192978
  have htrace : WordTrace (prefixWord ++ tailWord_192978) baseStart_192978 baseEnd_192978 := by
    simpa [prefixWord, tailWord_192978, baseEnd_192978] using wordTrace_append hprefix tailTrace_192978
  have hstable : (prefixWord ++ tailWord_192978).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_192978).length < 2 ^ (prefixWord ++ tailWord_192978).sum := by decide
  have hdescent : baseEnd_192978 < baseStart_192978 := by decide
  rcases family_descends (prefixWord ++ tailWord_192978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_192980 : List Nat := [2, 4, 1, 2, 2, 2, 3, 3]
def baseStart_192980 : Nat := 118140960795 + 192980 * 2 ^ 59
def prefixEnd_192980 : Nat := 4983230072969 + 3 ^ 40 * 192980 * 2
def baseEnd_192980 : Nat := 58720886936154191740745

theorem tailTrace_192980 : CollatzResearch.WordTrace tailWord_192980 prefixEnd_192980 58720886936154191740745 := by
  unfold tailWord_192980
  simp only [CollatzResearch.WordTrace]
  refine ⟨3519279420436946602580197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4692372560582595470106929 3519279420436946602580197)
  ·
    refine ⟨659864891331927487983787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3519279420436946602580197 659864891331927487983787)
    ·
      refine ⟨989797336997891231975681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 659864891331927487983787 989797336997891231975681)
      ·
        refine ⟨742348002748418423981761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 989797336997891231975681 742348002748418423981761)
        ·
          refine ⟨556761002061313817986321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 742348002748418423981761 556761002061313817986321)
          ·
            refine ⟨417570751545985363489741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 556761002061313817986321 417570751545985363489741)
            ·
              refine ⟨156589031829744511308653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 417570751545985363489741 156589031829744511308653)
              ·
                refine ⟨58720886936154191740745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 156589031829744511308653 58720886936154191740745)
                ·
                  rfl

theorem cell19_192980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 2, 3, 3].length) (baseStart_192980 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_192980 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_192980 prefixEnd_192980 := by exact prefixLift 192980
  have htrace : WordTrace (prefixWord ++ tailWord_192980) baseStart_192980 baseEnd_192980 := by
    simpa [prefixWord, tailWord_192980, baseEnd_192980] using wordTrace_append hprefix tailTrace_192980
  have hstable : (prefixWord ++ tailWord_192980).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_192980).length < 2 ^ (prefixWord ++ tailWord_192980).sum := by decide
  have hdescent : baseEnd_192980 < baseStart_192980 := by decide
  rcases family_descends (prefixWord ++ tailWord_192980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_193056 : List Nat := [2, 1, 1, 6, 3, 1, 5]
def baseStart_193056 : Nat := 118140960795 + 193056 * 2 ^ 59
def prefixEnd_193056 : Nat := 4983230072969 + 3 ^ 40 * 193056 * 2
def baseEnd_193056 : Nat := 19581337527802844683883

theorem tailTrace_193056 : CollatzResearch.WordTrace tailWord_193056 prefixEnd_193056 19581337527802844683883 := by
  unfold tailWord_193056
  simp only [CollatzResearch.WordTrace]
  refine ⟨3520665394299279092463511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4694220525732372123284681 3520665394299279092463511)
  ·
    refine ⟨5280998091448918638695267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3520665394299279092463511 5280998091448918638695267)
    ·
      refine ⟨7921497137173377958042901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5280998091448918638695267 7921497137173377958042901)
      ·
        refine ⟨371320178305002091783261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 7921497137173377958042901 371320178305002091783261)
        ·
          refine ⟨139245066864375784418723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 371320178305002091783261 139245066864375784418723)
          ·
            refine ⟨208867600296563676628085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 139245066864375784418723 208867600296563676628085)
            ·
              refine ⟨19581337527802844683883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 208867600296563676628085 19581337527802844683883)
              ·
                rfl

theorem cell19_193056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 3, 1, 5].length) (baseStart_193056 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_193056 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_193056 prefixEnd_193056 := by exact prefixLift 193056
  have htrace : WordTrace (prefixWord ++ tailWord_193056) baseStart_193056 baseEnd_193056 := by
    simpa [prefixWord, tailWord_193056, baseEnd_193056] using wordTrace_append hprefix tailTrace_193056
  have hstable : (prefixWord ++ tailWord_193056).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_193056).length < 2 ^ (prefixWord ++ tailWord_193056).sum := by decide
  have hdescent : baseEnd_193056 < baseStart_193056 := by decide
  rcases family_descends (prefixWord ++ tailWord_193056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_193079 : List Nat := [1, 1, 3, 1, 2, 3, 4, 4]
def baseStart_193079 : Nat := 118140960795 + 193079 * 2 ^ 59
def prefixEnd_193079 : Nat := 4983230072969 + 3 ^ 40 * 193079 * 2
def baseEnd_193079 : Nat := 58751011134551295540475

theorem tailTrace_193079 : CollatzResearch.WordTrace tailWord_193079 prefixEnd_193079 58751011134551295540475 := by
  unfold tailWord_193079
  simp only [CollatzResearch.WordTrace]
  refine ⟨7042169667515233113014291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4694779778343488742009527 7042169667515233113014291)
  ·
    refine ⟨10563254501272849669521437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7042169667515233113014291 10563254501272849669521437)
    ·
      refine ⟨3961220437977318626070539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10563254501272849669521437 3961220437977318626070539)
      ·
        refine ⟨5941830656965977939105809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3961220437977318626070539 5941830656965977939105809)
        ·
          refine ⟨4456372992724483454329357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5941830656965977939105809 4456372992724483454329357)
          ·
            refine ⟨1671139872271681295373509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4456372992724483454329357 1671139872271681295373509)
            ·
              refine ⟨313338726050940242882533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1671139872271681295373509 313338726050940242882533)
              ·
                refine ⟨58751011134551295540475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 313338726050940242882533 58751011134551295540475)
                ·
                  rfl

theorem cell19_193079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 4, 4].length) (baseStart_193079 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_193079 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_193079 prefixEnd_193079 := by exact prefixLift 193079
  have htrace : WordTrace (prefixWord ++ tailWord_193079) baseStart_193079 baseEnd_193079 := by
    simpa [prefixWord, tailWord_193079, baseEnd_193079] using wordTrace_append hprefix tailTrace_193079
  have hstable : (prefixWord ++ tailWord_193079).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_193079).length < 2 ^ (prefixWord ++ tailWord_193079).sum := by decide
  have hdescent : baseEnd_193079 < baseStart_193079 := by decide
  rcases family_descends (prefixWord ++ tailWord_193079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_193094 : List Nat := [6, 1, 1, 1, 2, 1, 2, 5]
def baseStart_193094 : Nat := 118140960795 + 193094 * 2 ^ 59
def prefixEnd_193094 : Nat := 4983230072969 + 3 ^ 40 * 193094 * 2
def baseEnd_193094 : Nat := 58755575407035705207101

theorem tailTrace_193094 : CollatzResearch.WordTrace tailWord_193094 prefixEnd_193094 58755575407035705207101 := by
  unfold tailWord_193094
  simp only [CollatzResearch.WordTrace]
  refine ⟨220084898826902833587823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 4695144508307260449873557 220084898826902833587823)
  ·
    refine ⟨330127348240354250381735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 220084898826902833587823 330127348240354250381735)
    ·
      refine ⟨495191022360531375572603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 330127348240354250381735 495191022360531375572603)
      ·
        refine ⟨742786533540797063358905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 495191022360531375572603 742786533540797063358905)
        ·
          refine ⟨557089900155597797519179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 742786533540797063358905 557089900155597797519179)
          ·
            refine ⟨835634850233396696278769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 557089900155597797519179 835634850233396696278769)
            ·
              refine ⟨626726137675047522209077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 835634850233396696278769 626726137675047522209077)
              ·
                refine ⟨58755575407035705207101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 626726137675047522209077 58755575407035705207101)
                ·
                  rfl

theorem cell19_193094_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 2, 5].length) (baseStart_193094 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_193094 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_193094 prefixEnd_193094 := by exact prefixLift 193094
  have htrace : WordTrace (prefixWord ++ tailWord_193094) baseStart_193094 baseEnd_193094 := by
    simpa [prefixWord, tailWord_193094, baseEnd_193094] using wordTrace_append hprefix tailTrace_193094
  have hstable : (prefixWord ++ tailWord_193094).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_193094).length < 2 ^ (prefixWord ++ tailWord_193094).sum := by decide
  have hdescent : baseEnd_193094 < baseStart_193094 := by decide
  rcases family_descends (prefixWord ++ tailWord_193094) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_193098 : List Nat := [3, 1, 2, 1, 1, 4, 2, 5]
def baseStart_193098 : Nat := 118140960795 + 193098 * 2 ^ 59
def prefixEnd_193098 : Nat := 4983230072969 + 3 ^ 40 * 193098 * 2
def baseEnd_193098 : Nat := 58756792546364881118201

theorem tailTrace_193098 : CollatzResearch.WordTrace tailWord_193098 prefixEnd_193098 58756792546364881118201 := by
  unfold tailWord_193098
  simp only [CollatzResearch.WordTrace]
  refine ⟨1760715663611599839488987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4695241769630932905303965 1760715663611599839488987)
  ·
    refine ⟨2641073495417399759233481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1760715663611599839488987 2641073495417399759233481)
    ·
      refine ⟨1980805121563049819425111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2641073495417399759233481 1980805121563049819425111)
      ·
        refine ⟨2971207682344574729137667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1980805121563049819425111 2971207682344574729137667)
        ·
          refine ⟨4456811523516862093706501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2971207682344574729137667 4456811523516862093706501)
          ·
            refine ⟨835652160659411642569969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4456811523516862093706501 835652160659411642569969)
            ·
              refine ⟨626739120494558731927477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 835652160659411642569969 626739120494558731927477)
              ·
                refine ⟨58756792546364881118201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 626739120494558731927477 58756792546364881118201)
                ·
                  rfl

theorem cell19_193098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 2, 5].length) (baseStart_193098 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_193098 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_193098 prefixEnd_193098 := by exact prefixLift 193098
  have htrace : WordTrace (prefixWord ++ tailWord_193098) baseStart_193098 baseEnd_193098 := by
    simpa [prefixWord, tailWord_193098, baseEnd_193098] using wordTrace_append hprefix tailTrace_193098
  have hstable : (prefixWord ++ tailWord_193098).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_193098).length < 2 ^ (prefixWord ++ tailWord_193098).sum := by decide
  have hdescent : baseEnd_193098 < baseStart_193098 := by decide
  rcases family_descends (prefixWord ++ tailWord_193098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_193117 : List Nat := [1, 4, 4, 10]
def baseStart_193117 : Nat := 118140960795 + 193117 * 2 ^ 59
def prefixEnd_193117 : Nat := 4983230072969 + 3 ^ 40 * 193117 * 2
def baseEnd_193117 : Nat := 725463876026894650567

theorem tailTrace_193117 : CollatzResearch.WordTrace tailWord_193117 prefixEnd_193117 725463876026894650567 := by
  unfold tailWord_193117
  simp only [CollatzResearch.WordTrace]
  refine ⟨7043555641377565602897605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4695703760918377068598403 7043555641377565602897605)
  ·
    refine ⟨1320666682758293550543301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7043555641377565602897605 1320666682758293550543301)
    ·
      refine ⟨247625003017180040726869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1320666682758293550543301 247625003017180040726869)
      ·
        refine ⟨725463876026894650567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 10 247625003017180040726869 725463876026894650567)
        ·
          rfl

theorem cell19_193117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 10].length) (baseStart_193117 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_193117 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_193117 prefixEnd_193117 := by exact prefixLift 193117
  have htrace : WordTrace (prefixWord ++ tailWord_193117) baseStart_193117 baseEnd_193117 := by
    simpa [prefixWord, tailWord_193117, baseEnd_193117] using wordTrace_append hprefix tailTrace_193117
  have hstable : (prefixWord ++ tailWord_193117).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_193117).length < 2 ^ (prefixWord ++ tailWord_193117).sum := by decide
  have hdescent : baseEnd_193117 < baseStart_193117 := by decide
  rcases family_descends (prefixWord ++ tailWord_193117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_193134 : List Nat := [4, 1, 2, 2, 2, 1, 3, 4]
def baseStart_193134 : Nat := 118140960795 + 193134 * 2 ^ 59
def prefixEnd_193134 : Nat := 4983230072969 + 3 ^ 40 * 193134 * 2
def baseEnd_193134 : Nat := 58767746800327464318103

theorem tailTrace_193134 : CollatzResearch.WordTrace tailWord_193134 prefixEnd_193134 58767746800327464318103 := by
  unfold tailWord_193134
  simp only [CollatzResearch.WordTrace]
  refine ⟨880521960289497188283307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 4696117121543985004177637 880521960289497188283307)
  ·
    refine ⟨1320782940434245782424961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 880521960289497188283307 1320782940434245782424961)
    ·
      refine ⟨990587205325684336818721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1320782940434245782424961 990587205325684336818721)
      ·
        refine ⟨742940403994263252614041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 990587205325684336818721 742940403994263252614041)
        ·
          refine ⟨557205302995697439460531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 742940403994263252614041 557205302995697439460531)
          ·
            refine ⟨835807954493546159190797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 557205302995697439460531 835807954493546159190797)
            ·
              refine ⟨313427982935079809696549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 835807954493546159190797 313427982935079809696549)
              ·
                refine ⟨58767746800327464318103, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 313427982935079809696549 58767746800327464318103)
                ·
                  rfl

theorem cell19_193134_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 3, 4].length) (baseStart_193134 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_193134 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_193134 prefixEnd_193134 := by exact prefixLift 193134
  have htrace : WordTrace (prefixWord ++ tailWord_193134) baseStart_193134 baseEnd_193134 := by
    simpa [prefixWord, tailWord_193134, baseEnd_193134] using wordTrace_append hprefix tailTrace_193134
  have hstable : (prefixWord ++ tailWord_193134).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_193134).length < 2 ^ (prefixWord ++ tailWord_193134).sum := by decide
  have hdescent : baseEnd_193134 < baseStart_193134 := by decide
  rcases family_descends (prefixWord ++ tailWord_193134) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_193153 : List Nat := [1, 2, 4, 2, 1, 1, 5, 3]
def baseStart_193153 : Nat := 118140960795 + 193153 * 2 ^ 59
def prefixEnd_193153 : Nat := 4983230072969 + 3 ^ 40 * 193153 * 2
def baseEnd_193153 : Nat := 58773528212141049895829

theorem tailTrace_193153 : CollatzResearch.WordTrace tailWord_193153 prefixEnd_193153 58773528212141049895829 := by
  unfold tailWord_193153
  simp only [CollatzResearch.WordTrace]
  refine ⟨7044868669247143751208113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4696579112831429167472075 7044868669247143751208113)
  ·
    refine ⟨5283651501935357813406085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7044868669247143751208113 5283651501935357813406085)
    ·
      refine ⟨990684656612879590013641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5283651501935357813406085 990684656612879590013641)
      ·
        refine ⟨743013492459659692510231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 990684656612879590013641 743013492459659692510231)
        ·
          refine ⟨1114520238689489538765347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 743013492459659692510231 1114520238689489538765347)
          ·
            refine ⟨1671780358034234308148021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1114520238689489538765347 1671780358034234308148021)
            ·
              refine ⟨156729408565709466388877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1671780358034234308148021 156729408565709466388877)
              ·
                refine ⟨58773528212141049895829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 156729408565709466388877 58773528212141049895829)
                ·
                  rfl

theorem cell19_193153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 5, 3].length) (baseStart_193153 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_193153 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_193153 prefixEnd_193153 := by exact prefixLift 193153
  have htrace : WordTrace (prefixWord ++ tailWord_193153) baseStart_193153 baseEnd_193153 := by
    simpa [prefixWord, tailWord_193153, baseEnd_193153] using wordTrace_append hprefix tailTrace_193153
  have hstable : (prefixWord ++ tailWord_193153).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_193153).length < 2 ^ (prefixWord ++ tailWord_193153).sum := by decide
  have hdescent : baseEnd_193153 < baseStart_193153 := by decide
  rcases family_descends (prefixWord ++ tailWord_193153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_193172 : List Nat := [2, 4, 2, 2, 1, 2, 6]
def baseStart_193172 : Nat := 118140960795 + 193172 * 2 ^ 59
def prefixEnd_193172 : Nat := 4983230072969 + 3 ^ 40 * 193172 * 2
def baseEnd_193172 : Nat := 19593103207984878491185

theorem tailTrace_193172 : CollatzResearch.WordTrace tailWord_193172 prefixEnd_193172 19593103207984878491185 := by
  unfold tailWord_193172
  simp only [CollatzResearch.WordTrace]
  refine ⟨3522780828089154998074885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4697041104118873330766513 3522780828089154998074885)
  ·
    refine ⟨660521405266716562139041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3522780828089154998074885 660521405266716562139041)
    ·
      refine ⟨495391053950037421604281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 660521405266716562139041 495391053950037421604281)
      ·
        refine ⟨371543290462528066203211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 495391053950037421604281 371543290462528066203211)
        ·
          refine ⟨557314935693792099304817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 371543290462528066203211 557314935693792099304817)
          ·
            refine ⟨417986201770344074478613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 557314935693792099304817 417986201770344074478613)
            ·
              refine ⟨19593103207984878491185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 417986201770344074478613 19593103207984878491185)
              ·
                rfl

theorem cell19_193172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 2, 6].length) (baseStart_193172 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_193172 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_193172 prefixEnd_193172 := by exact prefixLift 193172
  have htrace : WordTrace (prefixWord ++ tailWord_193172) baseStart_193172 baseEnd_193172 := by
    simpa [prefixWord, tailWord_193172, baseEnd_193172] using wordTrace_append hprefix tailTrace_193172
  have hstable : (prefixWord ++ tailWord_193172).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_193172).length < 2 ^ (prefixWord ++ tailWord_193172).sum := by decide
  have hdescent : baseEnd_193172 < baseStart_193172 := by decide
  rcases family_descends (prefixWord ++ tailWord_193172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_193212 : List Nat := [2, 2, 2, 3, 1, 1, 3, 5]
def baseStart_193212 : Nat := 118140960795 + 193212 * 2 ^ 59
def prefixEnd_193212 : Nat := 4983230072969 + 3 ^ 40 * 193212 * 2
def baseEnd_193212 : Nat := 58791481017246394584557

theorem tailTrace_193212 : CollatzResearch.WordTrace tailWord_193212 prefixEnd_193212 58791481017246394584557 := by
  unfold tailWord_193212
  simp only [CollatzResearch.WordTrace]
  refine ⟨3523510288016698413802945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4698013717355597885070593 3523510288016698413802945)
  ·
    refine ⟨2642632716012523810352209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3523510288016698413802945 2642632716012523810352209)
    ·
      refine ⟨1981974537009392857764157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2642632716012523810352209 1981974537009392857764157)
      ·
        refine ⟨743240451378522321661559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1981974537009392857764157 743240451378522321661559)
        ·
          refine ⟨1114860677067783482492339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 743240451378522321661559 1114860677067783482492339)
          ·
            refine ⟨1672291015601675223738509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1114860677067783482492339 1672291015601675223738509)
            ·
              refine ⟨627109130850628208901941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1672291015601675223738509 627109130850628208901941)
              ·
                refine ⟨58791481017246394584557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 627109130850628208901941 58791481017246394584557)
                ·
                  rfl

theorem cell19_193212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 3, 5].length) (baseStart_193212 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_193212 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_193212 prefixEnd_193212 := by exact prefixLift 193212
  have htrace : WordTrace (prefixWord ++ tailWord_193212) baseStart_193212 baseEnd_193212 := by
    simpa [prefixWord, tailWord_193212, baseEnd_193212] using wordTrace_append hprefix tailTrace_193212
  have hstable : (prefixWord ++ tailWord_193212).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_193212).length < 2 ^ (prefixWord ++ tailWord_193212).sum := by decide
  have hdescent : baseEnd_193212 < baseStart_193212 := by decide
  rcases family_descends (prefixWord ++ tailWord_193212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_193303 : List Nat := [1, 1, 3, 4, 4, 1, 1, 4]
def baseStart_193303 : Nat := 118140960795 + 193303 * 2 ^ 59
def prefixEnd_193303 : Nat := 4983230072969 + 3 ^ 40 * 193303 * 2
def baseEnd_193303 : Nat := 58819170936985146562087

theorem tailTrace_193303 : CollatzResearch.WordTrace tailWord_193303 prefixEnd_193303 58819170936985146562087 := by
  unfold tailWord_193303
  simp only [CollatzResearch.WordTrace]
  refine ⟨7050339618703719369168563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4700226412469146246112375 7050339618703719369168563)
  ·
    refine ⟨10575509428055579053752845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7050339618703719369168563 10575509428055579053752845)
    ·
      refine ⟨3965816035520842145157317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10575509428055579053752845 3965816035520842145157317)
      ·
        refine ⟨743590506660157902216997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3965816035520842145157317 743590506660157902216997)
        ·
          refine ⟨139423219998779606665687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 743590506660157902216997 139423219998779606665687)
          ·
            refine ⟨209134829998169409998531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 139423219998779606665687 209134829998169409998531)
            ·
              refine ⟨313702244997254114997797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 209134829998169409998531 313702244997254114997797)
              ·
                refine ⟨58819170936985146562087, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 313702244997254114997797 58819170936985146562087)
                ·
                  rfl

theorem cell19_193303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 4, 1, 1, 4].length) (baseStart_193303 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_193303 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_193303 prefixEnd_193303 := by exact prefixLift 193303
  have htrace : WordTrace (prefixWord ++ tailWord_193303) baseStart_193303 baseEnd_193303 := by
    simpa [prefixWord, tailWord_193303, baseEnd_193303] using wordTrace_append hprefix tailTrace_193303
  have hstable : (prefixWord ++ tailWord_193303).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_193303).length < 2 ^ (prefixWord ++ tailWord_193303).sum := by decide
  have hdescent : baseEnd_193303 < baseStart_193303 := by decide
  rcases family_descends (prefixWord ++ tailWord_193303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_193328 : List Nat := [2, 1, 1, 1, 2, 2, 1, 9]
def baseStart_193328 : Nat := 118140960795 + 193328 * 2 ^ 59
def prefixEnd_193328 : Nat := 4983230072969 + 3 ^ 40 * 193328 * 2
def baseEnd_193328 : Nat := 58826778057792496006463

theorem tailTrace_193328 : CollatzResearch.WordTrace tailWord_193328 prefixEnd_193328 58826778057792496006463 := by
  unfold tailWord_193328
  simp only [CollatzResearch.WordTrace]
  refine ⟨3525625721806574319414319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4700834295742099092552425 3525625721806574319414319)
  ·
    refine ⟨5288438582709861479121479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3525625721806574319414319 5288438582709861479121479)
    ·
      refine ⟨7932657874064792218682219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5288438582709861479121479 7932657874064792218682219)
      ·
        refine ⟨11898986811097188328023329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7932657874064792218682219 11898986811097188328023329)
        ·
          refine ⟨8924240108322891246017497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11898986811097188328023329 8924240108322891246017497)
          ·
            refine ⟨6693180081242168434513123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8924240108322891246017497 6693180081242168434513123)
            ·
              refine ⟨10039770121863252651769685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6693180081242168434513123 10039770121863252651769685)
              ·
                refine ⟨58826778057792496006463, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 10039770121863252651769685 58826778057792496006463)
                ·
                  rfl

theorem cell19_193328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 9].length) (baseStart_193328 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_193328 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_193328 prefixEnd_193328 := by exact prefixLift 193328
  have htrace : WordTrace (prefixWord ++ tailWord_193328) baseStart_193328 baseEnd_193328 := by
    simpa [prefixWord, tailWord_193328, baseEnd_193328] using wordTrace_append hprefix tailTrace_193328
  have hstable : (prefixWord ++ tailWord_193328).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_193328).length < 2 ^ (prefixWord ++ tailWord_193328).sum := by decide
  have hdescent : baseEnd_193328 < baseStart_193328 := by decide
  rcases family_descends (prefixWord ++ tailWord_193328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_193347 : List Nat := [1, 1, 1, 3, 1, 4, 8]
def baseStart_193347 : Nat := 118140960795 + 193347 * 2 ^ 59
def prefixEnd_193347 : Nat := 4983230072969 + 3 ^ 40 * 193347 * 2
def baseEnd_193347 : Nat := 19610853156535360528063

theorem tailTrace_193347 : CollatzResearch.WordTrace tailWord_193347 prefixEnd_193347 19610853156535360528063 := by
  unfold tailWord_193347
  simp only [CollatzResearch.WordTrace]
  refine ⟨7051944430544314883770295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4701296287029543255846863 7051944430544314883770295)
  ·
    refine ⟨10577916645816472325655443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7051944430544314883770295 10577916645816472325655443)
    ·
      refine ⟨15866874968724708488483165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10577916645816472325655443 15866874968724708488483165)
      ·
        refine ⟨5950078113271765683181187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15866874968724708488483165 5950078113271765683181187)
        ·
          refine ⟨8925117169907648524771781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5950078113271765683181187 8925117169907648524771781)
          ·
            refine ⟨1673459469357684098394709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8925117169907648524771781 1673459469357684098394709)
            ·
              refine ⟨19610853156535360528063, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1673459469357684098394709 19610853156535360528063)
              ·
                rfl

theorem cell19_193347_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 8].length) (baseStart_193347 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_193347 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_193347 prefixEnd_193347 := by exact prefixLift 193347
  have htrace : WordTrace (prefixWord ++ tailWord_193347) baseStart_193347 baseEnd_193347 := by
    simpa [prefixWord, tailWord_193347, baseEnd_193347] using wordTrace_append hprefix tailTrace_193347
  have hstable : (prefixWord ++ tailWord_193347).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_193347).length < 2 ^ (prefixWord ++ tailWord_193347).sum := by decide
  have hdescent : baseEnd_193347 < baseStart_193347 := by decide
  rcases family_descends (prefixWord ++ tailWord_193347) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_193383 : List Nat := [1, 1, 5, 1, 2, 3, 1, 5]
def baseStart_193383 : Nat := 118140960795 + 193383 * 2 ^ 59
def prefixEnd_193383 : Nat := 4983230072969 + 3 ^ 40 * 193383 * 2
def baseEnd_193383 : Nat := 58843513723568664784091

theorem tailTrace_193383 : CollatzResearch.WordTrace tailWord_193383 prefixEnd_193383 58843513723568664784091 := by
  unfold tailWord_193383
  simp only [CollatzResearch.WordTrace]
  refine ⟨7053257458413893032080803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4702171638942595354720535 7053257458413893032080803)
  ·
    refine ⟨10579886187620839548121205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7053257458413893032080803 10579886187620839548121205)
    ·
      refine ⟨991864330089453707636363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 10579886187620839548121205 991864330089453707636363)
      ·
        refine ⟨1487796495134180561454545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 991864330089453707636363 1487796495134180561454545)
        ·
          refine ⟨1115847371350635421090909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1487796495134180561454545 1115847371350635421090909)
          ·
            refine ⟨418442764256488282909091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1115847371350635421090909 418442764256488282909091)
            ·
              refine ⟨627664146384732424363637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 418442764256488282909091 627664146384732424363637)
              ·
                refine ⟨58843513723568664784091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 627664146384732424363637 58843513723568664784091)
                ·
                  rfl

theorem cell19_193383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 3, 1, 5].length) (baseStart_193383 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_193383 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_193383 prefixEnd_193383 := by exact prefixLift 193383
  have htrace : WordTrace (prefixWord ++ tailWord_193383) baseStart_193383 baseEnd_193383 := by
    simpa [prefixWord, tailWord_193383, baseEnd_193383] using wordTrace_append hprefix tailTrace_193383
  have hstable : (prefixWord ++ tailWord_193383).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_193383).length < 2 ^ (prefixWord ++ tailWord_193383).sum := by decide
  have hdescent : baseEnd_193383 < baseStart_193383 := by decide
  rcases family_descends (prefixWord ++ tailWord_193383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_193590 : List Nat := [5, 1, 2, 1, 1, 3, 2, 4]
def baseStart_193590 : Nat := 118140960795 + 193590 * 2 ^ 59
def prefixEnd_193590 : Nat := 4983230072969 + 3 ^ 40 * 193590 * 2
def baseEnd_193590 : Nat := 58906500683853518183527

theorem tailTrace_193590 : CollatzResearch.WordTrace tailWord_193590 prefixEnd_193590 58906500683853518183527 := by
  unfold tailWord_193590
  simp only [CollatzResearch.WordTrace]
  refine ⟨441300460541497961554139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 4707204912442644923244149 441300460541497961554139)
  ·
    refine ⟨661950690812246942331209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 441300460541497961554139 661950690812246942331209)
    ·
      refine ⟨496463018109185206748407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 661950690812246942331209 496463018109185206748407)
      ·
        refine ⟨744694527163777810122611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 496463018109185206748407 744694527163777810122611)
        ·
          refine ⟨1117041790745666715183917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 744694527163777810122611 1117041790745666715183917)
          ·
            refine ⟨418890671529625018193969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1117041790745666715183917 418890671529625018193969)
            ·
              refine ⟨314168003647218763645477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 418890671529625018193969 314168003647218763645477)
              ·
                refine ⟨58906500683853518183527, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 314168003647218763645477 58906500683853518183527)
                ·
                  rfl

theorem cell19_193590_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 3, 2, 4].length) (baseStart_193590 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_193590 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_193590 prefixEnd_193590 := by exact prefixLift 193590
  have htrace : WordTrace (prefixWord ++ tailWord_193590) baseStart_193590 baseEnd_193590 := by
    simpa [prefixWord, tailWord_193590, baseEnd_193590] using wordTrace_append hprefix tailTrace_193590
  have hstable : (prefixWord ++ tailWord_193590).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_193590).length < 2 ^ (prefixWord ++ tailWord_193590).sum := by decide
  have hdescent : baseEnd_193590 < baseStart_193590 := by decide
  rcases family_descends (prefixWord ++ tailWord_193590) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_193592 : List Nat := [2, 1, 2, 1, 5, 2, 2, 4]
def baseStart_193592 : Nat := 118140960795 + 193592 * 2 ^ 59
def prefixEnd_193592 : Nat := 4983230072969 + 3 ^ 40 * 193592 * 2
def baseEnd_193592 : Nat := 58907109253518106139077

theorem tailTrace_193592 : CollatzResearch.WordTrace tailWord_193592 prefixEnd_193592 58907109253518106139077 := by
  unfold tailWord_193592
  simp only [CollatzResearch.WordTrace]
  refine ⟨3530440157328360863219515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4707253543104481150959353 3530440157328360863219515)
  ·
    refine ⟨5295660235992541294829273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3530440157328360863219515 5295660235992541294829273)
    ·
      refine ⟨3971745176994405971121955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5295660235992541294829273 3971745176994405971121955)
      ·
        refine ⟨5957617765491608956682933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3971745176994405971121955 5957617765491608956682933)
        ·
          refine ⟨558526665514838339689025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 5957617765491608956682933 558526665514838339689025)
          ·
            refine ⟨418894999136128754766769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 558526665514838339689025 418894999136128754766769)
            ·
              refine ⟨314171249352096566075077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 418894999136128754766769 314171249352096566075077)
              ·
                refine ⟨58907109253518106139077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 314171249352096566075077 58907109253518106139077)
                ·
                  rfl

theorem cell19_193592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 2, 2, 4].length) (baseStart_193592 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_193592 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_193592 prefixEnd_193592 := by exact prefixLift 193592
  have htrace : WordTrace (prefixWord ++ tailWord_193592) baseStart_193592 baseEnd_193592 := by
    simpa [prefixWord, tailWord_193592, baseEnd_193592] using wordTrace_append hprefix tailTrace_193592
  have hstable : (prefixWord ++ tailWord_193592).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_193592).length < 2 ^ (prefixWord ++ tailWord_193592).sum := by decide
  have hdescent : baseEnd_193592 < baseStart_193592 := by decide
  rcases family_descends (prefixWord ++ tailWord_193592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_193594 : List Nat := [3, 1, 1, 1, 3, 1, 3, 6]
def baseStart_193594 : Nat := 118140960795 + 193594 * 2 ^ 59
def prefixEnd_193594 : Nat := 4983230072969 + 3 ^ 40 * 193594 * 2
def baseEnd_193594 : Nat := 58907717823182694094627

theorem tailTrace_193594 : CollatzResearch.WordTrace tailWord_193594 prefixEnd_193594 58907717823182694094627 := by
  unfold tailWord_193594
  simp only [CollatzResearch.WordTrace]
  refine ⟨1765238315162369017002959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4707302173766317378674557 1765238315162369017002959)
  ·
    refine ⟨2647857472743553525504439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1765238315162369017002959 2647857472743553525504439)
    ·
      refine ⟨3971786209115330288256659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2647857472743553525504439 3971786209115330288256659)
      ·
        refine ⟨5957679313672995432384989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3971786209115330288256659 5957679313672995432384989)
        ·
          refine ⟨2234129742627373287144371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5957679313672995432384989 2234129742627373287144371)
          ·
            refine ⟨3351194613941059930716557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2234129742627373287144371 3351194613941059930716557)
            ·
              refine ⟨1256697980227897474018709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3351194613941059930716557 1256697980227897474018709)
              ·
                refine ⟨58907717823182694094627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1256697980227897474018709 58907717823182694094627)
                ·
                  rfl

theorem cell19_193594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 3, 6].length) (baseStart_193594 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_193594 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_193594 prefixEnd_193594 := by exact prefixLift 193594
  have htrace : WordTrace (prefixWord ++ tailWord_193594) baseStart_193594 baseEnd_193594 := by
    simpa [prefixWord, tailWord_193594, baseEnd_193594] using wordTrace_append hprefix tailTrace_193594
  have hstable : (prefixWord ++ tailWord_193594).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_193594).length < 2 ^ (prefixWord ++ tailWord_193594).sum := by decide
  have hdescent : baseEnd_193594 < baseStart_193594 := by decide
  rcases family_descends (prefixWord ++ tailWord_193594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_193725 : List Nat := [1, 4, 1, 2, 1, 1, 6, 3]
def baseStart_193725 : Nat := 118140960795 + 193725 * 2 ^ 59
def prefixEnd_193725 : Nat := 4983230072969 + 3 ^ 40 * 193725 * 2
def baseEnd_193725 : Nat := 58947579136213205183159

theorem tailTrace_193725 : CollatzResearch.WordTrace tailWord_193725 prefixEnd_193725 58947579136213205183159 := by
  unfold tailWord_193725
  simp only [CollatzResearch.WordTrace]
  refine ⟨7065731223174885441030629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4710487482116590294020419 7065731223174885441030629)
  ·
    refine ⟨1324824604345291020193243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7065731223174885441030629 1324824604345291020193243)
    ·
      refine ⟨1987236906517936530289865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1324824604345291020193243 1987236906517936530289865)
      ·
        refine ⟨1490427679888452397717399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1987236906517936530289865 1490427679888452397717399)
        ·
          refine ⟨2235641519832678596576099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1490427679888452397717399 2235641519832678596576099)
          ·
            refine ⟨3353462279749017894864149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2235641519832678596576099 3353462279749017894864149)
            ·
              refine ⟨157193544363235213821757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 3353462279749017894864149 157193544363235213821757)
              ·
                refine ⟨58947579136213205183159, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 157193544363235213821757 58947579136213205183159)
                ·
                  rfl

theorem cell19_193725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 6, 3].length) (baseStart_193725 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_193725 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_193725 prefixEnd_193725 := by exact prefixLift 193725
  have htrace : WordTrace (prefixWord ++ tailWord_193725) baseStart_193725 baseEnd_193725 := by
    simpa [prefixWord, tailWord_193725, baseEnd_193725] using wordTrace_append hprefix tailTrace_193725
  have hstable : (prefixWord ++ tailWord_193725).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_193725).length < 2 ^ (prefixWord ++ tailWord_193725).sum := by decide
  have hdescent : baseEnd_193725 < baseStart_193725 := by decide
  rcases family_descends (prefixWord ++ tailWord_193725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_193742 : List Nat := [4, 1, 1, 1, 6, 1, 5]
def baseStart_193742 : Nat := 118140960795 + 193742 * 2 ^ 59
def prefixEnd_193742 : Nat := 4983230072969 + 3 ^ 40 * 193742 * 2
def baseEnd_193742 : Nat := 19650917326120734268445

theorem tailTrace_193742 : CollatzResearch.WordTrace tailWord_193742 prefixEnd_193742 19650917326120734268445 := by
  unfold tailWord_193742
  simp only [CollatzResearch.WordTrace]
  refine ⟨883293908014162168049935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 4710900842742198229599653 883293908014162168049935)
  ·
    refine ⟨1324940862021243252074903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 883293908014162168049935 1324940862021243252074903)
    ·
      refine ⟨1987411293031864878112355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1324940862021243252074903 1987411293031864878112355)
      ·
        refine ⟨2981116939547797317168533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1987411293031864878112355 2981116939547797317168533)
        ·
          refine ⟨139739856541302999242275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 2981116939547797317168533 139739856541302999242275)
          ·
            refine ⟨209609784811954498863413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 139739856541302999242275 209609784811954498863413)
            ·
              refine ⟨19650917326120734268445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 209609784811954498863413 19650917326120734268445)
              ·
                rfl

theorem cell19_193742_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 6, 1, 5].length) (baseStart_193742 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_193742 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_193742 prefixEnd_193742 := by exact prefixLift 193742
  have htrace : WordTrace (prefixWord ++ tailWord_193742) baseStart_193742 baseEnd_193742 := by
    simpa [prefixWord, tailWord_193742, baseEnd_193742] using wordTrace_append hprefix tailTrace_193742
  have hstable : (prefixWord ++ tailWord_193742).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_193742).length < 2 ^ (prefixWord ++ tailWord_193742).sum := by decide
  have hdescent : baseEnd_193742 < baseStart_193742 := by decide
  rcases family_descends (prefixWord ++ tailWord_193742) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_193896 : List Nat := [2, 1, 4, 2, 3, 1, 1, 5]
def baseStart_193896 : Nat := 118140960795 + 193896 * 2 ^ 59
def prefixEnd_193896 : Nat := 4983230072969 + 3 ^ 40 * 193896 * 2
def baseEnd_193896 : Nat := 58999611842535475382693

theorem tailTrace_193896 : CollatzResearch.WordTrace tailWord_193896 prefixEnd_193896 58999611842535475382693 := by
  unfold tailWord_193896
  simp only [CollatzResearch.WordTrace]
  refine ⟨3535984052777690822752771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4714645403703587763670361 3535984052777690822752771)
  ·
    refine ⟨5303976079166536234129157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3535984052777690822752771 5303976079166536234129157)
    ·
      refine ⟨994495514843725543899217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5303976079166536234129157 994495514843725543899217)
      ·
        refine ⟨745871636132794157924413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 994495514843725543899217 745871636132794157924413)
        ·
          refine ⟨279701863549797809221655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 745871636132794157924413 279701863549797809221655)
          ·
            refine ⟨419552795324696713832483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 279701863549797809221655 419552795324696713832483)
            ·
              refine ⟨629329192987045070748725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 419552795324696713832483 629329192987045070748725)
              ·
                refine ⟨58999611842535475382693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 629329192987045070748725 58999611842535475382693)
                ·
                  rfl

theorem cell19_193896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 3, 1, 1, 5].length) (baseStart_193896 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_193896 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_193896 prefixEnd_193896 := by exact prefixLift 193896
  have htrace : WordTrace (prefixWord ++ tailWord_193896) baseStart_193896 baseEnd_193896 := by
    simpa [prefixWord, tailWord_193896, baseEnd_193896] using wordTrace_append hprefix tailTrace_193896
  have hstable : (prefixWord ++ tailWord_193896).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_193896).length < 2 ^ (prefixWord ++ tailWord_193896).sum := by decide
  have hdescent : baseEnd_193896 < baseStart_193896 := by decide
  rcases family_descends (prefixWord ++ tailWord_193896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_194010 : List Nat := [3, 1, 1, 2, 3, 3, 3, 3]
def baseStart_194010 : Nat := 118140960795 + 194010 * 2 ^ 59
def prefixEnd_194010 : Nat := 4983230072969 + 3 ^ 40 * 194010 * 2
def baseEnd_194010 : Nat := 59034300313416988849049

theorem tailTrace_194010 : CollatzResearch.WordTrace tailWord_194010 prefixEnd_194010 59034300313416988849049 := by
  unfold tailWord_194010
  simp only [CollatzResearch.WordTrace]
  refine ⟨1769031506785594778788871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4717417351428252743436989 1769031506785594778788871)
  ·
    refine ⟨2653547260178392168183307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1769031506785594778788871 2653547260178392168183307)
    ·
      refine ⟨3980320890267588252274961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2653547260178392168183307 3980320890267588252274961)
      ·
        refine ⟨2985240667700691189206221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3980320890267588252274961 2985240667700691189206221)
        ·
          refine ⟨1119465250387759195952333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2985240667700691189206221 1119465250387759195952333)
          ·
            refine ⟨419799468895409698482125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1119465250387759195952333 419799468895409698482125)
            ·
              refine ⟨157424800835778636930797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 419799468895409698482125 157424800835778636930797)
              ·
                refine ⟨59034300313416988849049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 157424800835778636930797 59034300313416988849049)
                ·
                  rfl

theorem cell19_194010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 3, 3, 3].length) (baseStart_194010 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_194010 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_194010 prefixEnd_194010 := by exact prefixLift 194010
  have htrace : WordTrace (prefixWord ++ tailWord_194010) baseStart_194010 baseEnd_194010 := by
    simpa [prefixWord, tailWord_194010, baseEnd_194010] using wordTrace_append hprefix tailTrace_194010
  have hstable : (prefixWord ++ tailWord_194010).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_194010).length < 2 ^ (prefixWord ++ tailWord_194010).sum := by decide
  have hdescent : baseEnd_194010 < baseStart_194010 := by decide
  rcases family_descends (prefixWord ++ tailWord_194010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_194029 : List Nat := [1, 5, 1, 3, 2, 1, 6]
def baseStart_194029 : Nat := 118140960795 + 194029 * 2 ^ 59
def prefixEnd_194029 : Nat := 4983230072969 + 3 ^ 40 * 194029 * 2
def baseEnd_194029 : Nat := 19680027241743524808925

theorem tailTrace_194029 : CollatzResearch.WordTrace tailWord_194029 prefixEnd_194029 19680027241743524808925 := by
  unfold tailWord_194029
  simp only [CollatzResearch.WordTrace]
  refine ⟨7076819014073545360097141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4717879342715696906731427 7076819014073545360097141)
  ·
    refine ⟨663451782569394877509107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 7076819014073545360097141 663451782569394877509107)
    ·
      refine ⟨995177673854092316263661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 663451782569394877509107 995177673854092316263661)
      ·
        refine ⟨373191627695284618598873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 995177673854092316263661 373191627695284618598873)
        ·
          refine ⟨279893720771463463949155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 373191627695284618598873 279893720771463463949155)
          ·
            refine ⟨419840581157195195923733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 279893720771463463949155 419840581157195195923733)
            ·
              refine ⟨19680027241743524808925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 419840581157195195923733 19680027241743524808925)
              ·
                rfl

theorem cell19_194029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 2, 1, 6].length) (baseStart_194029 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_194029 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_194029 prefixEnd_194029 := by exact prefixLift 194029
  have htrace : WordTrace (prefixWord ++ tailWord_194029) baseStart_194029 baseEnd_194029 := by
    simpa [prefixWord, tailWord_194029, baseEnd_194029] using wordTrace_append hprefix tailTrace_194029
  have hstable : (prefixWord ++ tailWord_194029).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_194029).length < 2 ^ (prefixWord ++ tailWord_194029).sum := by decide
  have hdescent : baseEnd_194029 < baseStart_194029 := by decide
  rcases family_descends (prefixWord ++ tailWord_194029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_194061 : List Nat := [1, 7, 1, 1, 2, 2, 2, 3]
def baseStart_194061 : Nat := 118140960795 + 194061 * 2 ^ 59
def prefixEnd_194061 : Nat := 4983230072969 + 3 ^ 40 * 194061 * 2
def baseEnd_194061 : Nat := 59049818839863981715577

theorem tailTrace_194061 : CollatzResearch.WordTrace tailWord_194061 prefixEnd_194061 59049818839863981715577 := by
  unfold tailWord_194061
  simp only [CollatzResearch.WordTrace]
  refine ⟨7077986149957614825262037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4718657433305076550174691 7077986149957614825262037)
  ·
    refine ⟨165890300389631597467079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 7077986149957614825262037 165890300389631597467079)
    ·
      refine ⟨248835450584447396200619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 165890300389631597467079 248835450584447396200619)
      ·
        refine ⟨373253175876671094300929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 248835450584447396200619 373253175876671094300929)
        ·
          refine ⟨279939881907503320725697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 373253175876671094300929 279939881907503320725697)
          ·
            refine ⟨209954911430627490544273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 279939881907503320725697 209954911430627490544273)
            ·
              refine ⟨157466183572970617908205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 209954911430627490544273 157466183572970617908205)
              ·
                refine ⟨59049818839863981715577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 157466183572970617908205 59049818839863981715577)
                ·
                  rfl

theorem cell19_194061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 2, 2, 2, 3].length) (baseStart_194061 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_194061 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_194061 prefixEnd_194061 := by exact prefixLift 194061
  have htrace : WordTrace (prefixWord ++ tailWord_194061) baseStart_194061 baseEnd_194061 := by
    simpa [prefixWord, tailWord_194061, baseEnd_194061] using wordTrace_append hprefix tailTrace_194061
  have hstable : (prefixWord ++ tailWord_194061).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_194061).length < 2 ^ (prefixWord ++ tailWord_194061).sum := by decide
  have hdescent : baseEnd_194061 < baseStart_194061 := by decide
  rcases family_descends (prefixWord ++ tailWord_194061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_194067 : List Nat := [1, 1, 1, 2, 1, 8, 2, 3]
def baseStart_194067 : Nat := 118140960795 + 194067 * 2 ^ 59
def prefixEnd_194067 : Nat := 4983230072969 + 3 ^ 40 * 194067 * 2
def baseEnd_194067 : Nat := 59051644548857745582227

theorem tailTrace_194067 : CollatzResearch.WordTrace tailWord_194067 prefixEnd_194067 59051644548857745582227 := by
  unfold tailWord_194067
  simp only [CollatzResearch.WordTrace]
  refine ⟨7078204987935877849980455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4718803325290585233320303 7078204987935877849980455)
  ·
    refine ⟨10617307481903816774970683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7078204987935877849980455 10617307481903816774970683)
    ·
      refine ⟨15925961222855725162456025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10617307481903816774970683 15925961222855725162456025)
      ·
        refine ⟨11944470917141793871842019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15925961222855725162456025 11944470917141793871842019)
        ·
          refine ⟨17916706375712690807763029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11944470917141793871842019 17916706375712690807763029)
          ·
            refine ⟨209961402840383095403473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 17916706375712690807763029 209961402840383095403473)
            ·
              refine ⟨157471052130287321552605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 209961402840383095403473 157471052130287321552605)
              ·
                refine ⟨59051644548857745582227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 157471052130287321552605 59051644548857745582227)
                ·
                  rfl

theorem cell19_194067_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 8, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 8, 2, 3].length) (baseStart_194067 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_194067 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_194067 prefixEnd_194067 := by exact prefixLift 194067
  have htrace : WordTrace (prefixWord ++ tailWord_194067) baseStart_194067 baseEnd_194067 := by
    simpa [prefixWord, tailWord_194067, baseEnd_194067] using wordTrace_append hprefix tailTrace_194067
  have hstable : (prefixWord ++ tailWord_194067).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_194067).length < 2 ^ (prefixWord ++ tailWord_194067).sum := by decide
  have hdescent : baseEnd_194067 < baseStart_194067 := by decide
  rcases family_descends (prefixWord ++ tailWord_194067) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_194069 : List Nat := [1, 3, 2, 1, 3, 3, 1, 5]
def baseStart_194069 : Nat := 118140960795 + 194069 * 2 ^ 59
def prefixEnd_194069 : Nat := 4983230072969 + 3 ^ 40 * 194069 * 2
def baseEnd_194069 : Nat := 59052253118522333537777

theorem tailTrace_194069 : CollatzResearch.WordTrace tailWord_194069 prefixEnd_194069 59052253118522333537777 := by
  unfold tailWord_194069
  simp only [CollatzResearch.WordTrace]
  refine ⟨7078277933928632191553261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4718851955952421461035507 7078277933928632191553261)
  ·
    refine ⟨2654354225223237071832473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7078277933928632191553261 2654354225223237071832473)
    ·
      refine ⟨1990765668917427803874355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2654354225223237071832473 1990765668917427803874355)
      ·
        refine ⟨2986148503376141705811533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1990765668917427803874355 2986148503376141705811533)
        ·
          refine ⟨1119805688766053139679325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2986148503376141705811533 1119805688766053139679325)
          ·
            refine ⟨419927133287269927379747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1119805688766053139679325 419927133287269927379747)
            ·
              refine ⟨629890699930904891069621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 419927133287269927379747 629890699930904891069621)
              ·
                refine ⟨59052253118522333537777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 629890699930904891069621 59052253118522333537777)
                ·
                  rfl

theorem cell19_194069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 3, 1, 5].length) (baseStart_194069 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_194069 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_194069 prefixEnd_194069 := by exact prefixLift 194069
  have htrace : WordTrace (prefixWord ++ tailWord_194069) baseStart_194069 baseEnd_194069 := by
    simpa [prefixWord, tailWord_194069, baseEnd_194069] using wordTrace_append hprefix tailTrace_194069
  have hstable : (prefixWord ++ tailWord_194069).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_194069).length < 2 ^ (prefixWord ++ tailWord_194069).sum := by decide
  have hdescent : baseEnd_194069 < baseStart_194069 := by decide
  rcases family_descends (prefixWord ++ tailWord_194069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_194128 : List Nat := [2, 1, 1, 1, 1, 3, 3, 7]
def baseStart_194128 : Nat := 118140960795 + 194128 * 2 ^ 59
def prefixEnd_194128 : Nat := 4983230072969 + 3 ^ 40 * 194128 * 2
def baseEnd_194128 : Nat := 59070205923627678226505

theorem tailTrace_194128 : CollatzResearch.WordTrace tailWord_194128 prefixEnd_194128 59070205923627678226505 := by
  unfold tailWord_194128
  simp only [CollatzResearch.WordTrace]
  refine ⟨3540214920357442633975519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4720286560476590178634025 3540214920357442633975519)
  ·
    refine ⟨5310322380536163950963279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3540214920357442633975519 5310322380536163950963279)
    ·
      refine ⟨7965483570804245926444919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5310322380536163950963279 7965483570804245926444919)
      ·
        refine ⟨11948225356206368889667379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7965483570804245926444919 11948225356206368889667379)
        ·
          refine ⟨17922338034309553334501069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11948225356206368889667379 17922338034309553334501069)
          ·
            refine ⟨6720876762866082500437901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17922338034309553334501069 6720876762866082500437901)
            ·
              refine ⟨2520328786074780937664213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6720876762866082500437901 2520328786074780937664213)
              ·
                refine ⟨59070205923627678226505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2520328786074780937664213 59070205923627678226505)
                ·
                  rfl

theorem cell19_194128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 3, 7].length) (baseStart_194128 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_194128 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_194128 prefixEnd_194128 := by exact prefixLift 194128
  have htrace : WordTrace (prefixWord ++ tailWord_194128) baseStart_194128 baseEnd_194128 := by
    simpa [prefixWord, tailWord_194128, baseEnd_194128] using wordTrace_append hprefix tailTrace_194128
  have hstable : (prefixWord ++ tailWord_194128).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_194128).length < 2 ^ (prefixWord ++ tailWord_194128).sum := by decide
  have hdescent : baseEnd_194128 < baseStart_194128 := by decide
  rcases family_descends (prefixWord ++ tailWord_194128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_194141 : List Nat := [1, 4, 4, 2, 2, 6]
def baseStart_194141 : Nat := 118140960795 + 194141 * 2 ^ 59
def prefixEnd_194141 : Nat := 4983230072969 + 3 ^ 40 * 194141 * 2
def baseEnd_194141 : Nat := 6563795736271944437509

theorem tailTrace_194141 : CollatzResearch.WordTrace tailWord_194141 prefixEnd_194141 6563795736271944437509 := by
  unfold tailWord_194141
  simp only [CollatzResearch.WordTrace]
  refine ⟨7080903989667788488174277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4720602659778525658782851 7080903989667788488174277)
  ·
    refine ⟨1327669498062710341532677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7080903989667788488174277 1327669498062710341532677)
    ·
      refine ⟨248938030886758189037377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1327669498062710341532677 248938030886758189037377)
      ·
        refine ⟨186703523165068641778033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 248938030886758189037377 186703523165068641778033)
        ·
          refine ⟨140027642373801481333525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 186703523165068641778033 140027642373801481333525)
          ·
            refine ⟨6563795736271944437509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 140027642373801481333525 6563795736271944437509)
            ·
              rfl

theorem cell19_194141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 2, 6].length) (baseStart_194141 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_194141 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_194141 prefixEnd_194141 := by exact prefixLift 194141
  have htrace : WordTrace (prefixWord ++ tailWord_194141) baseStart_194141 baseEnd_194141 := by
    simpa [prefixWord, tailWord_194141, baseEnd_194141] using wordTrace_append hprefix tailTrace_194141
  have hstable : (prefixWord ++ tailWord_194141).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_194141).length < 2 ^ (prefixWord ++ tailWord_194141).sum := by decide
  have hdescent : baseEnd_194141 < baseStart_194141 := by decide
  rcases family_descends (prefixWord ++ tailWord_194141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_194147 : List Nat := [1, 1, 1, 5, 1, 10]
def baseStart_194147 : Nat := 118140960795 + 194147 * 2 ^ 59
def prefixEnd_194147 : Nat := 4983230072969 + 3 ^ 40 * 194147 * 2
def baseEnd_194147 : Nat := 6563998592826807089359

theorem tailTrace_194147 : CollatzResearch.WordTrace tailWord_194147 prefixEnd_194147 6563998592826807089359 := by
  unfold tailWord_194147
  simp only [CollatzResearch.WordTrace]
  refine ⟨7081122827646051512892695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4720748551764034341928463 7081122827646051512892695)
  ·
    refine ⟨10621684241469077269339043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7081122827646051512892695 10621684241469077269339043)
    ·
      refine ⟨15932526362203615904008565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10621684241469077269339043 15932526362203615904008565)
      ·
        refine ⟨1493674346456588991000803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 15932526362203615904008565 1493674346456588991000803)
        ·
          refine ⟨2240511519684883486501205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1493674346456588991000803 2240511519684883486501205)
          ·
            refine ⟨6563998592826807089359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 2240511519684883486501205 6563998592826807089359)
            ·
              rfl

theorem cell19_194147_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 10].length) (baseStart_194147 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_194147 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_194147 prefixEnd_194147 := by exact prefixLift 194147
  have htrace : WordTrace (prefixWord ++ tailWord_194147) baseStart_194147 baseEnd_194147 := by
    simpa [prefixWord, tailWord_194147, baseEnd_194147] using wordTrace_append hprefix tailTrace_194147
  have hstable : (prefixWord ++ tailWord_194147).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_194147).length < 2 ^ (prefixWord ++ tailWord_194147).sum := by decide
  have hdescent : baseEnd_194147 < baseStart_194147 := by decide
  rcases family_descends (prefixWord ++ tailWord_194147) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_194162 : List Nat := [3, 2, 1, 2, 3, 3, 1, 4]
def baseStart_194162 : Nat := 118140960795 + 194162 * 2 ^ 59
def prefixEnd_194162 : Nat := 4983230072969 + 3 ^ 40 * 194162 * 2
def baseEnd_194162 : Nat := 59080551607925673470857

theorem tailTrace_194162 : CollatzResearch.WordTrace tailWord_194162 prefixEnd_194162 59080551607925673470857 := by
  unfold tailWord_194162
  simp only [CollatzResearch.WordTrace]
  refine ⟨1770417480647927268672185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4721113281727806049792493 1770417480647927268672185)
  ·
    refine ⟨1327813110485945451504139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1770417480647927268672185 1327813110485945451504139)
    ·
      refine ⟨1991719665728918177256209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1327813110485945451504139 1991719665728918177256209)
      ·
        refine ⟨1493789749296688632942157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1991719665728918177256209 1493789749296688632942157)
        ·
          refine ⟨560171155986258237353309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1493789749296688632942157 560171155986258237353309)
          ·
            refine ⟨210064183494846839007491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 560171155986258237353309 210064183494846839007491)
            ·
              refine ⟨315096275242270258511237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 210064183494846839007491 315096275242270258511237)
              ·
                refine ⟨59080551607925673470857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 315096275242270258511237 59080551607925673470857)
                ·
                  rfl

theorem cell19_194162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 3, 1, 4].length) (baseStart_194162 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_194162 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_194162 prefixEnd_194162 := by exact prefixLift 194162
  have htrace : WordTrace (prefixWord ++ tailWord_194162) baseStart_194162 baseEnd_194162 := by
    simpa [prefixWord, tailWord_194162, baseEnd_194162] using wordTrace_append hprefix tailTrace_194162
  have hstable : (prefixWord ++ tailWord_194162).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_194162).length < 2 ^ (prefixWord ++ tailWord_194162).sum := by decide
  have hdescent : baseEnd_194162 < baseStart_194162 := by decide
  rcases family_descends (prefixWord ++ tailWord_194162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_194185 : List Nat := [1, 2, 1, 1, 4, 1, 2, 7]
def baseStart_194185 : Nat := 118140960795 + 194185 * 2 ^ 59
def prefixEnd_194185 : Nat := 4983230072969 + 3 ^ 40 * 194185 * 2
def baseEnd_194185 : Nat := 59087550159068434959683

theorem tailTrace_194185 : CollatzResearch.WordTrace tailWord_194185 prefixEnd_194185 59087550159068434959683 := by
  unfold tailWord_194185
  simp only [CollatzResearch.WordTrace]
  refine ⟨7082508801508384002776009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4721672534338922668517339 7082508801508384002776009)
  ·
    refine ⟨5311881601131288002082007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7082508801508384002776009 5311881601131288002082007)
    ·
      refine ⟨7967822401696932003123011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5311881601131288002082007 7967822401696932003123011)
      ·
        refine ⟨11951733602545398004684517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7967822401696932003123011 11951733602545398004684517)
        ·
          refine ⟨2240950050477262125878347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11951733602545398004684517 2240950050477262125878347)
          ·
            refine ⟨3361425075715893188817521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2240950050477262125878347 3361425075715893188817521)
            ·
              refine ⟨2521068806786919891613141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3361425075715893188817521 2521068806786919891613141)
              ·
                refine ⟨59087550159068434959683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2521068806786919891613141 59087550159068434959683)
                ·
                  rfl

theorem cell19_194185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 2, 7].length) (baseStart_194185 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_194185 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_194185 prefixEnd_194185 := by exact prefixLift 194185
  have htrace : WordTrace (prefixWord ++ tailWord_194185) baseStart_194185 baseEnd_194185 := by
    simpa [prefixWord, tailWord_194185, baseEnd_194185] using wordTrace_append hprefix tailTrace_194185
  have hstable : (prefixWord ++ tailWord_194185).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_194185).length < 2 ^ (prefixWord ++ tailWord_194185).sum := by decide
  have hdescent : baseEnd_194185 < baseStart_194185 := by decide
  rcases family_descends (prefixWord ++ tailWord_194185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_194221 : List Nat := [1, 5, 2, 1, 1, 1, 2, 6]
def baseStart_194221 : Nat := 118140960795 + 194221 * 2 ^ 59
def prefixEnd_194221 : Nat := 4983230072969 + 3 ^ 40 * 194221 * 2
def baseEnd_194221 : Nat := 59098504413031018159585

theorem tailTrace_194221 : CollatzResearch.WordTrace tailWord_194221 prefixEnd_194221 59098504413031018159585 := by
  unfold tailWord_194221
  simp only [CollatzResearch.WordTrace]
  refine ⟨7083821829377962151086517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4722547886251974767391011 7083821829377962151086517)
  ·
    refine ⟨664108296504183951664361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 7083821829377962151086517 664108296504183951664361)
    ·
      refine ⟨498081222378137963748271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 664108296504183951664361 498081222378137963748271)
      ·
        refine ⟨747121833567206945622407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 498081222378137963748271 747121833567206945622407)
        ·
          refine ⟨1120682750350810418433611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 747121833567206945622407 1120682750350810418433611)
          ·
            refine ⟨1681024125526215627650417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1120682750350810418433611 1681024125526215627650417)
            ·
              refine ⟨1260768094144661720737813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1681024125526215627650417 1260768094144661720737813)
              ·
                refine ⟨59098504413031018159585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1260768094144661720737813 59098504413031018159585)
                ·
                  rfl

theorem cell19_194221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 2, 6].length) (baseStart_194221 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_194221 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_194221 prefixEnd_194221 := by exact prefixLift 194221
  have htrace : WordTrace (prefixWord ++ tailWord_194221) baseStart_194221 baseEnd_194221 := by
    simpa [prefixWord, tailWord_194221, baseEnd_194221] using wordTrace_append hprefix tailTrace_194221
  have hstable : (prefixWord ++ tailWord_194221).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_194221).length < 2 ^ (prefixWord ++ tailWord_194221).sum := by decide
  have hdescent : baseEnd_194221 < baseStart_194221 := by decide
  rcases family_descends (prefixWord ++ tailWord_194221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_194223 : List Nat := [1, 1, 2, 1, 2, 4, 2, 6]
def baseStart_194223 : Nat := 118140960795 + 194223 * 2 ^ 59
def prefixEnd_194223 : Nat := 4983230072969 + 3 ^ 40 * 194223 * 2
def baseEnd_194223 : Nat := 59099112982695606115135

theorem tailTrace_194223 : CollatzResearch.WordTrace tailWord_194223 prefixEnd_194223 59099112982695606115135 := by
  unfold tailWord_194223
  simp only [CollatzResearch.WordTrace]
  refine ⟨7083894775370716492659323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4722596516913810995106215 7083894775370716492659323)
  ·
    refine ⟨10625842163056074738988985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7083894775370716492659323 10625842163056074738988985)
    ·
      refine ⟨7969381622292056054241739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10625842163056074738988985 7969381622292056054241739)
      ·
        refine ⟨11954072433438084081362609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7969381622292056054241739 11954072433438084081362609)
        ·
          refine ⟨8965554325078563061021957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11954072433438084081362609 8965554325078563061021957)
          ·
            refine ⟨1681041435952230573941617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8965554325078563061021957 1681041435952230573941617)
            ·
              refine ⟨1260781076964172930456213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1681041435952230573941617 1260781076964172930456213)
              ·
                refine ⟨59099112982695606115135, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1260781076964172930456213 59099112982695606115135)
                ·
                  rfl

theorem cell19_194223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 2, 6].length) (baseStart_194223 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_194223 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_194223 prefixEnd_194223 := by exact prefixLift 194223
  have htrace : WordTrace (prefixWord ++ tailWord_194223) baseStart_194223 baseEnd_194223 := by
    simpa [prefixWord, tailWord_194223, baseEnd_194223] using wordTrace_append hprefix tailTrace_194223
  have hstable : (prefixWord ++ tailWord_194223).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_194223).length < 2 ^ (prefixWord ++ tailWord_194223).sum := by decide
  have hdescent : baseEnd_194223 < baseStart_194223 := by decide
  rcases family_descends (prefixWord ++ tailWord_194223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_194238 : List Nat := [4, 2, 1, 1, 2, 2, 4, 3]
def baseStart_194238 : Nat := 118140960795 + 194238 * 2 ^ 59
def prefixEnd_194238 : Nat := 4983230072969 + 3 ^ 40 * 194238 * 2
def baseEnd_194238 : Nat := 59103677255180015781761

theorem tailTrace_194238 : CollatzResearch.WordTrace tailWord_194238 prefixEnd_194238 59103677255180015781761 := by
  unfold tailWord_194238
  simp only [CollatzResearch.WordTrace]
  refine ⟨885555233789546756806921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 4722961246877582702970245 885555233789546756806921)
  ·
    refine ⟨664166425342160067605191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 885555233789546756806921 664166425342160067605191)
    ·
      refine ⟨996249638013240101407787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 664166425342160067605191 996249638013240101407787)
      ·
        refine ⟨1494374457019860152111681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 996249638013240101407787 1494374457019860152111681)
        ·
          refine ⟨1120780842764895114083761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1494374457019860152111681 1120780842764895114083761)
          ·
            refine ⟨840585632073671335562821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1120780842764895114083761 840585632073671335562821)
            ·
              refine ⟨157609806013813375418029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 840585632073671335562821 157609806013813375418029)
              ·
                refine ⟨59103677255180015781761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 157609806013813375418029 59103677255180015781761)
                ·
                  rfl

theorem cell19_194238_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 4, 3].length) (baseStart_194238 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_194238 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_194238 prefixEnd_194238 := by exact prefixLift 194238
  have htrace : WordTrace (prefixWord ++ tailWord_194238) baseStart_194238 baseEnd_194238 := by
    simpa [prefixWord, tailWord_194238, baseEnd_194238] using wordTrace_append hprefix tailTrace_194238
  have hstable : (prefixWord ++ tailWord_194238).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_194238).length < 2 ^ (prefixWord ++ tailWord_194238).sum := by decide
  have hdescent : baseEnd_194238 < baseStart_194238 := by decide
  rcases family_descends (prefixWord ++ tailWord_194238) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_194310 : List Nat := [6, 2, 2, 1, 8]
def baseStart_194310 : Nat := 118140960795 + 194310 * 2 ^ 59
def prefixEnd_194310 : Nat := 4983230072969 + 3 ^ 40 * 194310 * 2
def baseEnd_194310 : Nat := 2189836509744636377095

theorem tailTrace_194310 : CollatzResearch.WordTrace tailWord_194310 prefixEnd_194310 2189836509744636377095 := by
  unfold tailWord_194310
  simp only [CollatzResearch.WordTrace]
  refine ⟨221470872689235323471137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 4724711950703686900717589 221470872689235323471137)
  ·
    refine ⟨166103154516926492603353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 221470872689235323471137 166103154516926492603353)
    ·
      refine ⟨124577365887694869452515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 166103154516926492603353 124577365887694869452515)
      ·
        refine ⟨186866048831542304178773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 124577365887694869452515 186866048831542304178773)
        ·
          refine ⟨2189836509744636377095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 186866048831542304178773 2189836509744636377095)
          ·
            rfl

theorem cell19_194310_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 8].length) (baseStart_194310 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_194310 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_194310 prefixEnd_194310 := by exact prefixLift 194310
  have htrace : WordTrace (prefixWord ++ tailWord_194310) baseStart_194310 baseEnd_194310 := by
    simpa [prefixWord, tailWord_194310, baseEnd_194310] using wordTrace_append hprefix tailTrace_194310
  have hstable : (prefixWord ++ tailWord_194310).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_194310).length < 2 ^ (prefixWord ++ tailWord_194310).sum := by decide
  have hdescent : baseEnd_194310 < baseStart_194310 := by decide
  rcases family_descends (prefixWord ++ tailWord_194310) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_194350 : List Nat := [4, 1, 3, 2, 2, 1, 3, 3]
def baseStart_194350 : Nat := 118140960795 + 194350 * 2 ^ 59
def prefixEnd_194350 : Nat := 4983230072969 + 3 ^ 40 * 194350 * 2
def baseEnd_194350 : Nat := 59137757156396941292567

theorem tailTrace_194350 : CollatzResearch.WordTrace tailWord_194350 prefixEnd_194350 59137757156396941292567 := by
  unfold tailWord_194350
  simp only [CollatzResearch.WordTrace]
  refine ⟨886065855738827147816563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 4725684563940411455021669 886065855738827147816563)
  ·
    refine ⟨1329098783608240721724845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 886065855738827147816563 1329098783608240721724845)
    ·
      refine ⟨498412043853090270646817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1329098783608240721724845 498412043853090270646817)
      ·
        refine ⟨373809032889817702985113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 498412043853090270646817 373809032889817702985113)
        ·
          refine ⟨280356774667363277238835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 373809032889817702985113 280356774667363277238835)
          ·
            refine ⟨420535162001044915858253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 280356774667363277238835 420535162001044915858253)
            ·
              refine ⟨157700685750391843446845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 420535162001044915858253 157700685750391843446845)
              ·
                refine ⟨59137757156396941292567, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 157700685750391843446845 59137757156396941292567)
                ·
                  rfl

theorem cell19_194350_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 2, 1, 3, 3].length) (baseStart_194350 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_194350 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_194350 prefixEnd_194350 := by exact prefixLift 194350
  have htrace : WordTrace (prefixWord ++ tailWord_194350) baseStart_194350 baseEnd_194350 := by
    simpa [prefixWord, tailWord_194350, baseEnd_194350] using wordTrace_append hprefix tailTrace_194350
  have hstable : (prefixWord ++ tailWord_194350).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_194350).length < 2 ^ (prefixWord ++ tailWord_194350).sum := by decide
  have hdescent : baseEnd_194350 < baseStart_194350 := by decide
  rcases family_descends (prefixWord ++ tailWord_194350) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_194394 : List Nat := [3, 1, 1, 2, 1, 3, 2, 6]
def baseStart_194394 : Nat := 118140960795 + 194394 * 2 ^ 59
def prefixEnd_194394 : Nat := 4983230072969 + 3 ^ 40 * 194394 * 2
def baseEnd_194394 : Nat := 59151145689017876314669

theorem tailTrace_194394 : CollatzResearch.WordTrace tailWord_194394 prefixEnd_194394 59151145689017876314669 := by
  unfold tailWord_194394
  simp only [CollatzResearch.WordTrace]
  refine ⟨1772532914437803174283559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4726754438500808464756157 1772532914437803174283559)
  ·
    refine ⟨2658799371656704761425339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1772532914437803174283559 2658799371656704761425339)
    ·
      refine ⟨3988199057485057142138009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2658799371656704761425339 3988199057485057142138009)
      ·
        refine ⟨2991149293113792856603507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3988199057485057142138009 2991149293113792856603507)
        ·
          refine ⟨4486723939670689284905261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2991149293113792856603507 4486723939670689284905261)
          ·
            refine ⟨1682521477376508481839473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4486723939670689284905261 1682521477376508481839473)
            ·
              refine ⟨1261891108032381361379605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1682521477376508481839473 1261891108032381361379605)
              ·
                refine ⟨59151145689017876314669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1261891108032381361379605 59151145689017876314669)
                ·
                  rfl

theorem cell19_194394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 2, 6].length) (baseStart_194394 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_194394 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_194394 prefixEnd_194394 := by exact prefixLift 194394
  have htrace : WordTrace (prefixWord ++ tailWord_194394) baseStart_194394 baseEnd_194394 := by
    simpa [prefixWord, tailWord_194394, baseEnd_194394] using wordTrace_append hprefix tailTrace_194394
  have hstable : (prefixWord ++ tailWord_194394).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_194394).length < 2 ^ (prefixWord ++ tailWord_194394).sum := by decide
  have hdescent : baseEnd_194394 < baseStart_194394 := by decide
  rcases family_descends (prefixWord ++ tailWord_194394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_194584 : List Nat := [2, 1, 2, 3, 2, 1, 3, 5]
def baseStart_194584 : Nat := 118140960795 + 194584 * 2 ^ 59
def prefixEnd_194584 : Nat := 4983230072969 + 3 ^ 40 * 194584 * 2
def baseEnd_194584 : Nat := 59208959807153732091929

theorem tailTrace_194584 : CollatzResearch.WordTrace tailWord_194584 prefixEnd_194584 59208959807153732091929 := by
  unfold tailWord_194584
  simp only [CollatzResearch.WordTrace]
  refine ⟨3548530763531437573275403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4731374351375250097700537 3548530763531437573275403)
  ·
    refine ⟨5322796145297156359913105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3548530763531437573275403 5322796145297156359913105)
    ·
      refine ⟨3992097108972867269934829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5322796145297156359913105 3992097108972867269934829)
      ·
        refine ⟨1497036415864825226225561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3992097108972867269934829 1497036415864825226225561)
        ·
          refine ⟨1122777311898618919669171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1497036415864825226225561 1122777311898618919669171)
          ·
            refine ⟨1684165967847928379503757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1122777311898618919669171 1684165967847928379503757)
            ·
              refine ⟨631562237942973142313909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1684165967847928379503757 631562237942973142313909)
              ·
                refine ⟨59208959807153732091929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 631562237942973142313909 59208959807153732091929)
                ·
                  rfl

theorem cell19_194584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 3, 5].length) (baseStart_194584 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_194584 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_194584 prefixEnd_194584 := by exact prefixLift 194584
  have htrace : WordTrace (prefixWord ++ tailWord_194584) baseStart_194584 baseEnd_194584 := by
    simpa [prefixWord, tailWord_194584, baseEnd_194584] using wordTrace_append hprefix tailTrace_194584
  have hstable : (prefixWord ++ tailWord_194584).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_194584).length < 2 ^ (prefixWord ++ tailWord_194584).sum := by decide
  have hdescent : baseEnd_194584 < baseStart_194584 := by decide
  rcases family_descends (prefixWord ++ tailWord_194584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_194599 : List Nat := [1, 1, 7, 1, 2, 2, 5]
def baseStart_194599 : Nat := 118140960795 + 194599 * 2 ^ 59
def prefixEnd_194599 : Nat := 4983230072969 + 3 ^ 40 * 194599 * 2
def baseEnd_194599 : Nat := 19737841359879380586185

theorem tailTrace_194599 : CollatzResearch.WordTrace tailWord_194599 prefixEnd_194599 19737841359879380586185 := by
  unfold tailWord_194599
  simp only [CollatzResearch.WordTrace]
  refine ⟨7097608622008532708346851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4731739081339021805564567 7097608622008532708346851)
  ·
    refine ⟨10646412933012799062520277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7097608622008532708346851 10646412933012799062520277)
    ·
      refine ⟨249525303117487478027819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 10646412933012799062520277 249525303117487478027819)
      ·
        refine ⟨374287954676231217041729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 249525303117487478027819 374287954676231217041729)
        ·
          refine ⟨280715966007173412781297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 374287954676231217041729 280715966007173412781297)
          ·
            refine ⟨210536974505380059585973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 280715966007173412781297 210536974505380059585973)
            ·
              refine ⟨19737841359879380586185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 210536974505380059585973 19737841359879380586185)
              ·
                rfl

theorem cell19_194599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 2, 2, 5].length) (baseStart_194599 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_194599 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_194599 prefixEnd_194599 := by exact prefixLift 194599
  have htrace : WordTrace (prefixWord ++ tailWord_194599) baseStart_194599 baseEnd_194599 := by
    simpa [prefixWord, tailWord_194599, baseEnd_194599] using wordTrace_append hprefix tailTrace_194599
  have hstable : (prefixWord ++ tailWord_194599).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_194599).length < 2 ^ (prefixWord ++ tailWord_194599).sum := by decide
  have hdescent : baseEnd_194599 < baseStart_194599 := by decide
  rcases family_descends (prefixWord ++ tailWord_194599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_194654 : List Nat := [4, 4, 1, 1, 3, 6]
def baseStart_194654 : Nat := 118140960795 + 194654 * 2 ^ 59
def prefixEnd_194654 : Nat := 4983230072969 + 3 ^ 40 * 194654 * 2
def baseEnd_194654 : Nat := 6581139971712701170687

theorem tailTrace_194654 : CollatzResearch.WordTrace tailWord_194654 prefixEnd_194654 6581139971712701170687 := by
  unfold tailWord_194654
  simp only [CollatzResearch.WordTrace]
  refine ⟨887451829601159637699877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 4733076424539518067732677 887451829601159637699877)
  ·
    refine ⟨166397218050217432068727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 887451829601159637699877 166397218050217432068727)
    ·
      refine ⟨249595827075326148103091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 166397218050217432068727 249595827075326148103091)
      ·
        refine ⟨374393740612989222154637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 249595827075326148103091 374393740612989222154637)
        ·
          refine ⟨140397652729870958307989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 374393740612989222154637 140397652729870958307989)
          ·
            refine ⟨6581139971712701170687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 140397652729870958307989 6581139971712701170687)
            ·
              rfl

theorem cell19_194654_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 3, 6].length) (baseStart_194654 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_194654 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_194654 prefixEnd_194654 := by exact prefixLift 194654
  have htrace : WordTrace (prefixWord ++ tailWord_194654) baseStart_194654 baseEnd_194654 := by
    simpa [prefixWord, tailWord_194654, baseEnd_194654] using wordTrace_append hprefix tailTrace_194654
  have hstable : (prefixWord ++ tailWord_194654).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_194654).length < 2 ^ (prefixWord ++ tailWord_194654).sum := by decide
  have hdescent : baseEnd_194654 < baseStart_194654 := by decide
  rcases family_descends (prefixWord ++ tailWord_194654) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_194658 : List Nat := [3, 3, 2, 2, 2, 7]
def baseStart_194658 : Nat := 118140960795 + 194658 * 2 ^ 59
def prefixEnd_194658 : Nat := 4983230072969 + 3 ^ 40 * 194658 * 2
def baseEnd_194658 : Nat := 6581275209415942938587

theorem tailTrace_194658 : CollatzResearch.WordTrace tailWord_194658 prefixEnd_194658 6581275209415942938587 := by
  unfold tailWord_194658
  simp only [CollatzResearch.WordTrace]
  refine ⟨1774940132198696446186157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4733173685863190523163085 1774940132198696446186157)
  ·
    refine ⟨665602549574511167319809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1774940132198696446186157 665602549574511167319809)
    ·
      refine ⟨499201912180883375489857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 665602549574511167319809 499201912180883375489857)
      ·
        refine ⟨374401434135662531617393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 499201912180883375489857 374401434135662531617393)
        ·
          refine ⟨280801075601746898713045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 374401434135662531617393 280801075601746898713045)
          ·
            refine ⟨6581275209415942938587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 280801075601746898713045 6581275209415942938587)
            ·
              rfl

theorem cell19_194658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 2, 7].length) (baseStart_194658 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_194658 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_194658 prefixEnd_194658 := by exact prefixLift 194658
  have htrace : WordTrace (prefixWord ++ tailWord_194658) baseStart_194658 baseEnd_194658 := by
    simpa [prefixWord, tailWord_194658, baseEnd_194658] using wordTrace_append hprefix tailTrace_194658
  have hstable : (prefixWord ++ tailWord_194658).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_194658).length < 2 ^ (prefixWord ++ tailWord_194658).sum := by decide
  have hdescent : baseEnd_194658 < baseStart_194658 := by decide
  rcases family_descends (prefixWord ++ tailWord_194658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_194679 : List Nat := [1, 1, 3, 1, 1, 5, 3, 4]
def baseStart_194679 : Nat := 118140960795 + 194679 * 2 ^ 59
def prefixEnd_194679 : Nat := 4983230072969 + 3 ^ 40 * 194679 * 2
def baseEnd_194679 : Nat := 59237866866221659980559

theorem tailTrace_194679 : CollatzResearch.WordTrace tailWord_194679 prefixEnd_194679 59237866866221659980559 := by
  unfold tailWord_194679
  simp only [CollatzResearch.WordTrace]
  refine ⟨7100526461718706371259091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4733684307812470914172727 7100526461718706371259091)
  ·
    refine ⟨10650789692578059556888637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7100526461718706371259091 10650789692578059556888637)
    ·
      refine ⟨3994046134716772333833239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10650789692578059556888637 3994046134716772333833239)
      ·
        refine ⟨5991069202075158500749859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3994046134716772333833239 5991069202075158500749859)
        ·
          refine ⟨8986603803112737751124789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5991069202075158500749859 8986603803112737751124789)
          ·
            refine ⟨842494106541819164167949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 8986603803112737751124789 842494106541819164167949)
            ·
              refine ⟨315935289953182186562981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 842494106541819164167949 315935289953182186562981)
              ·
                refine ⟨59237866866221659980559, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 315935289953182186562981 59237866866221659980559)
                ·
                  rfl

theorem cell19_194679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 3, 4].length) (baseStart_194679 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_194679 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_194679 prefixEnd_194679 := by exact prefixLift 194679
  have htrace : WordTrace (prefixWord ++ tailWord_194679) baseStart_194679 baseEnd_194679 := by
    simpa [prefixWord, tailWord_194679, baseEnd_194679] using wordTrace_append hprefix tailTrace_194679
  have hstable : (prefixWord ++ tailWord_194679).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_194679).length < 2 ^ (prefixWord ++ tailWord_194679).sum := by decide
  have hdescent : baseEnd_194679 < baseStart_194679 := by decide
  rcases family_descends (prefixWord ++ tailWord_194679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_194717 : List Nat := [1, 4, 2, 1, 1, 4, 6]
def baseStart_194717 : Nat := 118140960795 + 194717 * 2 ^ 59
def prefixEnd_194717 : Nat := 4983230072969 + 3 ^ 40 * 194717 * 2
def baseEnd_194717 : Nat := 19749809896616277045337

theorem tailTrace_194717 : CollatzResearch.WordTrace tailWord_194717 prefixEnd_194717 19749809896616277045337 := by
  unfold tailWord_194717
  simp only [CollatzResearch.WordTrace]
  refine ⟨7101912435581038861142405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4734608290387359240761603 7101912435581038861142405)
  ·
    refine ⟨1331608581671444786464201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7101912435581038861142405 1331608581671444786464201)
    ·
      refine ⟨998706436253583589848151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1331608581671444786464201 998706436253583589848151)
      ·
        refine ⟨1498059654380375384772227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 998706436253583589848151 1498059654380375384772227)
        ·
          refine ⟨2247089481570563077158341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1498059654380375384772227 2247089481570563077158341)
          ·
            refine ⟨421329277794480576967189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2247089481570563077158341 421329277794480576967189)
            ·
              refine ⟨19749809896616277045337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 421329277794480576967189 19749809896616277045337)
              ·
                rfl

theorem cell19_194717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 4, 6].length) (baseStart_194717 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_194717 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_194717 prefixEnd_194717 := by exact prefixLift 194717
  have htrace : WordTrace (prefixWord ++ tailWord_194717) baseStart_194717 baseEnd_194717 := by
    simpa [prefixWord, tailWord_194717, baseEnd_194717] using wordTrace_append hprefix tailTrace_194717
  have hstable : (prefixWord ++ tailWord_194717).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_194717).length < 2 ^ (prefixWord ++ tailWord_194717).sum := by decide
  have hdescent : baseEnd_194717 < baseStart_194717 := by decide
  rcases family_descends (prefixWord ++ tailWord_194717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_194791 : List Nat := [1, 1, 5, 3, 1, 2, 2, 4]
def baseStart_194791 : Nat := 118140960795 + 194791 * 2 ^ 59
def prefixEnd_194791 : Nat := 4983230072969 + 3 ^ 40 * 194791 * 2
def baseEnd_194791 : Nat := 59271946767438585491365

theorem tailTrace_194791 : CollatzResearch.WordTrace tailWord_194791 prefixEnd_194791 59271946767438585491365 := by
  unfold tailWord_194791
  simp only [CollatzResearch.WordTrace]
  refine ⟨7104611437312949499336227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4736407624875299666224151 7104611437312949499336227)
  ·
    refine ⟨10656917155969424249004341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7104611437312949499336227 10656917155969424249004341)
    ·
      refine ⟨999085983372133523344157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 10656917155969424249004341 999085983372133523344157)
      ·
        refine ⟨374657243764550071254059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 999085983372133523344157 374657243764550071254059)
        ·
          refine ⟨561985865646825106881089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 374657243764550071254059 561985865646825106881089)
          ·
            refine ⟨421489399235118830160817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 561985865646825106881089 421489399235118830160817)
            ·
              refine ⟨316117049426339122620613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 421489399235118830160817 316117049426339122620613)
              ·
                refine ⟨59271946767438585491365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 316117049426339122620613 59271946767438585491365)
                ·
                  rfl

theorem cell19_194791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 2, 2, 4].length) (baseStart_194791 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_194791 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_194791 prefixEnd_194791 := by exact prefixLift 194791
  have htrace : WordTrace (prefixWord ++ tailWord_194791) baseStart_194791 baseEnd_194791 := by
    simpa [prefixWord, tailWord_194791, baseEnd_194791] using wordTrace_append hprefix tailTrace_194791
  have hstable : (prefixWord ++ tailWord_194791).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_194791).length < 2 ^ (prefixWord ++ tailWord_194791).sum := by decide
  have hdescent : baseEnd_194791 < baseStart_194791 := by decide
  rcases family_descends (prefixWord ++ tailWord_194791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_194812 : List Nat := [2, 2, 2, 1, 4, 1, 2, 5]
def baseStart_194812 : Nat := 118140960795 + 194812 * 2 ^ 59
def prefixEnd_194812 : Nat := 4983230072969 + 3 ^ 40 * 194812 * 2
def baseEnd_194812 : Nat := 59278336748916759024641

theorem tailTrace_194812 : CollatzResearch.WordTrace tailWord_194812 prefixEnd_194812 59278336748916759024641 := by
  unfold tailWord_194812
  simp only [CollatzResearch.WordTrace]
  refine ⟨3552688685118435042925345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4736918246824580057233793 3552688685118435042925345)
  ·
    refine ⟨2664516513838826282194009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3552688685118435042925345 2664516513838826282194009)
    ·
      refine ⟨1998387385379119711645507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2664516513838826282194009 1998387385379119711645507)
      ·
        refine ⟨2997581078068679567468261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1998387385379119711645507 2997581078068679567468261)
        ·
          refine ⟨562046452137877418900299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2997581078068679567468261 562046452137877418900299)
          ·
            refine ⟨843069678206816128350449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 562046452137877418900299 843069678206816128350449)
            ·
              refine ⟨632302258655112096262837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 843069678206816128350449 632302258655112096262837)
              ·
                refine ⟨59278336748916759024641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 632302258655112096262837 59278336748916759024641)
                ·
                  rfl

theorem cell19_194812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 2, 5].length) (baseStart_194812 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_194812 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_194812 prefixEnd_194812 := by exact prefixLift 194812
  have htrace : WordTrace (prefixWord ++ tailWord_194812) baseStart_194812 baseEnd_194812 := by
    simpa [prefixWord, tailWord_194812, baseEnd_194812] using wordTrace_append hprefix tailTrace_194812
  have hstable : (prefixWord ++ tailWord_194812).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_194812).length < 2 ^ (prefixWord ++ tailWord_194812).sum := by decide
  have hdescent : baseEnd_194812 < baseStart_194812 := by decide
  rcases family_descends (prefixWord ++ tailWord_194812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_194833 : List Nat := [1, 2, 2, 1, 1, 12]
def baseStart_194833 : Nat := 118140960795 + 194833 * 2 ^ 59
def prefixEnd_194833 : Nat := 4983230072969 + 3 ^ 40 * 194833 * 2
def baseEnd_194833 : Nat := 6587191858932770284213

theorem tailTrace_194833 : CollatzResearch.WordTrace tailWord_194833 prefixEnd_194833 6587191858932770284213 := by
  unfold tailWord_194833
  simp only [CollatzResearch.WordTrace]
  refine ⟨7106143303160790672365153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4737428868773860448243435 7106143303160790672365153)
  ·
    refine ⟨5329607477370593004273865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7106143303160790672365153 5329607477370593004273865)
    ·
      refine ⟨3997205608027944753205399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5329607477370593004273865 3997205608027944753205399)
      ·
        refine ⟨5995808412041917129808099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3997205608027944753205399 5995808412041917129808099)
        ·
          refine ⟨8993712618062875694712149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5995808412041917129808099 8993712618062875694712149)
          ·
            refine ⟨6587191858932770284213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 12 8993712618062875694712149 6587191858932770284213)
            ·
              rfl

theorem cell19_194833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 12].length) (baseStart_194833 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_194833 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_194833 prefixEnd_194833 := by exact prefixLift 194833
  have htrace : WordTrace (prefixWord ++ tailWord_194833) baseStart_194833 baseEnd_194833 := by
    simpa [prefixWord, tailWord_194833, baseEnd_194833] using wordTrace_append hprefix tailTrace_194833
  have hstable : (prefixWord ++ tailWord_194833).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_194833).length < 2 ^ (prefixWord ++ tailWord_194833).sum := by decide
  have hdescent : baseEnd_194833 < baseStart_194833 := by decide
  rcases family_descends (prefixWord ++ tailWord_194833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_194846 : List Nat := [4, 3, 2, 1, 1, 1, 3, 4]
def baseStart_194846 : Nat := 118140960795 + 194846 * 2 ^ 59
def prefixEnd_194846 : Nat := 4983230072969 + 3 ^ 40 * 194846 * 2
def baseEnd_194846 : Nat := 59288682433214754268993

theorem tailTrace_194846 : CollatzResearch.WordTrace tailWord_194846 prefixEnd_194846 59288682433214754268993 := by
  unfold tailWord_194846
  simp only [CollatzResearch.WordTrace]
  refine ⟨888327181514211736573549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 4737744968075795928392261 888327181514211736573549)
  ·
    refine ⟨333122693067829401215081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 888327181514211736573549 333122693067829401215081)
    ·
      refine ⟨249842019800872050911311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 333122693067829401215081 249842019800872050911311)
      ·
        refine ⟨374763029701308076366967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 249842019800872050911311 374763029701308076366967)
        ·
          refine ⟨562144544551962114550451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 374763029701308076366967 562144544551962114550451)
          ·
            refine ⟨843216816827943171825677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 562144544551962114550451 843216816827943171825677)
            ·
              refine ⟨316206306310478689434629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 843216816827943171825677 316206306310478689434629)
              ·
                refine ⟨59288682433214754268993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 316206306310478689434629 59288682433214754268993)
                ·
                  rfl

theorem cell19_194846_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 3, 4].length) (baseStart_194846 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_194846 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_194846 prefixEnd_194846 := by exact prefixLift 194846
  have htrace : WordTrace (prefixWord ++ tailWord_194846) baseStart_194846 baseEnd_194846 := by
    simpa [prefixWord, tailWord_194846, baseEnd_194846] using wordTrace_append hprefix tailTrace_194846
  have hstable : (prefixWord ++ tailWord_194846).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_194846).length < 2 ^ (prefixWord ++ tailWord_194846).sum := by decide
  have hdescent : baseEnd_194846 < baseStart_194846 := by decide
  rcases family_descends (prefixWord ++ tailWord_194846) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_194848 : List Nat := [2, 1, 1, 5, 2, 3, 1, 4]
def baseStart_194848 : Nat := 118140960795 + 194848 * 2 ^ 59
def prefixEnd_194848 : Nat := 4983230072969 + 3 ^ 40 * 194848 * 2
def baseEnd_194848 : Nat := 59289291002879342224543

theorem tailTrace_194848 : CollatzResearch.WordTrace tailWord_194848 prefixEnd_194848 59289291002879342224543 := by
  unfold tailWord_194848
  simp only [CollatzResearch.WordTrace]
  refine ⟨3553345199053224117080599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4737793598737632156107465 3553345199053224117080599)
  ·
    refine ⟨5330017798579836175620899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3553345199053224117080599 5330017798579836175620899)
    ·
      refine ⟨7995026697869754263431349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5330017798579836175620899 7995026697869754263431349)
      ·
        refine ⟨749533752925289462196689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 7995026697869754263431349 749533752925289462196689)
        ·
          refine ⟨562150314693967096647517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 749533752925289462196689 562150314693967096647517)
          ·
            refine ⟨210806368010237661242819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 562150314693967096647517 210806368010237661242819)
            ·
              refine ⟨316209552015356491864229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 210806368010237661242819 316209552015356491864229)
              ·
                refine ⟨59289291002879342224543, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 316209552015356491864229 59289291002879342224543)
                ·
                  rfl

theorem cell19_194848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 3, 1, 4].length) (baseStart_194848 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_194848 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_194848 prefixEnd_194848 := by exact prefixLift 194848
  have htrace : WordTrace (prefixWord ++ tailWord_194848) baseStart_194848 baseEnd_194848 := by
    simpa [prefixWord, tailWord_194848, baseEnd_194848] using wordTrace_append hprefix tailTrace_194848
  have hstable : (prefixWord ++ tailWord_194848).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_194848).length < 2 ^ (prefixWord ++ tailWord_194848).sum := by decide
  have hdescent : baseEnd_194848 < baseStart_194848 := by decide
  rcases family_descends (prefixWord ++ tailWord_194848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_194871 : List Nat := [1, 1, 3, 1, 2, 1, 1, 9]
def baseStart_194871 : Nat := 118140960795 + 194871 * 2 ^ 59
def prefixEnd_194871 : Nat := 4983230072969 + 3 ^ 40 * 194871 * 2
def baseEnd_194871 : Nat := 59296289554022103713369

theorem tailTrace_194871 : CollatzResearch.WordTrace tailWord_194871 prefixEnd_194871 59296289554022103713369 := by
  unfold tailWord_194871
  simp only [CollatzResearch.WordTrace]
  refine ⟨7107529277023123162248467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4738352851348748774832311 7107529277023123162248467)
  ·
    refine ⟨10661293915534684743372701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7107529277023123162248467 10661293915534684743372701)
    ·
      refine ⟨3997985218325506778764763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10661293915534684743372701 3997985218325506778764763)
      ·
        refine ⟨5996977827488260168147145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3997985218325506778764763 5996977827488260168147145)
        ·
          refine ⟨4497733370616195126110359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5996977827488260168147145 4497733370616195126110359)
          ·
            refine ⟨6746600055924292689165539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4497733370616195126110359 6746600055924292689165539)
            ·
              refine ⟨10119900083886439033748309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6746600055924292689165539 10119900083886439033748309)
              ·
                refine ⟨59296289554022103713369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 10119900083886439033748309 59296289554022103713369)
                ·
                  rfl

theorem cell19_194871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 9].length) (baseStart_194871 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_194871 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_194871 prefixEnd_194871 := by exact prefixLift 194871
  have htrace : WordTrace (prefixWord ++ tailWord_194871) baseStart_194871 baseEnd_194871 := by
    simpa [prefixWord, tailWord_194871, baseEnd_194871] using wordTrace_append hprefix tailTrace_194871
  have hstable : (prefixWord ++ tailWord_194871).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_194871).length < 2 ^ (prefixWord ++ tailWord_194871).sum := by decide
  have hdescent : baseEnd_194871 < baseStart_194871 := by decide
  rcases family_descends (prefixWord ++ tailWord_194871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_194922 : List Nat := [3, 1, 3, 3, 1, 3, 2, 3]
def baseStart_194922 : Nat := 118140960795 + 194922 * 2 ^ 59
def prefixEnd_194922 : Nat := 4983230072969 + 3 ^ 40 * 194922 * 2
def baseEnd_194922 : Nat := 59311808080469096579897

theorem tailTrace_194922 : CollatzResearch.WordTrace tailWord_194922 prefixEnd_194922 59311808080469096579897 := by
  unfold tailWord_194922
  simp only [CollatzResearch.WordTrace]
  refine ⟨1777347349959589718088755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4739592933225572581570013 1777347349959589718088755)
  ·
    refine ⟨2666021024939384577133133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1777347349959589718088755 2666021024939384577133133)
    ·
      refine ⟨999757884352269216424925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2666021024939384577133133 999757884352269216424925)
      ·
        refine ⟨374909206632100956159347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 999757884352269216424925 374909206632100956159347)
        ·
          refine ⟨562363809948151434239021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 374909206632100956159347 562363809948151434239021)
          ·
            refine ⟨210886428730556787839633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 562363809948151434239021 210886428730556787839633)
            ·
              refine ⟨158164821547917590879725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 210886428730556787839633 158164821547917590879725)
              ·
                refine ⟨59311808080469096579897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 158164821547917590879725 59311808080469096579897)
                ·
                  rfl

theorem cell19_194922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 3, 2, 3].length) (baseStart_194922 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_194922 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_194922 prefixEnd_194922 := by exact prefixLift 194922
  have htrace : WordTrace (prefixWord ++ tailWord_194922) baseStart_194922 baseEnd_194922 := by
    simpa [prefixWord, tailWord_194922, baseEnd_194922] using wordTrace_append hprefix tailTrace_194922
  have hstable : (prefixWord ++ tailWord_194922).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_194922).length < 2 ^ (prefixWord ++ tailWord_194922).sum := by decide
  have hdescent : baseEnd_194922 < baseStart_194922 := by decide
  rcases family_descends (prefixWord ++ tailWord_194922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_194945 : List Nat := [1, 2, 4, 3, 1, 1, 7]
def baseStart_194945 : Nat := 118140960795 + 194945 * 2 ^ 59
def prefixEnd_194945 : Nat := 4983230072969 + 3 ^ 40 * 194945 * 2
def baseEnd_194945 : Nat := 19772935543870619356241

theorem tailTrace_194945 : CollatzResearch.WordTrace tailWord_194945 prefixEnd_194945 19772935543870619356241 := by
  unfold tailWord_194945
  simp only [CollatzResearch.WordTrace]
  refine ⟨7110228278755033800442289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4740152185836689200294859 7110228278755033800442289)
  ·
    refine ⟨5332671209066275350331717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7110228278755033800442289 5332671209066275350331717)
    ·
      refine ⟨999875851699926628187197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5332671209066275350331717 999875851699926628187197)
      ·
        refine ⟨374953444387472485570199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 999875851699926628187197 374953444387472485570199)
        ·
          refine ⟨562430166581208728355299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 374953444387472485570199 562430166581208728355299)
          ·
            refine ⟨843645249871813092532949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 562430166581208728355299 843645249871813092532949)
            ·
              refine ⟨19772935543870619356241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 843645249871813092532949 19772935543870619356241)
              ·
                rfl

theorem cell19_194945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 7].length) (baseStart_194945 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_194945 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_194945 prefixEnd_194945 := by exact prefixLift 194945
  have htrace : WordTrace (prefixWord ++ tailWord_194945) baseStart_194945 baseEnd_194945 := by
    simpa [prefixWord, tailWord_194945, baseEnd_194945] using wordTrace_append hprefix tailTrace_194945
  have hstable : (prefixWord ++ tailWord_194945).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_194945).length < 2 ^ (prefixWord ++ tailWord_194945).sum := by decide
  have hdescent : baseEnd_194945 < baseStart_194945 := by decide
  rcases family_descends (prefixWord ++ tailWord_194945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_194983 : List Nat := [1, 1, 6, 1, 1, 2, 2, 5]
def baseStart_194983 : Nat := 118140960795 + 194983 * 2 ^ 59
def prefixEnd_194983 : Nat := 4983230072969 + 3 ^ 40 * 194983 * 2
def baseEnd_194983 : Nat := 59330369455239029224175

theorem tailTrace_194983 : CollatzResearch.WordTrace tailWord_194983 prefixEnd_194983 59330369455239029224175 := by
  unfold tailWord_194983
  simp only [CollatzResearch.WordTrace]
  refine ⟨7111614252617366290325603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4741076168411577526883735 7111614252617366290325603)
  ·
    refine ⟨10667421378926049435488405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7111614252617366290325603 10667421378926049435488405)
    ·
      refine ⟨500035377137158567288519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 10667421378926049435488405 500035377137158567288519)
      ·
        refine ⟨750053065705737850932779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 500035377137158567288519 750053065705737850932779)
        ·
          refine ⟨1125079598558606776399169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 750053065705737850932779 1125079598558606776399169)
          ·
            refine ⟨843809698918955082299377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1125079598558606776399169 843809698918955082299377)
            ·
              refine ⟨632857274189216311724533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 843809698918955082299377 632857274189216311724533)
              ·
                refine ⟨59330369455239029224175, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 632857274189216311724533 59330369455239029224175)
                ·
                  rfl

theorem cell19_194983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 2, 5].length) (baseStart_194983 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_194983 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_194983 prefixEnd_194983 := by exact prefixLift 194983
  have htrace : WordTrace (prefixWord ++ tailWord_194983) baseStart_194983 baseEnd_194983 := by
    simpa [prefixWord, tailWord_194983, baseEnd_194983] using wordTrace_append hprefix tailTrace_194983
  have hstable : (prefixWord ++ tailWord_194983).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_194983).length < 2 ^ (prefixWord ++ tailWord_194983).sum := by decide
  have hdescent : baseEnd_194983 < baseStart_194983 := by decide
  rcases family_descends (prefixWord ++ tailWord_194983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_195040 : List Nat := [2, 1, 1, 3, 1, 1, 7, 3]
def baseStart_195040 : Nat := 118140960795 + 195040 * 2 ^ 59
def prefixEnd_195040 : Nat := 4983230072969 + 3 ^ 40 * 195040 * 2
def baseEnd_195040 : Nat := 59347713690679785957353

theorem tailTrace_195040 : CollatzResearch.WordTrace tailWord_195040 prefixEnd_195040 59347713690679785957353 := by
  unfold tailWord_195040
  simp only [CollatzResearch.WordTrace]
  refine ⟨3556846606705432512575287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4742462142273910016767049 3556846606705432512575287)
  ·
    refine ⟨5335269910058148768862931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3556846606705432512575287 5335269910058148768862931)
    ·
      refine ⟨8002904865087223153294397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5335269910058148768862931 8002904865087223153294397)
      ·
        refine ⟨3001089324407708682485399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8002904865087223153294397 3001089324407708682485399)
        ·
          refine ⟨4501633986611563023728099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3001089324407708682485399 4501633986611563023728099)
          ·
            refine ⟨6752450979917344535592149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4501633986611563023728099 6752450979917344535592149)
            ·
              refine ⟨158260569841812762552941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 6752450979917344535592149 158260569841812762552941)
              ·
                refine ⟨59347713690679785957353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 158260569841812762552941 59347713690679785957353)
                ·
                  rfl

theorem cell19_195040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 7, 3].length) (baseStart_195040 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_195040 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_195040 prefixEnd_195040 := by exact prefixLift 195040
  have htrace : WordTrace (prefixWord ++ tailWord_195040) baseStart_195040 baseEnd_195040 := by
    simpa [prefixWord, tailWord_195040, baseEnd_195040] using wordTrace_append hprefix tailTrace_195040
  have hstable : (prefixWord ++ tailWord_195040).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_195040).length < 2 ^ (prefixWord ++ tailWord_195040).sum := by decide
  have hdescent : baseEnd_195040 < baseStart_195040 := by decide
  rcases family_descends (prefixWord ++ tailWord_195040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_195080 : List Nat := [2, 1, 3, 2, 1, 1, 1, 8]
def baseStart_195080 : Nat := 118140960795 + 195080 * 2 ^ 59
def prefixEnd_195080 : Nat := 4983230072969 + 3 ^ 40 * 195080 * 2
def baseEnd_195080 : Nat := 59359885083971545068355

theorem tailTrace_195080 : CollatzResearch.WordTrace tailWord_195080 prefixEnd_195080 59359885083971545068355 := by
  unfold tailWord_195080
  simp only [CollatzResearch.WordTrace]
  refine ⟨3557576066632975928303347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4743434755510634571071129 3557576066632975928303347)
  ·
    refine ⟨5336364099949463892455021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3557576066632975928303347 5336364099949463892455021)
    ·
      refine ⟨2001136537481048959670633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5336364099949463892455021 2001136537481048959670633)
      ·
        refine ⟨1500852403110786719752975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2001136537481048959670633 1500852403110786719752975)
        ·
          refine ⟨2251278604666180079629463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1500852403110786719752975 2251278604666180079629463)
          ·
            refine ⟨3376917906999270119444195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2251278604666180079629463 3376917906999270119444195)
            ·
              refine ⟨5065376860498905179166293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3376917906999270119444195 5065376860498905179166293)
              ·
                refine ⟨59359885083971545068355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 5065376860498905179166293 59359885083971545068355)
                ·
                  rfl

theorem cell19_195080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 1, 8].length) (baseStart_195080 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_195080 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_195080 prefixEnd_195080 := by exact prefixLift 195080
  have htrace : WordTrace (prefixWord ++ tailWord_195080) baseStart_195080 baseEnd_195080 := by
    simpa [prefixWord, tailWord_195080, baseEnd_195080] using wordTrace_append hprefix tailTrace_195080
  have hstable : (prefixWord ++ tailWord_195080).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_195080).length < 2 ^ (prefixWord ++ tailWord_195080).sum := by decide
  have hdescent : baseEnd_195080 < baseStart_195080 := by decide
  rcases family_descends (prefixWord ++ tailWord_195080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_195095 : List Nat := [1, 1, 3, 6, 1, 1, 1, 5]
def baseStart_195095 : Nat := 118140960795 + 195095 * 2 ^ 59
def prefixEnd_195095 : Nat := 4983230072969 + 3 ^ 40 * 195095 * 2
def baseEnd_195095 : Nat := 59364449356455954734981

theorem tailTrace_195095 : CollatzResearch.WordTrace tailWord_195095 prefixEnd_195095 59364449356455954734981 := by
  unfold tailWord_195095
  simp only [CollatzResearch.WordTrace]
  refine ⟨7115699228211609418402739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4743799485474406278935159 7115699228211609418402739)
  ·
    refine ⟨10673548842317414127604109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7115699228211609418402739 10673548842317414127604109)
    ·
      refine ⟨4002580815869030297851541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10673548842317414127604109 4002580815869030297851541)
      ·
        refine ⟨187620975743860795211791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 4002580815869030297851541 187620975743860795211791)
        ·
          refine ⟨281431463615791192817687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 187620975743860795211791 281431463615791192817687)
          ·
            refine ⟨422147195423686789226531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 281431463615791192817687 422147195423686789226531)
            ·
              refine ⟨633220793135530183839797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 422147195423686789226531 633220793135530183839797)
              ·
                refine ⟨59364449356455954734981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 633220793135530183839797 59364449356455954734981)
                ·
                  rfl

theorem cell19_195095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 1, 1, 1, 5].length) (baseStart_195095 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_195095 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_195095 prefixEnd_195095 := by exact prefixLift 195095
  have htrace : WordTrace (prefixWord ++ tailWord_195095) baseStart_195095 baseEnd_195095 := by
    simpa [prefixWord, tailWord_195095, baseEnd_195095] using wordTrace_append hprefix tailTrace_195095
  have hstable : (prefixWord ++ tailWord_195095).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_195095).length < 2 ^ (prefixWord ++ tailWord_195095).sum := by decide
  have hdescent : baseEnd_195095 < baseStart_195095 := by decide
  rcases family_descends (prefixWord ++ tailWord_195095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_195173 : List Nat := [1, 3, 1, 3, 5, 6]
def baseStart_195173 : Nat := 118140960795 + 195173 * 2 ^ 59
def prefixEnd_195173 : Nat := 4983230072969 + 3 ^ 40 * 195173 * 2
def baseEnd_195173 : Nat := 6598687063708320555715

theorem tailTrace_195173 : CollatzResearch.WordTrace tailWord_195173 prefixEnd_195173 6598687063708320555715 := by
  unfold tailWord_195173
  simp only [CollatzResearch.WordTrace]
  refine ⟨7118544121929028739742173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4745696081286019159828115 7118544121929028739742173)
  ·
    refine ⟨2669454045723385777403315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7118544121929028739742173 2669454045723385777403315)
    ·
      refine ⟨4004181068585078666104973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2669454045723385777403315 4004181068585078666104973)
      ·
        refine ⟨1501567900719404499789365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4004181068585078666104973 1501567900719404499789365)
        ·
          refine ⟨140771990692444171855253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 1501567900719404499789365 140771990692444171855253)
          ·
            refine ⟨6598687063708320555715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 140771990692444171855253 6598687063708320555715)
            ·
              rfl

theorem cell19_195173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 5, 6].length) (baseStart_195173 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_195173 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_195173 prefixEnd_195173 := by exact prefixLift 195173
  have htrace : WordTrace (prefixWord ++ tailWord_195173) baseStart_195173 baseEnd_195173 := by
    simpa [prefixWord, tailWord_195173, baseEnd_195173] using wordTrace_append hprefix tailTrace_195173
  have hstable : (prefixWord ++ tailWord_195173).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_195173).length < 2 ^ (prefixWord ++ tailWord_195173).sum := by decide
  have hdescent : baseEnd_195173 < baseStart_195173 := by decide
  rcases family_descends (prefixWord ++ tailWord_195173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_195230 : List Nat := [4, 3, 1, 1, 1, 1, 8]
def baseStart_195230 : Nat := 118140960795 + 195230 * 2 ^ 59
def prefixEnd_195230 : Nat := 4983230072969 + 3 ^ 40 * 195230 * 2
def baseEnd_195230 : Nat := 19801842602938547244871

theorem tailTrace_195230 : CollatzResearch.WordTrace tailWord_195230 prefixEnd_195230 19801842602938547244871 := by
  unfold tailWord_195230
  simp only [CollatzResearch.WordTrace]
  refine ⟨890077885340315934320893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 4747082055148351649711429 890077885340315934320893)
  ·
    refine ⟨333779207002618475370335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 890077885340315934320893 333779207002618475370335)
    ·
      refine ⟨500668810503927713055503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 333779207002618475370335 500668810503927713055503)
      ·
        refine ⟨751003215755891569583255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 500668810503927713055503 751003215755891569583255)
        ·
          refine ⟨1126504823633837354374883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 751003215755891569583255 1126504823633837354374883)
          ·
            refine ⟨1689757235450756031562325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1126504823633837354374883 1689757235450756031562325)
            ·
              refine ⟨19801842602938547244871, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1689757235450756031562325 19801842602938547244871)
              ·
                rfl

theorem cell19_195230_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 8].length) (baseStart_195230 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_195230 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_195230 prefixEnd_195230 := by exact prefixLift 195230
  have htrace : WordTrace (prefixWord ++ tailWord_195230) baseStart_195230 baseEnd_195230 := by
    simpa [prefixWord, tailWord_195230, baseEnd_195230] using wordTrace_append hprefix tailTrace_195230
  have hstable : (prefixWord ++ tailWord_195230).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_195230).length < 2 ^ (prefixWord ++ tailWord_195230).sum := by decide
  have hdescent : baseEnd_195230 < baseStart_195230 := by decide
  rcases family_descends (prefixWord ++ tailWord_195230) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_195268 : List Nat := [2, 3, 3, 1, 1, 3, 1, 5]
def baseStart_195268 : Nat := 118140960795 + 195268 * 2 ^ 59
def prefixEnd_195268 : Nat := 4983230072969 + 3 ^ 40 * 195268 * 2
def baseEnd_195268 : Nat := 59417090632442812890065

theorem tailTrace_195268 : CollatzResearch.WordTrace tailWord_195268 prefixEnd_195268 59417090632442812890065 := by
  unfold tailWord_195268
  simp only [CollatzResearch.WordTrace]
  refine ⟨3561004528292429982225229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4748006037723239976300305 3561004528292429982225229)
  ·
    refine ⟨1335376698109661243334461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3561004528292429982225229 1335376698109661243334461)
    ·
      refine ⟨500766261791122966250423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1335376698109661243334461 500766261791122966250423)
      ·
        refine ⟨751149392686684449375635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 500766261791122966250423 751149392686684449375635)
        ·
          refine ⟨1126724089030026674063453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 751149392686684449375635 1126724089030026674063453)
          ·
            refine ⟨422521533386260002773795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1126724089030026674063453 422521533386260002773795)
            ·
              refine ⟨633782300079390004160693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 422521533386260002773795 633782300079390004160693)
              ·
                refine ⟨59417090632442812890065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 633782300079390004160693 59417090632442812890065)
                ·
                  rfl

theorem cell19_195268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 3, 1, 5].length) (baseStart_195268 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_195268 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_195268 prefixEnd_195268 := by exact prefixLift 195268
  have htrace : WordTrace (prefixWord ++ tailWord_195268) baseStart_195268 baseEnd_195268 := by
    simpa [prefixWord, tailWord_195268, baseEnd_195268] using wordTrace_append hprefix tailTrace_195268
  have hstable : (prefixWord ++ tailWord_195268).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_195268).length < 2 ^ (prefixWord ++ tailWord_195268).sum := by decide
  have hdescent : baseEnd_195268 < baseStart_195268 := by decide
  rcases family_descends (prefixWord ++ tailWord_195268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_195285 : List Nat := [1, 3, 2, 5, 1, 2, 5]
def baseStart_195285 : Nat := 118140960795 + 195285 * 2 ^ 59
def prefixEnd_195285 : Nat := 4983230072969 + 3 ^ 40 * 195285 * 2
def baseEnd_195285 : Nat := 19807421158197270170747

theorem tailTrace_195285 : CollatzResearch.WordTrace tailWord_195285 prefixEnd_195285 19807421158197270170747 := by
  unfold tailWord_195285
  simp only [CollatzResearch.WordTrace]
  refine ⟨7122629097523271867819309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4748419398348847911879539 7122629097523271867819309)
  ·
    refine ⟨2670985911571226950432241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7122629097523271867819309 2670985911571226950432241)
    ·
      refine ⟨2003239433678420212824181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2670985911571226950432241 2003239433678420212824181)
      ·
        refine ⟨187803696907351894952267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 2003239433678420212824181 187803696907351894952267)
        ·
          refine ⟨281705545361027842428401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 187803696907351894952267 281705545361027842428401)
          ·
            refine ⟨211279159020770881821301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 281705545361027842428401 211279159020770881821301)
            ·
              refine ⟨19807421158197270170747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 211279159020770881821301 19807421158197270170747)
              ·
                rfl

theorem cell19_195285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 1, 2, 5].length) (baseStart_195285 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_195285 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_195285 prefixEnd_195285 := by exact prefixLift 195285
  have htrace : WordTrace (prefixWord ++ tailWord_195285) baseStart_195285 baseEnd_195285 := by
    simpa [prefixWord, tailWord_195285, baseEnd_195285] using wordTrace_append hprefix tailTrace_195285
  have hstable : (prefixWord ++ tailWord_195285).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_195285).length < 2 ^ (prefixWord ++ tailWord_195285).sum := by decide
  have hdescent : baseEnd_195285 < baseStart_195285 := by decide
  rcases family_descends (prefixWord ++ tailWord_195285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_195441 : List Nat := [1, 2, 2, 2, 1, 5, 1, 5]
def baseStart_195441 : Nat := 118140960795 + 195441 * 2 ^ 59
def prefixEnd_195441 : Nat := 4983230072969 + 3 ^ 40 * 195441 * 2
def baseEnd_195441 : Nat := 59469731908429671045149

theorem tailTrace_195441 : CollatzResearch.WordTrace tailWord_195441 prefixEnd_195441 59469731908429671045149 := by
  unfold tailWord_195441
  simp only [CollatzResearch.WordTrace]
  refine ⟨7128318884958110510498177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4752212589972073673665451 7128318884958110510498177)
  ·
    refine ⟨5346239163718582882873633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7128318884958110510498177 5346239163718582882873633)
    ·
      refine ⟨4009679372788937162155225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5346239163718582882873633 4009679372788937162155225)
      ·
        refine ⟨3007259529591702871616419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4009679372788937162155225 3007259529591702871616419)
        ·
          refine ⟨4510889294387554307424629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3007259529591702871616419 4510889294387554307424629)
          ·
            refine ⟨422895871348833216321059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 4510889294387554307424629 422895871348833216321059)
            ·
              refine ⟨634343807023249824481589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 422895871348833216321059 634343807023249824481589)
              ·
                refine ⟨59469731908429671045149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 634343807023249824481589 59469731908429671045149)
                ·
                  rfl

theorem cell19_195441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 5, 1, 5].length) (baseStart_195441 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_195441 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_195441 prefixEnd_195441 := by exact prefixLift 195441
  have htrace : WordTrace (prefixWord ++ tailWord_195441) baseStart_195441 baseEnd_195441 := by
    simpa [prefixWord, tailWord_195441, baseEnd_195441] using wordTrace_append hprefix tailTrace_195441
  have hstable : (prefixWord ++ tailWord_195441).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_195441).length < 2 ^ (prefixWord ++ tailWord_195441).sum := by decide
  have hdescent : baseEnd_195441 < baseStart_195441 := by decide
  rcases family_descends (prefixWord ++ tailWord_195441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_195454 : List Nat := [4, 2, 3, 1, 3, 1, 5]
def baseStart_195454 : Nat := 118140960795 + 195454 * 2 ^ 59
def prefixEnd_195454 : Nat := 4983230072969 + 3 ^ 40 * 195454 * 2
def baseEnd_195454 : Nat := 19824562537083164252075

theorem tailTrace_195454 : CollatzResearch.WordTrace tailWord_195454 prefixEnd_195454 19824562537083164252075 := by
  unfold tailWord_195454
  simp only [CollatzResearch.WordTrace]
  refine ⟨891099129238876716340177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 4752528689274009153814277 891099129238876716340177)
  ·
    refine ⟨668324346929157537255133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 891099129238876716340177 668324346929157537255133)
    ·
      refine ⟨250621630098434076470675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 668324346929157537255133 250621630098434076470675)
      ·
        refine ⟨375932445147651114706013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 250621630098434076470675 375932445147651114706013)
        ·
          refine ⟨140974666930369168014755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 375932445147651114706013 140974666930369168014755)
          ·
            refine ⟨211462000395553752022133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 140974666930369168014755 211462000395553752022133)
            ·
              refine ⟨19824562537083164252075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 211462000395553752022133 19824562537083164252075)
              ·
                rfl

theorem cell19_195454_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 3, 1, 5].length) (baseStart_195454 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_195454 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_195454 prefixEnd_195454 := by exact prefixLift 195454
  have htrace : WordTrace (prefixWord ++ tailWord_195454) baseStart_195454 baseEnd_195454 := by
    simpa [prefixWord, tailWord_195454, baseEnd_195454] using wordTrace_append hprefix tailTrace_195454
  have hstable : (prefixWord ++ tailWord_195454).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_195454).length < 2 ^ (prefixWord ++ tailWord_195454).sum := by decide
  have hdescent : baseEnd_195454 < baseStart_195454 := by decide
  rcases family_descends (prefixWord ++ tailWord_195454) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_195479 : List Nat := [1, 1, 3, 3, 1, 2, 4, 4]
def baseStart_195479 : Nat := 118140960795 + 195479 * 2 ^ 59
def prefixEnd_195479 : Nat := 4983230072969 + 3 ^ 40 * 195479 * 2
def baseEnd_195479 : Nat := 59481294732056842200601

theorem tailTrace_195479 : CollatzResearch.WordTrace tailWord_195479 prefixEnd_195479 59481294732056842200601 := by
  unfold tailWord_195479
  simp only [CollatzResearch.WordTrace]
  refine ⟨7129704858820443000381491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4753136572546962000254327 7129704858820443000381491)
  ·
    refine ⟨10694557288230664500572237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7129704858820443000381491 10694557288230664500572237)
    ·
      refine ⟨4010458983086499187714589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10694557288230664500572237 4010458983086499187714589)
      ·
        refine ⟨1503922118657437195392971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4010458983086499187714589 1503922118657437195392971)
        ·
          refine ⟨2255883177986155793089457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1503922118657437195392971 2255883177986155793089457)
          ·
            refine ⟨1691912383489616844817093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2255883177986155793089457 1691912383489616844817093)
            ·
              refine ⟨317233571904303158403205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1691912383489616844817093 317233571904303158403205)
              ·
                refine ⟨59481294732056842200601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 317233571904303158403205 59481294732056842200601)
                ·
                  rfl

theorem cell19_195479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 4, 4].length) (baseStart_195479 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_195479 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_195479 prefixEnd_195479 := by exact prefixLift 195479
  have htrace : WordTrace (prefixWord ++ tailWord_195479) baseStart_195479 baseEnd_195479 := by
    simpa [prefixWord, tailWord_195479, baseEnd_195479] using wordTrace_append hprefix tailTrace_195479
  have hstable : (prefixWord ++ tailWord_195479).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_195479).length < 2 ^ (prefixWord ++ tailWord_195479).sum := by decide
  have hdescent : baseEnd_195479 < baseStart_195479 := by decide
  rcases family_descends (prefixWord ++ tailWord_195479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_195517 : List Nat := [1, 4, 1, 2, 4, 7]
def baseStart_195517 : Nat := 118140960795 + 195517 * 2 ^ 59
def prefixEnd_195517 : Nat := 4983230072969 + 3 ^ 40 * 195517 * 2
def baseEnd_195517 : Nat := 6610317506187112595117

theorem tailTrace_195517 : CollatzResearch.WordTrace tailWord_195517 prefixEnd_195517 6610317506187112595117 := by
  unfold tailWord_195517
  simp only [CollatzResearch.WordTrace]
  refine ⟨7131090832682775490264805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4754060555121850326843203 7131090832682775490264805)
  ·
    refine ⟨1337079531128020404424651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7131090832682775490264805 1337079531128020404424651)
    ·
      refine ⟨2005619296692030606636977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1337079531128020404424651 2005619296692030606636977)
      ·
        refine ⟨1504214472519022954977733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2005619296692030606636977 1504214472519022954977733)
        ·
          refine ⟨282040213597316804058325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1504214472519022954977733 282040213597316804058325)
          ·
            refine ⟨6610317506187112595117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 282040213597316804058325 6610317506187112595117)
            ·
              rfl

theorem cell19_195517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 4, 7].length) (baseStart_195517 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_195517 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_195517 prefixEnd_195517 := by exact prefixLift 195517
  have htrace : WordTrace (prefixWord ++ tailWord_195517) baseStart_195517 baseEnd_195517 := by
    simpa [prefixWord, tailWord_195517, baseEnd_195517] using wordTrace_append hprefix tailTrace_195517
  have hstable : (prefixWord ++ tailWord_195517).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_195517).length < 2 ^ (prefixWord ++ tailWord_195517).sum := by decide
  have hdescent : baseEnd_195517 < baseStart_195517 := by decide
  rcases family_descends (prefixWord ++ tailWord_195517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_195526 : List Nat := [6, 1, 3, 1, 1, 2, 1, 4]
def baseStart_195526 : Nat := 118140960795 + 195526 * 2 ^ 59
def prefixEnd_195526 : Nat := 4983230072969 + 3 ^ 40 * 195526 * 2
def baseEnd_195526 : Nat := 59495596119174659156029

theorem tailTrace_195526 : CollatzResearch.WordTrace tailWord_195526 prefixEnd_195526 59495596119174659156029 := by
  unfold tailWord_195526
  simp only [CollatzResearch.WordTrace]
  refine ⟨222856846551567813354451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 4754279393100113351561621 222856846551567813354451)
  ·
    refine ⟨334285269827351720031677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 222856846551567813354451 334285269827351720031677)
    ·
      refine ⟨125356976185256895011879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 334285269827351720031677 125356976185256895011879)
      ·
        refine ⟨188035464277885342517819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 125356976185256895011879 188035464277885342517819)
        ·
          refine ⟨282053196416828013776729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 188035464277885342517819 282053196416828013776729)
          ·
            refine ⟨211539897312621010332547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 282053196416828013776729 211539897312621010332547)
            ·
              refine ⟨317309845968931515498821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 211539897312621010332547 317309845968931515498821)
              ·
                refine ⟨59495596119174659156029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 317309845968931515498821 59495596119174659156029)
                ·
                  rfl

theorem cell19_195526_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 1, 2, 1, 4].length) (baseStart_195526 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_195526 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_195526 prefixEnd_195526 := by exact prefixLift 195526
  have htrace : WordTrace (prefixWord ++ tailWord_195526) baseStart_195526 baseEnd_195526 := by
    simpa [prefixWord, tailWord_195526, baseEnd_195526] using wordTrace_append hprefix tailTrace_195526
  have hstable : (prefixWord ++ tailWord_195526).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_195526).length < 2 ^ (prefixWord ++ tailWord_195526).sum := by decide
  have hdescent : baseEnd_195526 < baseStart_195526 := by decide
  rcases family_descends (prefixWord ++ tailWord_195526) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_195534 : List Nat := [4, 1, 1, 1, 2, 5, 1, 4]
def baseStart_195534 : Nat := 118140960795 + 195534 * 2 ^ 59
def prefixEnd_195534 : Nat := 4983230072969 + 3 ^ 40 * 195534 * 2
def baseEnd_195534 : Nat := 59498030397833010978229

theorem tailTrace_195534 : CollatzResearch.WordTrace tailWord_195534 prefixEnd_195534 59498030397833010978229 := by
  unfold tailWord_195534
  simp only [CollatzResearch.WordTrace]
  refine ⟨891463859202648424204207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 4754473915747458262422437 891463859202648424204207)
  ·
    refine ⟨1337195788803972636306311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 891463859202648424204207 1337195788803972636306311)
    ·
      refine ⟨2005793683205958954459467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1337195788803972636306311 2005793683205958954459467)
      ·
        refine ⟨3008690524808938431689201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2005793683205958954459467 3008690524808938431689201)
        ·
          refine ⟨2256517893606703823766901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3008690524808938431689201 2256517893606703823766901)
          ·
            refine ⟨211548552525628483478147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 2256517893606703823766901 211548552525628483478147)
            ·
              refine ⟨317322828788442725217221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 211548552525628483478147 317322828788442725217221)
              ·
                refine ⟨59498030397833010978229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 317322828788442725217221 59498030397833010978229)
                ·
                  rfl

theorem cell19_195534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 5, 1, 4].length) (baseStart_195534 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_195534 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_195534 prefixEnd_195534 := by exact prefixLift 195534
  have htrace : WordTrace (prefixWord ++ tailWord_195534) baseStart_195534 baseEnd_195534 := by
    simpa [prefixWord, tailWord_195534, baseEnd_195534] using wordTrace_append hprefix tailTrace_195534
  have hstable : (prefixWord ++ tailWord_195534).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_195534).length < 2 ^ (prefixWord ++ tailWord_195534).sum := by decide
  have hdescent : baseEnd_195534 < baseStart_195534 := by decide
  rcases family_descends (prefixWord ++ tailWord_195534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_195602 : List Nat := [3, 2, 5, 1, 2, 1, 2, 3]
def baseStart_195602 : Nat := 118140960795 + 195602 * 2 ^ 59
def prefixEnd_195602 : Nat := 4983230072969 + 3 ^ 40 * 195602 * 2
def baseEnd_195602 : Nat := 59518721766429001466933

theorem tailTrace_195602 : CollatzResearch.WordTrace tailWord_195602 prefixEnd_195602 59518721766429001466933 := by
  unfold tailWord_195602
  simp only [CollatzResearch.WordTrace]
  refine ⟨1783547759343708751777265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4756127358249890004739373 1783547759343708751777265)
  ·
    refine ⟨1337660819507781563832949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1783547759343708751777265 1337660819507781563832949)
    ·
      refine ⟨125405701828854521609339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 1337660819507781563832949 125405701828854521609339)
      ·
        refine ⟨188108552743281782414009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 125405701828854521609339 188108552743281782414009)
        ·
          refine ⟨141081414557461336810507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 188108552743281782414009 141081414557461336810507)
          ·
            refine ⟨211622121836192005215761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 141081414557461336810507 211622121836192005215761)
            ·
              refine ⟨158716591377144003911821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 211622121836192005215761 158716591377144003911821)
              ·
                refine ⟨59518721766429001466933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 158716591377144003911821 59518721766429001466933)
                ·
                  rfl

theorem cell19_195602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 2, 1, 2, 3].length) (baseStart_195602 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_195602 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_195602 prefixEnd_195602 := by exact prefixLift 195602
  have htrace : WordTrace (prefixWord ++ tailWord_195602) baseStart_195602 baseEnd_195602 := by
    simpa [prefixWord, tailWord_195602, baseEnd_195602] using wordTrace_append hprefix tailTrace_195602
  have hstable : (prefixWord ++ tailWord_195602).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_195602).length < 2 ^ (prefixWord ++ tailWord_195602).sum := by decide
  have hdescent : baseEnd_195602 < baseStart_195602 := by decide
  rcases family_descends (prefixWord ++ tailWord_195602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_195688 : List Nat := [2, 1, 4, 4, 8]
def baseStart_195688 : Nat := 118140960795 + 195688 * 2 ^ 59
def prefixEnd_195688 : Nat := 4983230072969 + 3 ^ 40 * 195688 * 2
def baseEnd_195688 : Nat := 2205366306000232724281

theorem tailTrace_195688 : CollatzResearch.WordTrace tailWord_195688 prefixEnd_195688 2205366306000232724281 := by
  unfold tailWord_195688
  simp only [CollatzResearch.WordTrace]
  refine ⟨3568663857531635847369859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4758218476708847796493145 3568663857531635847369859)
  ·
    refine ⟨5352995786297453771054789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3568663857531635847369859 5352995786297453771054789)
    ·
      refine ⟨1003686709930772582072773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5352995786297453771054789 1003686709930772582072773)
      ·
        refine ⟨188191258112019859138645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1003686709930772582072773 188191258112019859138645)
        ·
          refine ⟨2205366306000232724281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 188191258112019859138645 2205366306000232724281)
          ·
            rfl

theorem cell19_195688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 8].length) (baseStart_195688 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_195688 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_195688 prefixEnd_195688 := by exact prefixLift 195688
  have htrace : WordTrace (prefixWord ++ tailWord_195688) baseStart_195688 baseEnd_195688 := by
    simpa [prefixWord, tailWord_195688, baseEnd_195688] using wordTrace_append hprefix tailTrace_195688
  have hstable : (prefixWord ++ tailWord_195688).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_195688).length < 2 ^ (prefixWord ++ tailWord_195688).sum := by decide
  have hdescent : baseEnd_195688 < baseStart_195688 := by decide
  rcases family_descends (prefixWord ++ tailWord_195688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_195701 : List Nat := [1, 3, 4, 3, 2, 1, 1, 4]
def baseStart_195701 : Nat := 118140960795 + 195701 * 2 ^ 59
def prefixEnd_195701 : Nat := 4983230072969 + 3 ^ 40 * 195701 * 2
def baseEnd_195701 : Nat := 59548845964826105266663

theorem tailTrace_195701 : CollatzResearch.WordTrace tailWord_195701 prefixEnd_195701 59548845964826105266663 := by
  unfold tailWord_195701
  simp only [CollatzResearch.WordTrace]
  refine ⟨7137801864016174914962957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4758534576010783276641971 7137801864016174914962957)
  ·
    refine ⟨2676675699006065593111109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7137801864016174914962957 2676675699006065593111109)
    ·
      refine ⟨501876693563637298708333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2676675699006065593111109 501876693563637298708333)
      ·
        refine ⟨188203760086363987015625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 501876693563637298708333 188203760086363987015625)
        ·
          refine ⟨141152820064772990261719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 188203760086363987015625 141152820064772990261719)
          ·
            refine ⟨211729230097159485392579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 141152820064772990261719 211729230097159485392579)
            ·
              refine ⟨317593845145739228088869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 211729230097159485392579 317593845145739228088869)
              ·
                refine ⟨59548845964826105266663, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 317593845145739228088869 59548845964826105266663)
                ·
                  rfl

theorem cell19_195701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 2, 1, 1, 4].length) (baseStart_195701 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_195701 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_195701 prefixEnd_195701 := by exact prefixLift 195701
  have htrace : WordTrace (prefixWord ++ tailWord_195701) baseStart_195701 baseEnd_195701 := by
    simpa [prefixWord, tailWord_195701, baseEnd_195701] using wordTrace_append hprefix tailTrace_195701
  have hstable : (prefixWord ++ tailWord_195701).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_195701).length < 2 ^ (prefixWord ++ tailWord_195701).sum := by decide
  have hdescent : baseEnd_195701 < baseStart_195701 := by decide
  rcases family_descends (prefixWord ++ tailWord_195701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_195705 : List Nat := [1, 2, 1, 3, 5, 2, 1, 4]
def baseStart_195705 : Nat := 118140960795 + 195705 * 2 ^ 59
def prefixEnd_195705 : Nat := 4983230072969 + 3 ^ 40 * 195705 * 2
def baseEnd_195705 : Nat := 59550063104155281177763

theorem tailTrace_195705 : CollatzResearch.WordTrace tailWord_195705 prefixEnd_195705 59550063104155281177763 := by
  unfold tailWord_195705
  simp only [CollatzResearch.WordTrace]
  refine ⟨7137947756001683598108569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4758631837334455732072379 7137947756001683598108569)
  ·
    refine ⟨5353460817001262698581427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7137947756001683598108569 5353460817001262698581427)
    ·
      refine ⟨8030191225501894047872141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5353460817001262698581427 8030191225501894047872141)
      ·
        refine ⟨3011321709563210267952053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8030191225501894047872141 3011321709563210267952053)
        ·
          refine ⟨282311410271550962620505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 3011321709563210267952053 282311410271550962620505)
          ·
            refine ⟨211733557703663221965379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 282311410271550962620505 211733557703663221965379)
            ·
              refine ⟨317600336555494832948069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 211733557703663221965379 317600336555494832948069)
              ·
                refine ⟨59550063104155281177763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 317600336555494832948069 59550063104155281177763)
                ·
                  rfl

theorem cell19_195705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 5, 2, 1, 4].length) (baseStart_195705 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_195705 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_195705 prefixEnd_195705 := by exact prefixLift 195705
  have htrace : WordTrace (prefixWord ++ tailWord_195705) baseStart_195705 baseEnd_195705 := by
    simpa [prefixWord, tailWord_195705, baseEnd_195705] using wordTrace_append hprefix tailTrace_195705
  have hstable : (prefixWord ++ tailWord_195705).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_195705).length < 2 ^ (prefixWord ++ tailWord_195705).sum := by decide
  have hdescent : baseEnd_195705 < baseStart_195705 := by decide
  rcases family_descends (prefixWord ++ tailWord_195705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_195798 : List Nat := [5, 2, 1, 2, 2, 2, 5]
def baseStart_195798 : Nat := 118140960795 + 195798 * 2 ^ 59
def prefixEnd_195798 : Nat := 4983230072969 + 3 ^ 40 * 195798 * 2
def baseEnd_195798 : Nat := 19859453864519540370281

theorem tailTrace_195798 : CollatzResearch.WordTrace tailWord_195798 prefixEnd_195798 19859453864519540370281 := by
  unfold tailWord_195798
  simp only [CollatzResearch.WordTrace]
  refine ⟨446333734041547530077753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 4760893163109840320829365 446333734041547530077753)
  ·
    refine ⟨334750300531160647558315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 446333734041547530077753 334750300531160647558315)
    ·
      refine ⟨502125450796740971337473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 334750300531160647558315 502125450796740971337473)
      ·
        refine ⟨376594088097555728503105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 502125450796740971337473 376594088097555728503105)
        ·
          refine ⟨282445566073166796377329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 376594088097555728503105 282445566073166796377329)
          ·
            refine ⟨211834174554875097282997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 282445566073166796377329 211834174554875097282997)
            ·
              refine ⟨19859453864519540370281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 211834174554875097282997 19859453864519540370281)
              ·
                rfl

theorem cell19_195798_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 2, 2, 5].length) (baseStart_195798 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_195798 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_195798 prefixEnd_195798 := by exact prefixLift 195798
  have htrace : WordTrace (prefixWord ++ tailWord_195798) baseStart_195798 baseEnd_195798 := by
    simpa [prefixWord, tailWord_195798, baseEnd_195798] using wordTrace_append hprefix tailTrace_195798
  have hstable : (prefixWord ++ tailWord_195798).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_195798).length < 2 ^ (prefixWord ++ tailWord_195798).sum := by decide
  have hdescent : baseEnd_195798 < baseStart_195798 := by decide
  rcases family_descends (prefixWord ++ tailWord_195798) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_195800 : List Nat := [2, 1, 2, 2, 6, 1, 5]
def baseStart_195800 : Nat := 118140960795 + 195800 * 2 ^ 59
def prefixEnd_195800 : Nat := 4983230072969 + 3 ^ 40 * 195800 * 2
def baseEnd_195800 : Nat := 19859656721074403022131

theorem tailTrace_195800 : CollatzResearch.WordTrace tailWord_195800 prefixEnd_195800 19859656721074403022131 := by
  unfold tailWord_195800
  simp only [CollatzResearch.WordTrace]
  refine ⟨3570706345328757411408427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4760941793771676548544569 3570706345328757411408427)
  ·
    refine ⟨5356059517993136117112641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3570706345328757411408427 5356059517993136117112641)
    ·
      refine ⟨4017044638494852087834481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5356059517993136117112641 4017044638494852087834481)
      ·
        refine ⟨3012783478871139065875861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4017044638494852087834481 3012783478871139065875861)
        ·
          refine ⟨141224225572084643712931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 3012783478871139065875861 141224225572084643712931)
          ·
            refine ⟨211836338358126965569397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 141224225572084643712931 211836338358126965569397)
            ·
              refine ⟨19859656721074403022131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 211836338358126965569397 19859656721074403022131)
              ·
                rfl

theorem cell19_195800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 6, 1, 5].length) (baseStart_195800 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_195800 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_195800 prefixEnd_195800 := by exact prefixLift 195800
  have htrace : WordTrace (prefixWord ++ tailWord_195800) baseStart_195800 baseEnd_195800 := by
    simpa [prefixWord, tailWord_195800, baseEnd_195800] using wordTrace_append hprefix tailTrace_195800
  have hstable : (prefixWord ++ tailWord_195800).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_195800).length < 2 ^ (prefixWord ++ tailWord_195800).sum := by decide
  have hdescent : baseEnd_195800 < baseStart_195800 := by decide
  rcases family_descends (prefixWord ++ tailWord_195800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_195821 : List Nat := [1, 5, 1, 2, 2, 1, 1, 6]
def baseStart_195821 : Nat := 118140960795 + 195821 * 2 ^ 59
def prefixEnd_195821 : Nat := 4983230072969 + 3 ^ 40 * 195821 * 2
def baseEnd_195821 : Nat := 59585360144701382599669

theorem tailTrace_195821 : CollatzResearch.WordTrace tailWord_195821 prefixEnd_195821 59585360144701382599669 := by
  unfold tailWord_195821
  simp only [CollatzResearch.WordTrace]
  refine ⟨7142178623581435409331317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4761452415720956939554211 7142178623581435409331317)
  ·
    refine ⟨669579245960759569624811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 7142178623581435409331317 669579245960759569624811)
    ·
      refine ⟨1004368868941139354437217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 669579245960759569624811 1004368868941139354437217)
      ·
        refine ⟨753276651705854515827913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1004368868941139354437217 753276651705854515827913)
        ·
          refine ⟨564957488779390886870935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 753276651705854515827913 564957488779390886870935)
          ·
            refine ⟨847436233169086330306403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 564957488779390886870935 847436233169086330306403)
            ·
              refine ⟨1271154349753629495459605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 847436233169086330306403 1271154349753629495459605)
              ·
                refine ⟨59585360144701382599669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1271154349753629495459605 59585360144701382599669)
                ·
                  rfl

theorem cell19_195821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 1, 6].length) (baseStart_195821 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_195821 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_195821 prefixEnd_195821 := by exact prefixLift 195821
  have htrace : WordTrace (prefixWord ++ tailWord_195821) baseStart_195821 baseEnd_195821 := by
    simpa [prefixWord, tailWord_195821, baseEnd_195821] using wordTrace_append hprefix tailTrace_195821
  have hstable : (prefixWord ++ tailWord_195821).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_195821).length < 2 ^ (prefixWord ++ tailWord_195821).sum := by decide
  have hdescent : baseEnd_195821 < baseStart_195821 := by decide
  rcases family_descends (prefixWord ++ tailWord_195821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_195874 : List Nat := [3, 3, 1, 1, 5, 1, 1, 4]
def baseStart_195874 : Nat := 118140960795 + 195874 * 2 ^ 59
def prefixEnd_195874 : Nat := 4983230072969 + 3 ^ 40 * 195874 * 2
def baseEnd_195874 : Nat := 59601487240812963421747

theorem tailTrace_195874 : CollatzResearch.WordTrace tailWord_195874 prefixEnd_195874 59601487240812963421747 := by
  unfold tailWord_195874
  simp only [CollatzResearch.WordTrace]
  refine ⟨1786027923097356365252669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4762741128259616974007117 1786027923097356365252669)
  ·
    refine ⟨669760471161508636969751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1786027923097356365252669 669760471161508636969751)
    ·
      refine ⟨1004640706742262955454627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 669760471161508636969751 1004640706742262955454627)
      ·
        refine ⟨1506961060113394433181941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1004640706742262955454627 1506961060113394433181941)
        ·
          refine ⟨141277599385630728110807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 1506961060113394433181941 141277599385630728110807)
          ·
            refine ⟨211916399078446092166211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 141277599385630728110807 211916399078446092166211)
            ·
              refine ⟨317874598617669138249317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 211916399078446092166211 317874598617669138249317)
              ·
                refine ⟨59601487240812963421747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 317874598617669138249317 59601487240812963421747)
                ·
                  rfl

theorem cell19_195874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 5, 1, 1, 4].length) (baseStart_195874 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_195874 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_195874 prefixEnd_195874 := by exact prefixLift 195874
  have htrace : WordTrace (prefixWord ++ tailWord_195874) baseStart_195874 baseEnd_195874 := by
    simpa [prefixWord, tailWord_195874, baseEnd_195874] using wordTrace_append hprefix tailTrace_195874
  have hstable : (prefixWord ++ tailWord_195874).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_195874).length < 2 ^ (prefixWord ++ tailWord_195874).sum := by decide
  have hdescent : baseEnd_195874 < baseStart_195874 := by decide
  rcases family_descends (prefixWord ++ tailWord_195874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_195918 : List Nat := [4, 1, 1, 1, 1, 1, 10]
def baseStart_195918 : Nat := 118140960795 + 195918 * 2 ^ 59
def prefixEnd_195918 : Nat := 4983230072969 + 3 ^ 40 * 195918 * 2
def baseEnd_195918 : Nat := 19871625257811299481283

theorem tailTrace_195918 : CollatzResearch.WordTrace tailWord_195918 prefixEnd_195918 19871625257811299481283 := by
  unfold tailWord_195918
  simp only [CollatzResearch.WordTrace]
  refine ⟨893214563028752621951551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 4763811002820013983741605 893214563028752621951551)
  ·
    refine ⟨1339821844543128932927327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 893214563028752621951551 1339821844543128932927327)
    ·
      refine ⟨2009732766814693399390991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1339821844543128932927327 2009732766814693399390991)
      ·
        refine ⟨3014599150222040099086487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2009732766814693399390991 3014599150222040099086487)
        ·
          refine ⟨4521898725333060148629731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3014599150222040099086487 4521898725333060148629731)
          ·
            refine ⟨6782848087999590222944597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4521898725333060148629731 6782848087999590222944597)
            ·
              refine ⟨19871625257811299481283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 6782848087999590222944597 19871625257811299481283)
              ·
                rfl

theorem cell19_195918_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 10].length) (baseStart_195918 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_195918 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_195918 prefixEnd_195918 := by exact prefixLift 195918
  have htrace : WordTrace (prefixWord ++ tailWord_195918) baseStart_195918 baseEnd_195918 := by
    simpa [prefixWord, tailWord_195918, baseEnd_195918] using wordTrace_append hprefix tailTrace_195918
  have hstable : (prefixWord ++ tailWord_195918).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_195918).length < 2 ^ (prefixWord ++ tailWord_195918).sum := by decide
  have hdescent : baseEnd_195918 < baseStart_195918 := by decide
  rcases family_descends (prefixWord ++ tailWord_195918) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_195975 : List Nat := [1, 1, 4, 2, 2, 2, 7]
def baseStart_195975 : Nat := 118140960795 + 195975 * 2 ^ 59
def prefixEnd_195975 : Nat := 4983230072969 + 3 ^ 40 * 195975 * 2
def baseEnd_195975 : Nat := 19877406669624885059009

theorem tailTrace_195975 : CollatzResearch.WordTrace tailWord_195975 prefixEnd_195975 19877406669624885059009 := by
  unfold tailWord_195975
  simp only [CollatzResearch.WordTrace]
  refine ⟨7147795465023519710437379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4765196976682346473624919 7147795465023519710437379)
  ·
    refine ⟨10721693197535279565656069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7147795465023519710437379 10721693197535279565656069)
    ·
      refine ⟨2010317474537864918560513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10721693197535279565656069 2010317474537864918560513)
      ·
        refine ⟨1507738105903398688920385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2010317474537864918560513 1507738105903398688920385)
        ·
          refine ⟨1130803579427549016690289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1507738105903398688920385 1130803579427549016690289)
          ·
            refine ⟨848102684570661762517717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1130803579427549016690289 848102684570661762517717)
            ·
              refine ⟨19877406669624885059009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 848102684570661762517717 19877406669624885059009)
              ·
                rfl

theorem cell19_195975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 7].length) (baseStart_195975 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_195975 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_195975 prefixEnd_195975 := by exact prefixLift 195975
  have htrace : WordTrace (prefixWord ++ tailWord_195975) baseStart_195975 baseEnd_195975 := by
    simpa [prefixWord, tailWord_195975, baseEnd_195975] using wordTrace_append hprefix tailTrace_195975
  have hstable : (prefixWord ++ tailWord_195975).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_195975).length < 2 ^ (prefixWord ++ tailWord_195975).sum := by decide
  have hdescent : baseEnd_195975 < baseStart_195975 := by decide
  rcases family_descends (prefixWord ++ tailWord_195975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_196165 : List Nat := [1, 3, 1, 1, 1, 4, 4, 4]
def baseStart_196165 : Nat := 118140960795 + 196165 * 2 ^ 59
def prefixEnd_196165 : Nat := 4983230072969 + 3 ^ 40 * 196165 * 2
def baseEnd_196165 : Nat := 59690034127010510954287

theorem tailTrace_196165 : CollatzResearch.WordTrace tailWord_196165 prefixEnd_196165 59690034127010510954287 := by
  unfold tailWord_196165
  simp only [CollatzResearch.WordTrace]
  refine ⟨7154725334335182159853949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4769816889556788106569299 7154725334335182159853949)
  ·
    refine ⟨2683022000375693309945231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7154725334335182159853949 2683022000375693309945231)
    ·
      refine ⟨4024533000563539964917847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2683022000375693309945231 4024533000563539964917847)
      ·
        refine ⟨6036799500845309947376771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4024533000563539964917847 6036799500845309947376771)
        ·
          refine ⟨9055199251267964921065157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6036799500845309947376771 9055199251267964921065157)
          ·
            refine ⟨1697849859612743422699717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9055199251267964921065157 1697849859612743422699717)
            ·
              refine ⟨318346848677389391756197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1697849859612743422699717 318346848677389391756197)
              ·
                refine ⟨59690034127010510954287, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 318346848677389391756197 59690034127010510954287)
                ·
                  rfl

theorem cell19_196165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 4, 4].length) (baseStart_196165 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_196165 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_196165 prefixEnd_196165 := by exact prefixLift 196165
  have htrace : WordTrace (prefixWord ++ tailWord_196165) baseStart_196165 baseEnd_196165 := by
    simpa [prefixWord, tailWord_196165, baseEnd_196165] using wordTrace_append hprefix tailTrace_196165
  have hstable : (prefixWord ++ tailWord_196165).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_196165).length < 2 ^ (prefixWord ++ tailWord_196165).sum := by decide
  have hdescent : baseEnd_196165 < baseStart_196165 := by decide
  rcases family_descends (prefixWord ++ tailWord_196165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_196260 : List Nat := [2, 3, 1, 2, 2, 3, 6]
def baseStart_196260 : Nat := 118140960795 + 196260 * 2 ^ 59
def prefixEnd_196260 : Nat := 4983230072969 + 3 ^ 40 * 196260 * 2
def baseEnd_196260 : Nat := 19906313728692812947639

theorem tailTrace_196260 : CollatzResearch.WordTrace tailWord_196260 prefixEnd_196260 19906313728692812947639 := by
  unfold tailWord_196260
  simp only [CollatzResearch.WordTrace]
  refine ⟨3579095134495506692281117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4772126845994008923041489 3579095134495506692281117)
  ·
    refine ⟨1342160675435815009605419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3579095134495506692281117 1342160675435815009605419)
    ·
      refine ⟨2013241013153722514408129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1342160675435815009605419 2013241013153722514408129)
      ·
        refine ⟨1509930759865291885806097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2013241013153722514408129 1509930759865291885806097)
        ·
          refine ⟨1132448069898968914354573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1509930759865291885806097 1132448069898968914354573)
          ·
            refine ⟨424668026212113342882965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1132448069898968914354573 424668026212113342882965)
            ·
              refine ⟨19906313728692812947639, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 424668026212113342882965 19906313728692812947639)
              ·
                rfl

theorem cell19_196260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 3, 6].length) (baseStart_196260 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_196260 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_196260 prefixEnd_196260 := by exact prefixLift 196260
  have htrace : WordTrace (prefixWord ++ tailWord_196260) baseStart_196260 baseEnd_196260 := by
    simpa [prefixWord, tailWord_196260, baseEnd_196260] using wordTrace_append hprefix tailTrace_196260
  have hstable : (prefixWord ++ tailWord_196260).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_196260).length < 2 ^ (prefixWord ++ tailWord_196260).sum := by decide
  have hdescent : baseEnd_196260 < baseStart_196260 := by decide
  rcases family_descends (prefixWord ++ tailWord_196260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_196410 : List Nat := [3, 1, 1, 1, 5, 2, 3, 3]
def baseStart_196410 : Nat := 118140960795 + 196410 * 2 ^ 59
def prefixEnd_196410 : Nat := 4983230072969 + 3 ^ 40 * 196410 * 2
def baseEnd_196410 : Nat := 59764583910922535509175

theorem tailTrace_196410 : CollatzResearch.WordTrace tailWord_196410 prefixEnd_196410 59764583910922535509175 := by
  unfold tailWord_196410
  simp only [CollatzResearch.WordTrace]
  refine ⟨1790915304611897250630671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4775774145631726001681789 1790915304611897250630671)
  ·
    refine ⟨2686372956917845875946007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1790915304611897250630671 2686372956917845875946007)
    ·
      refine ⟨4029559435376768813919011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2686372956917845875946007 4029559435376768813919011)
      ·
        refine ⟨6044339153065153220878517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4029559435376768813919011 6044339153065153220878517)
        ·
          refine ⟨566656795599858114457361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 6044339153065153220878517 566656795599858114457361)
          ·
            refine ⟨424992596699893585843021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 566656795599858114457361 424992596699893585843021)
            ·
              refine ⟨159372223762460094691133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 424992596699893585843021 159372223762460094691133)
              ·
                refine ⟨59764583910922535509175, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 159372223762460094691133 59764583910922535509175)
                ·
                  rfl

theorem cell19_196410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 2, 3, 3].length) (baseStart_196410 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_196410 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_196410 prefixEnd_196410 := by exact prefixLift 196410
  have htrace : WordTrace (prefixWord ++ tailWord_196410) baseStart_196410 baseEnd_196410 := by
    simpa [prefixWord, tailWord_196410, baseEnd_196410] using wordTrace_append hprefix tailTrace_196410
  have hstable : (prefixWord ++ tailWord_196410).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_196410).length < 2 ^ (prefixWord ++ tailWord_196410).sum := by decide
  have hdescent : baseEnd_196410 < baseStart_196410 := by decide
  rcases family_descends (prefixWord ++ tailWord_196410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_196429 : List Nat := [1, 6, 1, 2, 1, 2, 6]
def baseStart_196429 : Nat := 118140960795 + 196429 * 2 ^ 59
def prefixEnd_196429 : Nat := 4983230072969 + 3 ^ 40 * 196429 * 2
def baseEnd_196429 : Nat := 19923455107578707028967

theorem tailTrace_196429 : CollatzResearch.WordTrace tailWord_196429 prefixEnd_196429 19923455107578707028967 := by
  unfold tailWord_196429
  simp only [CollatzResearch.WordTrace]
  refine ⟨7164354205378755247464341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4776236136919170164976227 7164354205378755247464341)
  ·
    refine ⟨335829103377129152224891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 7164354205378755247464341 335829103377129152224891)
    ·
      refine ⟨503743655065693728337337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 335829103377129152224891 503743655065693728337337)
      ·
        refine ⟨377807741299270296253003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 503743655065693728337337 377807741299270296253003)
        ·
          refine ⟨566711611948905444379505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 377807741299270296253003 566711611948905444379505)
          ·
            refine ⟨425033708961679083284629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 566711611948905444379505 425033708961679083284629)
            ·
              refine ⟨19923455107578707028967, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 425033708961679083284629 19923455107578707028967)
              ·
                rfl

theorem cell19_196429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 2, 6].length) (baseStart_196429 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_196429 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_196429 prefixEnd_196429 := by exact prefixLift 196429
  have htrace : WordTrace (prefixWord ++ tailWord_196429) baseStart_196429 baseEnd_196429 := by
    simpa [prefixWord, tailWord_196429, baseEnd_196429] using wordTrace_append hprefix tailTrace_196429
  have hstable : (prefixWord ++ tailWord_196429).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_196429).length < 2 ^ (prefixWord ++ tailWord_196429).sum := by decide
  have hdescent : baseEnd_196429 < baseStart_196429 := by decide
  rcases family_descends (prefixWord ++ tailWord_196429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_196469 : List Nat := [1, 3, 4, 1, 1, 1, 3, 5]
def baseStart_196469 : Nat := 118140960795 + 196469 * 2 ^ 59
def prefixEnd_196469 : Nat := 4983230072969 + 3 ^ 40 * 196469 * 2
def baseEnd_196469 : Nat := 59782536716027880197903

theorem tailTrace_196469 : CollatzResearch.WordTrace tailWord_196469 prefixEnd_196469 59782536716027880197903 := by
  unfold tailWord_196469
  simp only [CollatzResearch.WordTrace]
  refine ⟨7165813125233842078920461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4777208750155894719280307 7165813125233842078920461)
  ·
    refine ⟨2687179921962690779595173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7165813125233842078920461 2687179921962690779595173)
    ·
      refine ⟨503846235368004521174095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2687179921962690779595173 503846235368004521174095)
      ·
        refine ⟨755769353052006781761143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 503846235368004521174095 755769353052006781761143)
        ·
          refine ⟨1133654029578010172641715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 755769353052006781761143 1133654029578010172641715)
          ·
            refine ⟨1700481044367015258962573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1133654029578010172641715 1700481044367015258962573)
            ·
              refine ⟨637680391637630722110965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1700481044367015258962573 637680391637630722110965)
              ·
                refine ⟨59782536716027880197903, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 637680391637630722110965 59782536716027880197903)
                ·
                  rfl

theorem cell19_196469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 3, 5].length) (baseStart_196469 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_196469 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_196469 prefixEnd_196469 := by exact prefixLift 196469
  have htrace : WordTrace (prefixWord ++ tailWord_196469) baseStart_196469 baseEnd_196469 := by
    simpa [prefixWord, tailWord_196469, baseEnd_196469] using wordTrace_append hprefix tailTrace_196469
  have hstable : (prefixWord ++ tailWord_196469).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_196469).length < 2 ^ (prefixWord ++ tailWord_196469).sum := by decide
  have hdescent : baseEnd_196469 < baseStart_196469 := by decide
  rcases family_descends (prefixWord ++ tailWord_196469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_196604 : List Nat := [2, 2, 2, 1, 2, 2, 8]
def baseStart_196604 : Nat := 118140960795 + 196604 * 2 ^ 59
def prefixEnd_196604 : Nat := 4983230072969 + 3 ^ 40 * 196604 * 2
def baseEnd_196604 : Nat := 19941205056129189065845

theorem tailTrace_196604 : CollatzResearch.WordTrace tailWord_196604 prefixEnd_196604 19941205056129189065845 := by
  unfold tailWord_196604
  simp only [CollatzResearch.WordTrace]
  refine ⟨3585368489872380067542433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4780491319829840090056577 3585368489872380067542433)
  ·
    refine ⟨2689026367404285050656825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3585368489872380067542433 2689026367404285050656825)
    ·
      refine ⟨2016769775553213787992619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2689026367404285050656825 2016769775553213787992619)
      ·
        refine ⟨3025154663329820681988929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2016769775553213787992619 3025154663329820681988929)
        ·
          refine ⟨2268865997497365511491697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3025154663329820681988929 2268865997497365511491697)
          ·
            refine ⟨1701649498123024133618773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2268865997497365511491697 1701649498123024133618773)
            ·
              refine ⟨19941205056129189065845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1701649498123024133618773 19941205056129189065845)
              ·
                rfl

theorem cell19_196604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 8].length) (baseStart_196604 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_196604 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_196604 prefixEnd_196604 := by exact prefixLift 196604
  have htrace : WordTrace (prefixWord ++ tailWord_196604) baseStart_196604 baseEnd_196604 := by
    simpa [prefixWord, tailWord_196604, baseEnd_196604] using wordTrace_append hprefix tailTrace_196604
  have hstable : (prefixWord ++ tailWord_196604).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_196604).length < 2 ^ (prefixWord ++ tailWord_196604).sum := by decide
  have hdescent : baseEnd_196604 < baseStart_196604 := by decide
  rcases family_descends (prefixWord ++ tailWord_196604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_196661 : List Nat := [1, 3, 3, 1, 1, 1, 9]
def baseStart_196661 : Nat := 118140960795 + 196661 * 2 ^ 59
def prefixEnd_196661 : Nat := 4983230072969 + 3 ^ 40 * 196661 * 2
def baseEnd_196661 : Nat := 19946986467942774643571

theorem tailTrace_196661 : CollatzResearch.WordTrace tailWord_196661 prefixEnd_196661 19946986467942774643571 := by
  unfold tailWord_196661
  simp only [CollatzResearch.WordTrace]
  refine ⟨7172815940538258869909837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4781877293692172579939891 7172815940538258869909837)
  ·
    refine ⟨2689805977701847076216189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7172815940538258869909837 2689805977701847076216189)
    ·
      refine ⟨1008677241638192653581071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2689805977701847076216189 1008677241638192653581071)
      ·
        refine ⟨1513015862457288980371607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1008677241638192653581071 1513015862457288980371607)
        ·
          refine ⟨2269523793685933470557411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1513015862457288980371607 2269523793685933470557411)
          ·
            refine ⟨3404285690528900205836117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2269523793685933470557411 3404285690528900205836117)
            ·
              refine ⟨19946986467942774643571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 3404285690528900205836117 19946986467942774643571)
              ·
                rfl

theorem cell19_196661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 9].length) (baseStart_196661 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_196661 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_196661 prefixEnd_196661 := by exact prefixLift 196661
  have htrace : WordTrace (prefixWord ++ tailWord_196661) baseStart_196661 baseEnd_196661 := by
    simpa [prefixWord, tailWord_196661, baseEnd_196661] using wordTrace_append hprefix tailTrace_196661
  have hstable : (prefixWord ++ tailWord_196661).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_196661).length < 2 ^ (prefixWord ++ tailWord_196661).sum := by decide
  have hdescent : baseEnd_196661 < baseStart_196661 := by decide
  rcases family_descends (prefixWord ++ tailWord_196661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_196851 : List Nat := [1, 1, 1, 2, 2, 4, 4, 4]
def baseStart_196851 : Nat := 118140960795 + 196851 * 2 ^ 59
def prefixEnd_196851 : Nat := 4983230072969 + 3 ^ 40 * 196851 * 2
def baseEnd_196851 : Nat := 59898773521964179707973

theorem tailTrace_196851 : CollatzResearch.WordTrace tailWord_196851 prefixEnd_196851 59898773521964179707973 := by
  unfold tailWord_196851
  simp only [CollatzResearch.WordTrace]
  refine ⟨7179745809849921319326407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4786497206566614212884271 7179745809849921319326407)
  ·
    refine ⟨10769618714774881978989611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7179745809849921319326407 10769618714774881978989611)
    ·
      refine ⟨16154428072162322968484417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10769618714774881978989611 16154428072162322968484417)
      ·
        refine ⟨12115821054121742226363313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16154428072162322968484417 12115821054121742226363313)
        ·
          refine ⟨9086865790591306669772485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12115821054121742226363313 9086865790591306669772485)
          ·
            refine ⟨1703787335735870000582341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9086865790591306669772485 1703787335735870000582341)
            ·
              refine ⟨319460125450475625109189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1703787335735870000582341 319460125450475625109189)
              ·
                refine ⟨59898773521964179707973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 319460125450475625109189 59898773521964179707973)
                ·
                  rfl

theorem cell19_196851_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 4, 4].length) (baseStart_196851 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_196851 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_196851 prefixEnd_196851 := by exact prefixLift 196851
  have htrace : WordTrace (prefixWord ++ tailWord_196851) baseStart_196851 baseEnd_196851 := by
    simpa [prefixWord, tailWord_196851, baseEnd_196851] using wordTrace_append hprefix tailTrace_196851
  have hstable : (prefixWord ++ tailWord_196851).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_196851).length < 2 ^ (prefixWord ++ tailWord_196851).sum := by decide
  have hdescent : baseEnd_196851 < baseStart_196851 := by decide
  rcases family_descends (prefixWord ++ tailWord_196851) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_196904 : List Nat := [2, 1, 5, 1, 3, 2, 1, 4]
def baseStart_196904 : Nat := 118140960795 + 196904 * 2 ^ 59
def prefixEnd_196904 : Nat := 4983230072969 + 3 ^ 40 * 196904 * 2
def baseEnd_196904 : Nat := 59914900618075760530051

theorem tailTrace_196904 : CollatzResearch.WordTrace tailWord_196904 prefixEnd_196904 59914900618075760530051 := by
  unfold tailWord_196904
  simp only [CollatzResearch.WordTrace]
  refine ⟨3590839439328955685502883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4787785919105274247337177 3590839439328955685502883)
  ·
    refine ⟨5386259158993433528254325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3590839439328955685502883 5386259158993433528254325)
    ·
      refine ⟨504961796155634393273843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 5386259158993433528254325 504961796155634393273843)
      ·
        refine ⟨757442694233451589910765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 504961796155634393273843 757442694233451589910765)
        ·
          refine ⟨284041010337544346216537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 757442694233451589910765 284041010337544346216537)
          ·
            refine ⟨213030757753158259662403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 284041010337544346216537 213030757753158259662403)
            ·
              refine ⟨319546136629737389493605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 213030757753158259662403 319546136629737389493605)
              ·
                refine ⟨59914900618075760530051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 319546136629737389493605 59914900618075760530051)
                ·
                  rfl

theorem cell19_196904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 3, 2, 1, 4].length) (baseStart_196904 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_196904 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_196904 prefixEnd_196904 := by exact prefixLift 196904
  have htrace : WordTrace (prefixWord ++ tailWord_196904) baseStart_196904 baseEnd_196904 := by
    simpa [prefixWord, tailWord_196904, baseEnd_196904] using wordTrace_append hprefix tailTrace_196904
  have hstable : (prefixWord ++ tailWord_196904).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_196904).length < 2 ^ (prefixWord ++ tailWord_196904).sum := by decide
  have hdescent : baseEnd_196904 < baseStart_196904 := by decide
  rcases family_descends (prefixWord ++ tailWord_196904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_196908 : List Nat := [2, 2, 1, 1, 1, 3, 5, 4]
def baseStart_196908 : Nat := 118140960795 + 196908 * 2 ^ 59
def prefixEnd_196908 : Nat := 4983230072969 + 3 ^ 40 * 196908 * 2
def baseEnd_196908 : Nat := 59916117757404936441151

theorem tailTrace_196908 : CollatzResearch.WordTrace tailWord_196908 prefixEnd_196908 59916117757404936441151 := by
  unfold tailWord_196908
  simp only [CollatzResearch.WordTrace]
  refine ⟨3590912385321710027075689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4787883180428946702767585 3590912385321710027075689)
  ·
    refine ⟨2693184288991282520306767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3590912385321710027075689 2693184288991282520306767)
    ·
      refine ⟨4039776433486923780460151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2693184288991282520306767 4039776433486923780460151)
      ·
        refine ⟨6059664650230385670690227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4039776433486923780460151 6059664650230385670690227)
        ·
          refine ⟨9089496975345578506035341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6059664650230385670690227 9089496975345578506035341)
          ·
            refine ⟨3408561365754591939763253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9089496975345578506035341 3408561365754591939763253)
            ·
              refine ⟨319552628039492994352805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 3408561365754591939763253 319552628039492994352805)
              ·
                refine ⟨59916117757404936441151, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 319552628039492994352805 59916117757404936441151)
                ·
                  rfl

theorem cell19_196908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 5, 4].length) (baseStart_196908 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_196908 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_196908 prefixEnd_196908 := by exact prefixLift 196908
  have htrace : WordTrace (prefixWord ++ tailWord_196908) baseStart_196908 baseEnd_196908 := by
    simpa [prefixWord, tailWord_196908, baseEnd_196908] using wordTrace_append hprefix tailTrace_196908
  have hstable : (prefixWord ++ tailWord_196908).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_196908).length < 2 ^ (prefixWord ++ tailWord_196908).sum := by decide
  have hdescent : baseEnd_196908 < baseStart_196908 := by decide
  rcases family_descends (prefixWord ++ tailWord_196908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_197003 : List Nat := [1, 1, 1, 1, 4, 6, 5]
def baseStart_197003 : Nat := 118140960795 + 197003 * 2 ^ 59
def prefixEnd_197003 : Nat := 4983230072969 + 3 ^ 40 * 197003 * 2
def baseEnd_197003 : Nat := 19981674938824288109927

theorem tailTrace_197003 : CollatzResearch.WordTrace tailWord_197003 prefixEnd_197003 19981674938824288109927 := by
  unfold tailWord_197003
  simp only [CollatzResearch.WordTrace]
  refine ⟨7185289705299251278859663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4790193136866167519239775 7185289705299251278859663)
  ·
    refine ⟨10777934557948876918289495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7185289705299251278859663 10777934557948876918289495)
    ·
      refine ⟨16166901836923315377434243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10777934557948876918289495 16166901836923315377434243)
      ·
        refine ⟨24250352755384973066151365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16166901836923315377434243 24250352755384973066151365)
        ·
          refine ⟨4546941141634682449903381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 24250352755384973066151365 4546941141634682449903381)
          ·
            refine ⟨213137866014125739839221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 4546941141634682449903381 213137866014125739839221)
            ·
              refine ⟨19981674938824288109927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 213137866014125739839221 19981674938824288109927)
              ·
                rfl

theorem cell19_197003_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 6, 5].length) (baseStart_197003 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_197003 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_197003 prefixEnd_197003 := by exact prefixLift 197003
  have htrace : WordTrace (prefixWord ++ tailWord_197003) baseStart_197003 baseEnd_197003 := by
    simpa [prefixWord, tailWord_197003, baseEnd_197003] using wordTrace_append hprefix tailTrace_197003
  have hstable : (prefixWord ++ tailWord_197003).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_197003).length < 2 ^ (prefixWord ++ tailWord_197003).sum := by decide
  have hdescent : baseEnd_197003 < baseStart_197003 := by decide
  rcases family_descends (prefixWord ++ tailWord_197003) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_197014 : List Nat := [5, 3, 1, 2, 1, 1, 2, 4]
def baseStart_197014 : Nat := 118140960795 + 197014 * 2 ^ 59
def prefixEnd_197014 : Nat := 4983230072969 + 3 ^ 40 * 197014 * 2
def baseEnd_197014 : Nat := 59948371949628098085307

theorem tailTrace_197014 : CollatzResearch.WordTrace tailWord_197014 prefixEnd_197014 59948371949628098085307 := by
  unfold tailWord_197014
  simp only [CollatzResearch.WordTrace]
  refine ⟨449105681766212509844381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 4790460605506266771673397 449105681766212509844381)
  ·
    refine ⟨168414630662329691191643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 449105681766212509844381 168414630662329691191643)
    ·
      refine ⟨252621945993494536787465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 168414630662329691191643 252621945993494536787465)
      ·
        refine ⟨189466459495120902590599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 252621945993494536787465 189466459495120902590599)
        ·
          refine ⟨284199689242681353885899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 189466459495120902590599 284199689242681353885899)
          ·
            refine ⟨426299533864022030828849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 284199689242681353885899 426299533864022030828849)
            ·
              refine ⟨319724650398016523121637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 426299533864022030828849 319724650398016523121637)
              ·
                refine ⟨59948371949628098085307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 319724650398016523121637 59948371949628098085307)
                ·
                  rfl

theorem cell19_197014_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 1, 1, 2, 4].length) (baseStart_197014 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_197014 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_197014 prefixEnd_197014 := by exact prefixLift 197014
  have htrace : WordTrace (prefixWord ++ tailWord_197014) baseStart_197014 baseEnd_197014 := by
    simpa [prefixWord, tailWord_197014, baseEnd_197014] using wordTrace_append hprefix tailTrace_197014
  have hstable : (prefixWord ++ tailWord_197014).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_197014).length < 2 ^ (prefixWord ++ tailWord_197014).sum := by decide
  have hdescent : baseEnd_197014 < baseStart_197014 := by decide
  rcases family_descends (prefixWord ++ tailWord_197014) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_197041 : List Nat := [1, 2, 2, 4, 1, 2, 2, 5]
def baseStart_197041 : Nat := 118140960795 + 197041 * 2 ^ 59
def prefixEnd_197041 : Nat := 4983230072969 + 3 ^ 40 * 197041 * 2
def baseEnd_197041 : Nat := 59956587640100035485233

theorem tailTrace_197041 : CollatzResearch.WordTrace tailWord_197041 prefixEnd_197041 59956587640100035485233 := by
  unfold tailWord_197041
  simp only [CollatzResearch.WordTrace]
  refine ⟨7186675679161583768742977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4791117119441055845828651 7186675679161583768742977)
  ·
    refine ⟨5390006759371187826557233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7186675679161583768742977 5390006759371187826557233)
    ·
      refine ⟨4042505069528390869917925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5390006759371187826557233 4042505069528390869917925)
      ·
        refine ⟨757969700536573288109611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4042505069528390869917925 757969700536573288109611)
        ·
          refine ⟨1136954550804859932164417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 757969700536573288109611 1136954550804859932164417)
          ·
            refine ⟨852715913103644949123313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1136954550804859932164417 852715913103644949123313)
            ·
              refine ⟨639536934827733711842485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 852715913103644949123313 639536934827733711842485)
              ·
                refine ⟨59956587640100035485233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 639536934827733711842485 59956587640100035485233)
                ·
                  rfl

theorem cell19_197041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 2, 5].length) (baseStart_197041 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_197041 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_197041 prefixEnd_197041 := by exact prefixLift 197041
  have htrace : WordTrace (prefixWord ++ tailWord_197041) baseStart_197041 baseEnd_197041 := by
    simpa [prefixWord, tailWord_197041, baseEnd_197041] using wordTrace_append hprefix tailTrace_197041
  have hstable : (prefixWord ++ tailWord_197041).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_197041).length < 2 ^ (prefixWord ++ tailWord_197041).sum := by decide
  have hdescent : baseEnd_197041 < baseStart_197041 := by decide
  rcases family_descends (prefixWord ++ tailWord_197041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_197060 : List Nat := [2, 3, 3, 2, 9]
def baseStart_197060 : Nat := 118140960795 + 197060 * 2 ^ 59
def prefixEnd_197060 : Nat := 4983230072969 + 3 ^ 40 * 197060 * 2
def baseEnd_197060 : Nat := 2220828483404208187517

theorem tailTrace_197060 : CollatzResearch.WordTrace tailWord_197060 prefixEnd_197060 2220828483404208187517 := by
  unfold tailWord_197060
  simp only [CollatzResearch.WordTrace]
  refine ⟨3593684333046375006842317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4791579110728500009123089 3593684333046375006842317)
  ·
    refine ⟨1347631624892390627565869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3593684333046375006842317 1347631624892390627565869)
    ·
      refine ⟨505361859334646485337201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1347631624892390627565869 505361859334646485337201)
      ·
        refine ⟨379021394500984864002901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 505361859334646485337201 379021394500984864002901)
        ·
          refine ⟨2220828483404208187517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 9 379021394500984864002901 2220828483404208187517)
          ·
            rfl

theorem cell19_197060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 9].length) (baseStart_197060 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_197060 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_197060 prefixEnd_197060 := by exact prefixLift 197060
  have htrace : WordTrace (prefixWord ++ tailWord_197060) baseStart_197060 baseEnd_197060 := by
    simpa [prefixWord, tailWord_197060, baseEnd_197060] using wordTrace_append hprefix tailTrace_197060
  have hstable : (prefixWord ++ tailWord_197060).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_197060).length < 2 ^ (prefixWord ++ tailWord_197060).sum := by decide
  have hdescent : baseEnd_197060 < baseStart_197060 := by decide
  rcases family_descends (prefixWord ++ tailWord_197060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_197077 : List Nat := [1, 3, 2, 3, 1, 4, 1, 4]
def baseStart_197077 : Nat := 118140960795 + 197077 * 2 ^ 59
def prefixEnd_197077 : Nat := 4983230072969 + 3 ^ 40 * 197077 * 2
def baseEnd_197077 : Nat := 59967541894062618685135

theorem tailTrace_197077 : CollatzResearch.WordTrace tailWord_197077 prefixEnd_197077 59967541894062618685135 := by
  unfold tailWord_197077
  simp only [CollatzResearch.WordTrace]
  refine ⟨7187988707031161917053485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4791992471354107944702323 7187988707031161917053485)
  ·
    refine ⟨2695495765136685718895057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7187988707031161917053485 2695495765136685718895057)
    ·
      refine ⟨2021621823852514289171293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2695495765136685718895057 2021621823852514289171293)
      ·
        refine ⟨758108183944692858439235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2021621823852514289171293 758108183944692858439235)
        ·
          refine ⟨1137162275917039287658853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 758108183944692858439235 1137162275917039287658853)
          ·
            refine ⟨213217926734444866436035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1137162275917039287658853 213217926734444866436035)
            ·
              refine ⟨319826890101667299654053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 213217926734444866436035 319826890101667299654053)
              ·
                refine ⟨59967541894062618685135, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 319826890101667299654053 59967541894062618685135)
                ·
                  rfl

theorem cell19_197077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 4, 1, 4].length) (baseStart_197077 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_197077 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_197077 prefixEnd_197077 := by exact prefixLift 197077
  have htrace : WordTrace (prefixWord ++ tailWord_197077) baseStart_197077 baseEnd_197077 := by
    simpa [prefixWord, tailWord_197077, baseEnd_197077] using wordTrace_append hprefix tailTrace_197077
  have hstable : (prefixWord ++ tailWord_197077).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_197077).length < 2 ^ (prefixWord ++ tailWord_197077).sum := by decide
  have hdescent : baseEnd_197077 < baseStart_197077 := by decide
  rcases family_descends (prefixWord ++ tailWord_197077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_197096 : List Nat := [2, 1, 4, 1, 1, 4, 3, 3]
def baseStart_197096 : Nat := 118140960795 + 197096 * 2 ^ 59
def prefixEnd_197096 : Nat := 4983230072969 + 3 ^ 40 * 197096 * 2
def baseEnd_197096 : Nat := 59973323305876204262861

theorem tailTrace_197096 : CollatzResearch.WordTrace tailWord_197096 prefixEnd_197096 59973323305876204262861 := by
  unfold tailWord_197096
  simp only [CollatzResearch.WordTrace]
  refine ⟨3594340846981164080997571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4792454462641552107996761 3594340846981164080997571)
  ·
    refine ⟨5391511270471746121496357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3594340846981164080997571 5391511270471746121496357)
    ·
      refine ⟨1010908363213452397780567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5391511270471746121496357 1010908363213452397780567)
      ·
        refine ⟨1516362544820178596670851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1010908363213452397780567 1516362544820178596670851)
        ·
          refine ⟨2274543817230267895006277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1516362544820178596670851 2274543817230267895006277)
          ·
            refine ⟨426476965730675230313677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2274543817230267895006277 426476965730675230313677)
            ·
              refine ⟨159928862149003211367629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 426476965730675230313677 159928862149003211367629)
              ·
                refine ⟨59973323305876204262861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 159928862149003211367629 59973323305876204262861)
                ·
                  rfl

theorem cell19_197096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 4, 3, 3].length) (baseStart_197096 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_197096 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_197096 prefixEnd_197096 := by exact prefixLift 197096
  have htrace : WordTrace (prefixWord ++ tailWord_197096) baseStart_197096 baseEnd_197096 := by
    simpa [prefixWord, tailWord_197096, baseEnd_197096] using wordTrace_append hprefix tailTrace_197096
  have hstable : (prefixWord ++ tailWord_197096).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_197096).length < 2 ^ (prefixWord ++ tailWord_197096).sum := by decide
  have hdescent : baseEnd_197096 < baseStart_197096 := by decide
  rcases family_descends (prefixWord ++ tailWord_197096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_197119 : List Nat := [1, 1, 2, 2, 1, 2, 10]
def baseStart_197119 : Nat := 118140960795 + 197119 * 2 ^ 59
def prefixEnd_197119 : Nat := 4983230072969 + 3 ^ 40 * 197119 * 2
def baseEnd_197119 : Nat := 19993440619006321917229

theorem tailTrace_197119 : CollatzResearch.WordTrace tailWord_197119 prefixEnd_197119 19993440619006321917229 := by
  unfold tailWord_197119
  simp only [CollatzResearch.WordTrace]
  refine ⟨7189520572879003090082411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4793013715252668726721607 7189520572879003090082411)
  ·
    refine ⟨10784280859318504635123617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7189520572879003090082411 10784280859318504635123617)
    ·
      refine ⟨8088210644488878476342713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10784280859318504635123617 8088210644488878476342713)
      ·
        refine ⟨6066157983366658857257035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8088210644488878476342713 6066157983366658857257035)
        ·
          refine ⟨9099236975049988285885553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6066157983366658857257035 9099236975049988285885553)
          ·
            refine ⟨6824427731287491214414165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9099236975049988285885553 6824427731287491214414165)
            ·
              refine ⟨19993440619006321917229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 6824427731287491214414165 19993440619006321917229)
              ·
                rfl

theorem cell19_197119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 10].length) (baseStart_197119 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_197119 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_197119 prefixEnd_197119 := by exact prefixLift 197119
  have htrace : WordTrace (prefixWord ++ tailWord_197119) baseStart_197119 baseEnd_197119 := by
    simpa [prefixWord, tailWord_197119, baseEnd_197119] using wordTrace_append hprefix tailTrace_197119
  have hstable : (prefixWord ++ tailWord_197119).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_197119).length < 2 ^ (prefixWord ++ tailWord_197119).sum := by decide
  have hdescent : baseEnd_197119 < baseStart_197119 := by decide
  rcases family_descends (prefixWord ++ tailWord_197119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_197155 : List Nat := [1, 1, 1, 4, 4, 2, 1, 5]
def baseStart_197155 : Nat := 118140960795 + 197155 * 2 ^ 59
def prefixEnd_197155 : Nat := 4983230072969 + 3 ^ 40 * 197155 * 2
def baseEnd_197155 : Nat := 59991276110981548951589

theorem tailTrace_197155 : CollatzResearch.WordTrace tailWord_197155 prefixEnd_197155 59991276110981548951589 := by
  unfold tailWord_197155
  simp only [CollatzResearch.WordTrace]
  refine ⟨7190833600748581238392919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4793889067165720825595279 7190833600748581238392919)
  ·
    refine ⟨10786250401122871857589379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7190833600748581238392919 10786250401122871857589379)
    ·
      refine ⟨16179375601684307786384069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10786250401122871857589379 16179375601684307786384069)
      ·
        refine ⟨3033632925315807709947013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 16179375601684307786384069 3033632925315807709947013)
        ·
          refine ⟨568806173496713945615065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3033632925315807709947013 568806173496713945615065)
          ·
            refine ⟨426604630122535459211299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 568806173496713945615065 426604630122535459211299)
            ·
              refine ⟨639906945183803188816949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 426604630122535459211299 639906945183803188816949)
              ·
                refine ⟨59991276110981548951589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 639906945183803188816949 59991276110981548951589)
                ·
                  rfl

theorem cell19_197155_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 2, 1, 5].length) (baseStart_197155 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_197155 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_197155 prefixEnd_197155 := by exact prefixLift 197155
  have htrace : WordTrace (prefixWord ++ tailWord_197155) baseStart_197155 baseEnd_197155 := by
    simpa [prefixWord, tailWord_197155, baseEnd_197155] using wordTrace_append hprefix tailTrace_197155
  have hstable : (prefixWord ++ tailWord_197155).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_197155).length < 2 ^ (prefixWord ++ tailWord_197155).sum := by decide
  have hdescent : baseEnd_197155 < baseStart_197155 := by decide
  rcases family_descends (prefixWord ++ tailWord_197155) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_197195 : List Nat := [1, 1, 1, 1, 3, 1, 5, 6]
def baseStart_197195 : Nat := 118140960795 + 197195 * 2 ^ 59
def prefixEnd_197195 : Nat := 4983230072969 + 3 ^ 40 * 197195 * 2
def baseEnd_197195 : Nat := 60003447504273308062591

theorem tailTrace_197195 : CollatzResearch.WordTrace tailWord_197195 prefixEnd_197195 60003447504273308062591 := by
  unfold tailWord_197195
  simp only [CollatzResearch.WordTrace]
  refine ⟨7192292520603668069849039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4794861680402445379899359 7192292520603668069849039)
  ·
    refine ⟨10788438780905502104773559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7192292520603668069849039 10788438780905502104773559)
    ·
      refine ⟨16182658171358253157160339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10788438780905502104773559 16182658171358253157160339)
      ·
        refine ⟨24273987257037379735740509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16182658171358253157160339 24273987257037379735740509)
        ·
          refine ⟨9102745221389017400902691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24273987257037379735740509 9102745221389017400902691)
          ·
            refine ⟨13654117832083526101354037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9102745221389017400902691 13654117832083526101354037)
            ·
              refine ⟨1280073546757830572001941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 13654117832083526101354037 1280073546757830572001941)
              ·
                refine ⟨60003447504273308062591, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1280073546757830572001941 60003447504273308062591)
                ·
                  rfl

theorem cell19_197195_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 5, 6].length) (baseStart_197195 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_197195 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_197195 prefixEnd_197195 := by exact prefixLift 197195
  have htrace : WordTrace (prefixWord ++ tailWord_197195) baseStart_197195 baseEnd_197195 := by
    simpa [prefixWord, tailWord_197195, baseEnd_197195] using wordTrace_append hprefix tailTrace_197195
  have hstable : (prefixWord ++ tailWord_197195).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_197195).length < 2 ^ (prefixWord ++ tailWord_197195).sum := by decide
  have hdescent : baseEnd_197195 < baseStart_197195 := by decide
  rcases family_descends (prefixWord ++ tailWord_197195) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_197318 : List Nat := [6, 1, 2, 1, 2, 2, 2, 3]
def baseStart_197318 : Nat := 118140960795 + 197318 * 2 ^ 59
def prefixEnd_197318 : Nat := 4983230072969 + 3 ^ 40 * 197318 * 2
def baseEnd_197318 : Nat := 60040874538645467328923

theorem tailTrace_197318 : CollatzResearch.WordTrace tailWord_197318 prefixEnd_197318 60040874538645467328923 := by
  unfold tailWord_197318
  simp only [CollatzResearch.WordTrace]
  refine ⟨224899334348689377393019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 4797852466105373384384405 224899334348689377393019)
  ·
    refine ⟨337349001523034066089529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 224899334348689377393019 337349001523034066089529)
    ·
      refine ⟨253011751142275549567147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 337349001523034066089529 253011751142275549567147)
      ·
        refine ⟨379517626713413324350721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 253011751142275549567147 379517626713413324350721)
        ·
          refine ⟨284638220035059993263041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 379517626713413324350721 284638220035059993263041)
          ·
            refine ⟨213478665026294994947281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 284638220035059993263041 213478665026294994947281)
            ·
              refine ⟨160108998769721246210461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 213478665026294994947281 160108998769721246210461)
              ·
                refine ⟨60040874538645467328923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 160108998769721246210461 60040874538645467328923)
                ·
                  rfl

theorem cell19_197318_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 2, 2, 2, 3].length) (baseStart_197318 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_197318 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_197318 prefixEnd_197318 := by exact prefixLift 197318
  have htrace : WordTrace (prefixWord ++ tailWord_197318) baseStart_197318 baseEnd_197318 := by
    simpa [prefixWord, tailWord_197318, baseEnd_197318] using wordTrace_append hprefix tailTrace_197318
  have hstable : (prefixWord ++ tailWord_197318).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_197318).length < 2 ^ (prefixWord ++ tailWord_197318).sum := by decide
  have hdescent : baseEnd_197318 < baseStart_197318 := by decide
  rcases family_descends (prefixWord ++ tailWord_197318) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_197324 : List Nat := [2, 2, 1, 5, 1, 1, 4, 3]
def baseStart_197324 : Nat := 118140960795 + 197324 * 2 ^ 59
def prefixEnd_197324 : Nat := 4983230072969 + 3 ^ 40 * 197324 * 2
def baseEnd_197324 : Nat := 60042700247639231195573

theorem tailTrace_197324 : CollatzResearch.WordTrace tailWord_197324 prefixEnd_197324 60042700247639231195573 := by
  unfold tailWord_197324
  simp only [CollatzResearch.WordTrace]
  refine ⟨3598498768568161550647513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4797998358090882067530017 3598498768568161550647513)
  ·
    refine ⟨2698874076426121162985635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3598498768568161550647513 2698874076426121162985635)
    ·
      refine ⟨4048311114639181744478453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2698874076426121162985635 4048311114639181744478453)
      ·
        refine ⟨379529166997423288544855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 4048311114639181744478453 379529166997423288544855)
        ·
          refine ⟨569293750496134932817283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 379529166997423288544855 569293750496134932817283)
          ·
            refine ⟨853940625744202399225925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 569293750496134932817283 853940625744202399225925)
            ·
              refine ⟨160113867327037949854861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 853940625744202399225925 160113867327037949854861)
              ·
                refine ⟨60042700247639231195573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 160113867327037949854861 60042700247639231195573)
                ·
                  rfl

theorem cell19_197324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 4, 3].length) (baseStart_197324 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_197324 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_197324 prefixEnd_197324 := by exact prefixLift 197324
  have htrace : WordTrace (prefixWord ++ tailWord_197324) baseStart_197324 baseEnd_197324 := by
    simpa [prefixWord, tailWord_197324, baseEnd_197324] using wordTrace_append hprefix tailTrace_197324
  have hstable : (prefixWord ++ tailWord_197324).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_197324).length < 2 ^ (prefixWord ++ tailWord_197324).sum := by decide
  have hdescent : baseEnd_197324 < baseStart_197324 := by decide
  rcases family_descends (prefixWord ++ tailWord_197324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_197326 : List Nat := [4, 1, 1, 1, 3, 3, 1, 5]
def baseStart_197326 : Nat := 118140960795 + 197326 * 2 ^ 59
def prefixEnd_197326 : Nat := 4983230072969 + 3 ^ 40 * 197326 * 2
def baseEnd_197326 : Nat := 60043308817303819151123

theorem tailTrace_197326 : CollatzResearch.WordTrace tailWord_197326 prefixEnd_197326 60043308817303819151123 := by
  unfold tailWord_197326
  simp only [CollatzResearch.WordTrace]
  refine ⟨899633810391134680358479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 4798046988752718295245221 899633810391134680358479)
  ·
    refine ⟨1349450715586702020537719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 899633810391134680358479 1349450715586702020537719)
    ·
      refine ⟨2024176073380053030806579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1349450715586702020537719 2024176073380053030806579)
      ·
        refine ⟨3036264110070079546209869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2024176073380053030806579 3036264110070079546209869)
        ·
          refine ⟨1138599041276279829828701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3036264110070079546209869 1138599041276279829828701)
          ·
            refine ⟨426974640478604936185763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1138599041276279829828701 426974640478604936185763)
            ·
              refine ⟨640461960717907404278645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 426974640478604936185763 640461960717907404278645)
              ·
                refine ⟨60043308817303819151123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 640461960717907404278645 60043308817303819151123)
                ·
                  rfl

theorem cell19_197326_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 3, 1, 5].length) (baseStart_197326 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_197326 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_197326 prefixEnd_197326 := by exact prefixLift 197326
  have htrace : WordTrace (prefixWord ++ tailWord_197326) baseStart_197326 baseEnd_197326 := by
    simpa [prefixWord, tailWord_197326, baseEnd_197326] using wordTrace_append hprefix tailTrace_197326
  have hstable : (prefixWord ++ tailWord_197326).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_197326).length < 2 ^ (prefixWord ++ tailWord_197326).sum := by decide
  have hdescent : baseEnd_197326 < baseStart_197326 := by decide
  rcases family_descends (prefixWord ++ tailWord_197326) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_197345 : List Nat := [1, 2, 3, 1, 4, 3, 5]
def baseStart_197345 : Nat := 118140960795 + 197345 * 2 ^ 59
def prefixEnd_197345 : Nat := 4983230072969 + 3 ^ 40 * 197345 * 2
def baseEnd_197345 : Nat := 20016363409705801576283

theorem tailTrace_197345 : CollatzResearch.WordTrace tailWord_197345 prefixEnd_197345 20016363409705801576283 := by
  unfold tailWord_197345
  simp only [CollatzResearch.WordTrace]
  refine ⟨7197763470060243687809489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4798508980040162458539659 7197763470060243687809489)
  ·
    refine ⟨5398322602545182765857117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7197763470060243687809489 5398322602545182765857117)
    ·
      refine ⟨2024370975954443537196419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5398322602545182765857117 2024370975954443537196419)
      ·
        refine ⟨3036556463931665305794629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2024370975954443537196419 3036556463931665305794629)
        ·
          refine ⟨569354336987187244836493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3036556463931665305794629 569354336987187244836493)
          ·
            refine ⟨213507876370195216813685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 569354336987187244836493 213507876370195216813685)
            ·
              refine ⟨20016363409705801576283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 213507876370195216813685 20016363409705801576283)
              ·
                rfl

theorem cell19_197345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 3, 5].length) (baseStart_197345 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_197345 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_197345 prefixEnd_197345 := by exact prefixLift 197345
  have htrace : WordTrace (prefixWord ++ tailWord_197345) baseStart_197345 baseEnd_197345 := by
    simpa [prefixWord, tailWord_197345, baseEnd_197345] using wordTrace_append hprefix tailTrace_197345
  have hstable : (prefixWord ++ tailWord_197345).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_197345).length < 2 ^ (prefixWord ++ tailWord_197345).sum := by decide
  have hdescent : baseEnd_197345 < baseStart_197345 := by decide
  rcases family_descends (prefixWord ++ tailWord_197345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_197383 : List Nat := [1, 1, 4, 4, 1, 1, 2, 5]
def baseStart_197383 : Nat := 118140960795 + 197383 * 2 ^ 59
def prefixEnd_197383 : Nat := 4983230072969 + 3 ^ 40 * 197383 * 2
def baseEnd_197383 : Nat := 60060653052744575884301

theorem tailTrace_197383 : CollatzResearch.WordTrace tailWord_197383 prefixEnd_197383 60060653052744575884301 := by
  unfold tailWord_197383
  simp only [CollatzResearch.WordTrace]
  refine ⟨7199149443922576177692803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4799432962615050785128535 7199149443922576177692803)
  ·
    refine ⟨10798724165883864266539205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7199149443922576177692803 10798724165883864266539205)
    ·
      refine ⟨2024760781103224549976101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10798724165883864266539205 2024760781103224549976101)
      ·
        refine ⟨379642646456854603120519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2024760781103224549976101 379642646456854603120519)
        ·
          refine ⟨569463969685281904680779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 379642646456854603120519 569463969685281904680779)
          ·
            refine ⟨854195954527922857021169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 569463969685281904680779 854195954527922857021169)
            ·
              refine ⟨640646965895942142765877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 854195954527922857021169 640646965895942142765877)
              ·
                refine ⟨60060653052744575884301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 640646965895942142765877 60060653052744575884301)
                ·
                  rfl

theorem cell19_197383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 2, 5].length) (baseStart_197383 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_197383 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_197383 prefixEnd_197383 := by exact prefixLift 197383
  have htrace : WordTrace (prefixWord ++ tailWord_197383) baseStart_197383 baseEnd_197383 := by
    simpa [prefixWord, tailWord_197383, baseEnd_197383] using wordTrace_append hprefix tailTrace_197383
  have hstable : (prefixWord ++ tailWord_197383).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_197383).length < 2 ^ (prefixWord ++ tailWord_197383).sum := by decide
  have hdescent : baseEnd_197383 < baseStart_197383 := by decide
  rcases family_descends (prefixWord ++ tailWord_197383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_197385 : List Nat := [1, 2, 1, 1, 3, 2, 4, 5]
def baseStart_197385 : Nat := 118140960795 + 197385 * 2 ^ 59
def prefixEnd_197385 : Nat := 4983230072969 + 3 ^ 40 * 197385 * 2
def baseEnd_197385 : Nat := 60061261622409163839851

theorem tailTrace_197385 : CollatzResearch.WordTrace tailWord_197385 prefixEnd_197385 60061261622409163839851 := by
  unfold tailWord_197385
  simp only [CollatzResearch.WordTrace]
  refine ⟨7199222389915330519265609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4799481593276887012843739 7199222389915330519265609)
  ·
    refine ⟨5399416792436497889449207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7199222389915330519265609 5399416792436497889449207)
    ·
      refine ⟨8099125188654746834173811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5399416792436497889449207 8099125188654746834173811)
      ·
        refine ⟨12148687782982120251260717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8099125188654746834173811 12148687782982120251260717)
        ·
          refine ⟨4555757918618295094222769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12148687782982120251260717 4555757918618295094222769)
          ·
            refine ⟨3416818438963721320667077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4555757918618295094222769 3416818438963721320667077)
            ·
              refine ⟨640653457305697747625077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3416818438963721320667077 640653457305697747625077)
              ·
                refine ⟨60061261622409163839851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 640653457305697747625077 60061261622409163839851)
                ·
                  rfl

theorem cell19_197385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 4, 5].length) (baseStart_197385 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_197385 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_197385 prefixEnd_197385 := by exact prefixLift 197385
  have htrace : WordTrace (prefixWord ++ tailWord_197385) baseStart_197385 baseEnd_197385 := by
    simpa [prefixWord, tailWord_197385, baseEnd_197385] using wordTrace_append hprefix tailTrace_197385
  have hstable : (prefixWord ++ tailWord_197385).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_197385).length < 2 ^ (prefixWord ++ tailWord_197385).sum := by decide
  have hdescent : baseEnd_197385 < baseStart_197385 := by decide
  rcases family_descends (prefixWord ++ tailWord_197385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_197404 : List Nat := [2, 2, 3, 1, 1, 10]
def baseStart_197404 : Nat := 118140960795 + 197404 * 2 ^ 59
def prefixEnd_197404 : Nat := 4983230072969 + 3 ^ 40 * 197404 * 2
def baseEnd_197404 : Nat := 6674115892691416601953

theorem tailTrace_197404 : CollatzResearch.WordTrace tailWord_197404 prefixEnd_197404 6674115892691416601953 := by
  unfold tailWord_197404
  simp only [CollatzResearch.WordTrace]
  refine ⟨3599957688423248382103633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4799943584564331176138177 3599957688423248382103633)
  ·
    refine ⟨2699968266317436286577725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3599957688423248382103633 2699968266317436286577725)
    ·
      refine ⟨1012488099869038607466647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2699968266317436286577725 1012488099869038607466647)
      ·
        refine ⟨1518732149803557911199971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1012488099869038607466647 1518732149803557911199971)
        ·
          refine ⟨2278098224705336866799957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1518732149803557911199971 2278098224705336866799957)
          ·
            refine ⟨6674115892691416601953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 2278098224705336866799957 6674115892691416601953)
            ·
              rfl

theorem cell19_197404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 10].length) (baseStart_197404 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_197404 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_197404 prefixEnd_197404 := by exact prefixLift 197404
  have htrace : WordTrace (prefixWord ++ tailWord_197404) baseStart_197404 baseEnd_197404 := by
    simpa [prefixWord, tailWord_197404, baseEnd_197404] using wordTrace_append hprefix tailTrace_197404
  have hstable : (prefixWord ++ tailWord_197404).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_197404).length < 2 ^ (prefixWord ++ tailWord_197404).sum := by decide
  have hdescent : baseEnd_197404 < baseStart_197404 := by decide
  rcases family_descends (prefixWord ++ tailWord_197404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_197461 : List Nat := [1, 3, 2, 2, 2, 1, 8]
def baseStart_197461 : Nat := 118140960795 + 197461 * 2 ^ 59
def prefixEnd_197461 : Nat := 4983230072969 + 3 ^ 40 * 197461 * 2
def baseEnd_197461 : Nat := 20028129089887835383585

theorem tailTrace_197461 : CollatzResearch.WordTrace tailWord_197461 prefixEnd_197461 20028129089887835383585 := by
  unfold tailWord_197461
  simp only [CollatzResearch.WordTrace]
  refine ⟨7201994337639995499032237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4801329558426663666021491 7201994337639995499032237)
  ·
    refine ⟨2700747876614998312137089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7201994337639995499032237 2700747876614998312137089)
    ·
      refine ⟨2025560907461248734102817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2700747876614998312137089 2025560907461248734102817)
      ·
        refine ⟨1519170680595936550577113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2025560907461248734102817 1519170680595936550577113)
        ·
          refine ⟨1139378010446952412932835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1519170680595936550577113 1139378010446952412932835)
          ·
            refine ⟨1709067015670428619399253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1139378010446952412932835 1709067015670428619399253)
            ·
              refine ⟨20028129089887835383585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1709067015670428619399253 20028129089887835383585)
              ·
                rfl

theorem cell19_197461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 8].length) (baseStart_197461 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_197461 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_197461 prefixEnd_197461 := by exact prefixLift 197461
  have htrace : WordTrace (prefixWord ++ tailWord_197461) baseStart_197461 baseEnd_197461 := by
    simpa [prefixWord, tailWord_197461, baseEnd_197461] using wordTrace_append hprefix tailTrace_197461
  have hstable : (prefixWord ++ tailWord_197461).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_197461).length < 2 ^ (prefixWord ++ tailWord_197461).sum := by decide
  have hdescent : baseEnd_197461 < baseStart_197461 := by decide
  rcases family_descends (prefixWord ++ tailWord_197461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_197497 : List Nat := [1, 2, 1, 3, 2, 3, 4, 3]
def baseStart_197497 : Nat := 118140960795 + 197497 * 2 ^ 59
def prefixEnd_197497 : Nat := 4983230072969 + 3 ^ 40 * 197497 * 2
def baseEnd_197497 : Nat := 60095341523626089350657

theorem tailTrace_197497 : CollatzResearch.WordTrace tailWord_197497 prefixEnd_197497 60095341523626089350657 := by
  unfold tailWord_197497
  simp only [CollatzResearch.WordTrace]
  refine ⟨7203307365509573647342745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4802204910339715764895163 7203307365509573647342745)
  ·
    refine ⟨5402480524132180235507059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7203307365509573647342745 5402480524132180235507059)
    ·
      refine ⟨8103720786198270353260589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5402480524132180235507059 8103720786198270353260589)
      ·
        refine ⟨3038895294824351382472721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8103720786198270353260589 3038895294824351382472721)
        ·
          refine ⟨2279171471118263536854541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3038895294824351382472721 2279171471118263536854541)
          ·
            refine ⟨854689301669348826320453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2279171471118263536854541 854689301669348826320453)
            ·
              refine ⟨160254244063002904935085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 854689301669348826320453 160254244063002904935085)
              ·
                refine ⟨60095341523626089350657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 160254244063002904935085 60095341523626089350657)
                ·
                  rfl

theorem cell19_197497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 4, 3].length) (baseStart_197497 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_197497 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_197497 prefixEnd_197497 := by exact prefixLift 197497
  have htrace : WordTrace (prefixWord ++ tailWord_197497) baseStart_197497 baseEnd_197497 := by
    simpa [prefixWord, tailWord_197497, baseEnd_197497] using wordTrace_append hprefix tailTrace_197497
  have hstable : (prefixWord ++ tailWord_197497).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_197497).length < 2 ^ (prefixWord ++ tailWord_197497).sum := by decide
  have hdescent : baseEnd_197497 < baseStart_197497 := by decide
  rcases family_descends (prefixWord ++ tailWord_197497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_197535 : List Nat := [1, 1, 2, 5, 2, 2, 2, 4]
def baseStart_197535 : Nat := 118140960795 + 197535 * 2 ^ 59
def prefixEnd_197535 : Nat := 4983230072969 + 3 ^ 40 * 197535 * 2
def baseEnd_197535 : Nat := 60106904347253260506109

theorem tailTrace_197535 : CollatzResearch.WordTrace tailWord_197535 prefixEnd_197535 60106904347253260506109 := by
  unfold tailWord_197535
  simp only [CollatzResearch.WordTrace]
  refine ⟨7204693339371906137226059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4803128892914604091484039 7204693339371906137226059)
  ·
    refine ⟨10807040009057859205839089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7204693339371906137226059 10807040009057859205839089)
    ·
      refine ⟨8105280006793394404379317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10807040009057859205839089 8105280006793394404379317)
      ·
        refine ⟨759870000636880725410561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 8105280006793394404379317 759870000636880725410561)
        ·
          refine ⟨569902500477660544057921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 759870000636880725410561 569902500477660544057921)
          ·
            refine ⟨427426875358245408043441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 569902500477660544057921 427426875358245408043441)
            ·
              refine ⟨320570156518684056032581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 427426875358245408043441 320570156518684056032581)
              ·
                refine ⟨60106904347253260506109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 320570156518684056032581 60106904347253260506109)
                ·
                  rfl

theorem cell19_197535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 2, 2, 4].length) (baseStart_197535 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_197535 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_197535 prefixEnd_197535 := by exact prefixLift 197535
  have htrace : WordTrace (prefixWord ++ tailWord_197535) baseStart_197535 baseEnd_197535 := by
    simpa [prefixWord, tailWord_197535, baseEnd_197535] using wordTrace_append hprefix tailTrace_197535
  have hstable : (prefixWord ++ tailWord_197535).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_197535).length < 2 ^ (prefixWord ++ tailWord_197535).sum := by decide
  have hdescent : baseEnd_197535 < baseStart_197535 := by decide
  rcases family_descends (prefixWord ++ tailWord_197535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_197590 : List Nat := [5, 2, 1, 1, 2, 1, 3, 4]
def baseStart_197590 : Nat := 118140960795 + 197590 * 2 ^ 59
def prefixEnd_197590 : Nat := 4983230072969 + 3 ^ 40 * 197590 * 2
def baseEnd_197590 : Nat := 60123640013029429283737

theorem tailTrace_197590 : CollatzResearch.WordTrace tailWord_197590 prefixEnd_197590 60123640013029429283737 := by
  unfold tailWord_197590
  simp only [CollatzResearch.WordTrace]
  refine ⟨450418709635790658154889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 4804466236115100353652149 450418709635790658154889)
  ·
    refine ⟨337814032226842993616167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 450418709635790658154889 337814032226842993616167)
    ·
      refine ⟨506721048340264490424251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 337814032226842993616167 506721048340264490424251)
      ·
        refine ⟨760081572510396735636377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 506721048340264490424251 760081572510396735636377)
        ·
          refine ⟨570061179382797551727283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 760081572510396735636377 570061179382797551727283)
          ·
            refine ⟨855091769074196327590925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 570061179382797551727283 855091769074196327590925)
            ·
              refine ⟨320659413402823622846597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 855091769074196327590925 320659413402823622846597)
              ·
                refine ⟨60123640013029429283737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 320659413402823622846597 60123640013029429283737)
                ·
                  rfl

theorem cell19_197590_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 3, 4].length) (baseStart_197590 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_197590 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_197590 prefixEnd_197590 := by exact prefixLift 197590
  have htrace : WordTrace (prefixWord ++ tailWord_197590) baseStart_197590 baseEnd_197590 := by
    simpa [prefixWord, tailWord_197590, baseEnd_197590] using wordTrace_append hprefix tailTrace_197590
  have hstable : (prefixWord ++ tailWord_197590).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_197590).length < 2 ^ (prefixWord ++ tailWord_197590).sum := by decide
  have hdescent : baseEnd_197590 < baseStart_197590 := by decide
  rcases family_descends (prefixWord ++ tailWord_197590) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_197592 : List Nat := [2, 1, 2, 2, 2, 5, 1, 4]
def baseStart_197592 : Nat := 118140960795 + 197592 * 2 ^ 59
def prefixEnd_197592 : Nat := 4983230072969 + 3 ^ 40 * 197592 * 2
def baseEnd_197592 : Nat := 60124248582694017239287

theorem tailTrace_197592 : CollatzResearch.WordTrace tailWord_197592 prefixEnd_197592 60124248582694017239287 := by
  unfold tailWord_197592
  simp only [CollatzResearch.WordTrace]
  refine ⟨3603386150082702436025515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4804514866776936581367353 3603386150082702436025515)
  ·
    refine ⟨5405079225124053654038273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3603386150082702436025515 5405079225124053654038273)
    ·
      refine ⟨4053809418843040240528705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5405079225124053654038273 4053809418843040240528705)
      ·
        refine ⟨3040357064132280180396529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4053809418843040240528705 3040357064132280180396529)
        ·
          refine ⟨2280267798099210135297397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3040357064132280180396529 2280267798099210135297397)
          ·
            refine ⟨213775106071800950184131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 2280267798099210135297397 213775106071800950184131)
            ·
              refine ⟨320662659107701425276197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 213775106071800950184131 320662659107701425276197)
              ·
                refine ⟨60124248582694017239287, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 320662659107701425276197 60124248582694017239287)
                ·
                  rfl

theorem cell19_197592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 5, 1, 4].length) (baseStart_197592 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_197592 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_197592 prefixEnd_197592 := by exact prefixLift 197592
  have htrace : WordTrace (prefixWord ++ tailWord_197592) baseStart_197592 baseEnd_197592 := by
    simpa [prefixWord, tailWord_197592, baseEnd_197592] using wordTrace_append hprefix tailTrace_197592
  have hstable : (prefixWord ++ tailWord_197592).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_197592).length < 2 ^ (prefixWord ++ tailWord_197592).sum := by decide
  have hdescent : baseEnd_197592 < baseStart_197592 := by decide
  rcases family_descends (prefixWord ++ tailWord_197592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_197664 : List Nat := [2, 1, 1, 7, 1, 2, 2, 3]
def baseStart_197664 : Nat := 118140960795 + 197664 * 2 ^ 59
def prefixEnd_197664 : Nat := 4983230072969 + 3 ^ 40 * 197664 * 2
def baseEnd_197664 : Nat := 60146157090619183639091

theorem tailTrace_197664 : CollatzResearch.WordTrace tailWord_197664 prefixEnd_197664 60146157090619183639091 := by
  unfold tailWord_197664
  simp only [CollatzResearch.WordTrace]
  refine ⟨3604699177952280584336023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4806265570603040779114697 3604699177952280584336023)
  ·
    refine ⟨5407048766928420876504035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3604699177952280584336023 5407048766928420876504035)
    ·
      refine ⟨8110573150392631314756053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5407048766928420876504035 8110573150392631314756053)
      ·
        refine ⟨190091558212327296439595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 8110573150392631314756053 190091558212327296439595)
        ·
          refine ⟨285137337318490944659393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 190091558212327296439595 285137337318490944659393)
          ·
            refine ⟨213853002988868208494545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 285137337318490944659393 213853002988868208494545)
            ·
              refine ⟨160389752241651156370909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 213853002988868208494545 160389752241651156370909)
              ·
                refine ⟨60146157090619183639091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 160389752241651156370909 60146157090619183639091)
                ·
                  rfl

theorem cell19_197664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 1, 2, 2, 3].length) (baseStart_197664 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_197664 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_197664 prefixEnd_197664 := by exact prefixLift 197664
  have htrace : WordTrace (prefixWord ++ tailWord_197664) baseStart_197664 baseEnd_197664 := by
    simpa [prefixWord, tailWord_197664, baseEnd_197664] using wordTrace_append hprefix tailTrace_197664
  have hstable : (prefixWord ++ tailWord_197664).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_197664).length < 2 ^ (prefixWord ++ tailWord_197664).sum := by decide
  have hdescent : baseEnd_197664 < baseStart_197664 := by decide
  rcases family_descends (prefixWord ++ tailWord_197664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_197666 : List Nat := [3, 3, 1, 1, 1, 5, 2, 3]
def baseStart_197666 : Nat := 118140960795 + 197666 * 2 ^ 59
def prefixEnd_197666 : Nat := 4983230072969 + 3 ^ 40 * 197666 * 2
def baseEnd_197666 : Nat := 60146765660283771594641

theorem tailTrace_197666 : CollatzResearch.WordTrace tailWord_197666 prefixEnd_197666 60146765660283771594641 := by
  unfold tailWord_197666
  simp only [CollatzResearch.WordTrace]
  refine ⟨1802367825474328877561213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4806314201264877006829901 1802367825474328877561213)
  ·
    refine ⟨675887934552873329085455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1802367825474328877561213 675887934552873329085455)
    ·
      refine ⟨1013831901829309993628183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 675887934552873329085455 1013831901829309993628183)
      ·
        refine ⟨1520747852743964990442275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1013831901829309993628183 1520747852743964990442275)
        ·
          refine ⟨2281121779115947485663413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1520747852743964990442275 2281121779115947485663413)
          ·
            refine ⟨213855166792120076780945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 2281121779115947485663413 213855166792120076780945)
            ·
              refine ⟨160391375094090057585709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 213855166792120076780945 160391375094090057585709)
              ·
                refine ⟨60146765660283771594641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 160391375094090057585709 60146765660283771594641)
                ·
                  rfl

theorem cell19_197666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 5, 2, 3].length) (baseStart_197666 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_197666 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_197666 prefixEnd_197666 := by exact prefixLift 197666
  have htrace : WordTrace (prefixWord ++ tailWord_197666) baseStart_197666 baseEnd_197666 := by
    simpa [prefixWord, tailWord_197666, baseEnd_197666] using wordTrace_append hprefix tailTrace_197666
  have hstable : (prefixWord ++ tailWord_197666).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_197666).length < 2 ^ (prefixWord ++ tailWord_197666).sum := by decide
  have hdescent : baseEnd_197666 < baseStart_197666 := by decide
  rcases family_descends (prefixWord ++ tailWord_197666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_197668 : List Nat := [2, 3, 1, 4, 1, 2, 1, 5]
def baseStart_197668 : Nat := 118140960795 + 197668 * 2 ^ 59
def prefixEnd_197668 : Nat := 4983230072969 + 3 ^ 40 * 197668 * 2
def baseEnd_197668 : Nat := 60147374229948359550191

theorem tailTrace_197668 : CollatzResearch.WordTrace tailWord_197668 prefixEnd_197668 60147374229948359550191 := by
  unfold tailWord_197668
  simp only [CollatzResearch.WordTrace]
  refine ⟨3604772123945034925908829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4806362831926713234545105 3604772123945034925908829)
  ·
    refine ⟨1351789546479388097215811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3604772123945034925908829 1351789546479388097215811)
    ·
      refine ⟨2027684319719082145823717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1351789546479388097215811 2027684319719082145823717)
      ·
        refine ⟨380190809947327902341947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2027684319719082145823717 380190809947327902341947)
        ·
          refine ⟨570286214920991853512921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 380190809947327902341947 570286214920991853512921)
          ·
            refine ⟨427714661190743890134691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 570286214920991853512921 427714661190743890134691)
            ·
              refine ⟨641571991786115835202037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 427714661190743890134691 641571991786115835202037)
              ·
                refine ⟨60147374229948359550191, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 641571991786115835202037 60147374229948359550191)
                ·
                  rfl

theorem cell19_197668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 2, 1, 5].length) (baseStart_197668 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_197668 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_197668 prefixEnd_197668 := by exact prefixLift 197668
  have htrace : WordTrace (prefixWord ++ tailWord_197668) baseStart_197668 baseEnd_197668 := by
    simpa [prefixWord, tailWord_197668, baseEnd_197668] using wordTrace_append hprefix tailTrace_197668
  have hstable : (prefixWord ++ tailWord_197668).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_197668).length < 2 ^ (prefixWord ++ tailWord_197668).sum := by decide
  have hdescent : baseEnd_197668 < baseStart_197668 := by decide
  rcases family_descends (prefixWord ++ tailWord_197668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_197689 : List Nat := [1, 2, 1, 5, 2, 1, 7]
def baseStart_197689 : Nat := 118140960795 + 197689 * 2 ^ 59
def prefixEnd_197689 : Nat := 4983230072969 + 3 ^ 40 * 197689 * 2
def baseEnd_197689 : Nat := 20051254737142177694489

theorem tailTrace_197689 : CollatzResearch.WordTrace tailWord_197689 prefixEnd_197689 20051254737142177694489 := by
  unfold tailWord_197689
  simp only [CollatzResearch.WordTrace]
  refine ⟨7210310180813990438332121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4806873453875993625554747 7210310180813990438332121)
  ·
    refine ⟨5407732635610492828749091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7210310180813990438332121 5407732635610492828749091)
    ·
      refine ⟨8111598953415739243123637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5407732635610492828749091 8111598953415739243123637)
      ·
        refine ⟨760462401882725554042841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 8111598953415739243123637 760462401882725554042841)
        ·
          refine ⟨570346801412044165532131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 760462401882725554042841 570346801412044165532131)
          ·
            refine ⟨855520202118066248298197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 570346801412044165532131 855520202118066248298197)
            ·
              refine ⟨20051254737142177694489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 855520202118066248298197 20051254737142177694489)
              ·
                rfl

theorem cell19_197689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 7].length) (baseStart_197689 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_197689 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_197689 prefixEnd_197689 := by exact prefixLift 197689
  have htrace : WordTrace (prefixWord ++ tailWord_197689) baseStart_197689 baseEnd_197689 := by
    simpa [prefixWord, tailWord_197689, baseEnd_197689] using wordTrace_append hprefix tailTrace_197689
  have hstable : (prefixWord ++ tailWord_197689).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_197689).length < 2 ^ (prefixWord ++ tailWord_197689).sum := by decide
  have hdescent : baseEnd_197689 < baseStart_197689 := by decide
  rcases family_descends (prefixWord ++ tailWord_197689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_197843 : List Nat := [1, 1, 1, 2, 1, 1, 1, 11]
def baseStart_197843 : Nat := 118140960795 + 197843 * 2 ^ 59
def prefixEnd_197843 : Nat := 4983230072969 + 3 ^ 40 * 197843 * 2
def baseEnd_197843 : Nat := 60200624075599805660825

theorem tailTrace_197843 : CollatzResearch.WordTrace tailWord_197843 prefixEnd_197843 60200624075599805660825 := by
  unfold tailWord_197843
  simp only [CollatzResearch.WordTrace]
  refine ⟨7215927022256074739438183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4810618014837383159625455 7215927022256074739438183)
  ·
    refine ⟨10823890533384112109157275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7215927022256074739438183 10823890533384112109157275)
    ·
      refine ⟨16235835800076168163735913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10823890533384112109157275 16235835800076168163735913)
      ·
        refine ⟨12176876850057126122801935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16235835800076168163735913 12176876850057126122801935)
        ·
          refine ⟨18265315275085689184202903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12176876850057126122801935 18265315275085689184202903)
          ·
            refine ⟨27397972912628533776304355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18265315275085689184202903 27397972912628533776304355)
            ·
              refine ⟨41096959368942800664456533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27397972912628533776304355 41096959368942800664456533)
              ·
                refine ⟨60200624075599805660825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 41096959368942800664456533 60200624075599805660825)
                ·
                  rfl

theorem cell19_197843_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 11].length) (baseStart_197843 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_197843 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_197843 prefixEnd_197843 := by exact prefixLift 197843
  have htrace : WordTrace (prefixWord ++ tailWord_197843) baseStart_197843 baseEnd_197843 := by
    simpa [prefixWord, tailWord_197843, baseEnd_197843] using wordTrace_append hprefix tailTrace_197843
  have hstable : (prefixWord ++ tailWord_197843).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_197843).length < 2 ^ (prefixWord ++ tailWord_197843).sum := by decide
  have hdescent : baseEnd_197843 < baseStart_197843 := by decide
  rcases family_descends (prefixWord ++ tailWord_197843) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_197917 : List Nat := [1, 4, 2, 3, 1, 8]
def baseStart_197917 : Nat := 118140960795 + 197917 * 2 ^ 59
def prefixEnd_197917 : Nat := 4983230072969 + 3 ^ 40 * 197917 * 2
def baseEnd_197917 : Nat := 6691460128132173335131

theorem tailTrace_197917 : CollatzResearch.WordTrace tailWord_197917 prefixEnd_197917 6691460128132173335131 := by
  unfold tailWord_197917
  simp only [CollatzResearch.WordTrace]
  refine ⟨7218626023987985377632005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4812417349325323585088003 7218626023987985377632005)
  ·
    refine ⟨1353492379497747258306001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7218626023987985377632005 1353492379497747258306001)
    ·
      refine ⟨1015119284623310443729501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1353492379497747258306001 1015119284623310443729501)
      ·
        refine ⟨380669731733741416398563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1015119284623310443729501 380669731733741416398563)
        ·
          refine ⟨571004597600612124597845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 380669731733741416398563 571004597600612124597845)
          ·
            refine ⟨6691460128132173335131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 571004597600612124597845 6691460128132173335131)
            ·
              rfl

theorem cell19_197917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 8].length) (baseStart_197917 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_197917 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_197917 prefixEnd_197917 := by exact prefixLift 197917
  have htrace : WordTrace (prefixWord ++ tailWord_197917) baseStart_197917 baseEnd_197917 := by
    simpa [prefixWord, tailWord_197917, baseEnd_197917] using wordTrace_append hprefix tailTrace_197917
  have hstable : (prefixWord ++ tailWord_197917).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_197917).length < 2 ^ (prefixWord ++ tailWord_197917).sum := by decide
  have hdescent : baseEnd_197917 < baseStart_197917 := by decide
  rcases family_descends (prefixWord ++ tailWord_197917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_197919 : List Nat := [1, 1, 2, 4, 11]
def baseStart_197919 : Nat := 118140960795 + 197919 * 2 ^ 59
def prefixEnd_197919 : Nat := 4983230072969 + 3 ^ 40 * 197919 * 2
def baseEnd_197919 : Nat := 2230509248994598073027

theorem tailTrace_197919 : CollatzResearch.WordTrace tailWord_197919 prefixEnd_197919 2230509248994598073027 := by
  unfold tailWord_197919
  simp only [CollatzResearch.WordTrace]
  refine ⟨7218698969980739719204811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4812465979987159812803207 7218698969980739719204811)
  ·
    refine ⟨10828048454971109578807217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7218698969980739719204811 10828048454971109578807217)
    ·
      refine ⟨8121036341228332184105413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10828048454971109578807217 8121036341228332184105413)
      ·
        refine ⟨1522694313980312284519765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8121036341228332184105413 1522694313980312284519765)
        ·
          refine ⟨2230509248994598073027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 11 1522694313980312284519765 2230509248994598073027)
          ·
            rfl

theorem cell19_197919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 11].length) (baseStart_197919 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_197919 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_197919 prefixEnd_197919 := by exact prefixLift 197919
  have htrace : WordTrace (prefixWord ++ tailWord_197919) baseStart_197919 baseEnd_197919 := by
    simpa [prefixWord, tailWord_197919, baseEnd_197919] using wordTrace_append hprefix tailTrace_197919
  have hstable : (prefixWord ++ tailWord_197919).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_197919).length < 2 ^ (prefixWord ++ tailWord_197919).sum := by decide
  have hdescent : baseEnd_197919 < baseStart_197919 := by decide
  rcases family_descends (prefixWord ++ tailWord_197919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_197957 : List Nat := [1, 3, 1, 1, 1, 2, 1, 9]
def baseStart_197957 : Nat := 118140960795 + 197957 * 2 ^ 59
def prefixEnd_197957 : Nat := 4983230072969 + 3 ^ 40 * 197957 * 2
def baseEnd_197957 : Nat := 60235312546481319127181

theorem tailTrace_197957 : CollatzResearch.WordTrace tailWord_197957 prefixEnd_197957 60235312546481319127181 := by
  unfold tailWord_197957
  simp only [CollatzResearch.WordTrace]
  refine ⟨7220084943843072209088125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4813389962562048139392083 7220084943843072209088125)
  ·
    refine ⟨2707531853941152078408047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7220084943843072209088125 2707531853941152078408047)
    ·
      refine ⟨4061297780911728117612071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2707531853941152078408047 4061297780911728117612071)
      ·
        refine ⟨6091946671367592176418107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4061297780911728117612071 6091946671367592176418107)
        ·
          refine ⟨9137920007051388264627161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6091946671367592176418107 9137920007051388264627161)
          ·
            refine ⟨6853440005288541198470371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9137920007051388264627161 6853440005288541198470371)
            ·
              refine ⟨10280160007932811797705557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6853440005288541198470371 10280160007932811797705557)
              ·
                refine ⟨60235312546481319127181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 10280160007932811797705557 60235312546481319127181)
                ·
                  rfl

theorem cell19_197957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 9].length) (baseStart_197957 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_197957 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_197957 prefixEnd_197957 := by exact prefixLift 197957
  have htrace : WordTrace (prefixWord ++ tailWord_197957) baseStart_197957 baseEnd_197957 := by
    simpa [prefixWord, tailWord_197957, baseEnd_197957] using wordTrace_append hprefix tailTrace_197957
  have hstable : (prefixWord ++ tailWord_197957).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_197957).length < 2 ^ (prefixWord ++ tailWord_197957).sum := by decide
  have hdescent : baseEnd_197957 < baseStart_197957 := by decide
  rcases family_descends (prefixWord ++ tailWord_197957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_197976 : List Nat := [2, 1, 2, 2, 1, 1, 10]
def baseStart_197976 : Nat := 118140960795 + 197976 * 2 ^ 59
def prefixEnd_197976 : Nat := 4983230072969 + 3 ^ 40 * 197976 * 2
def baseEnd_197976 : Nat := 20080364652764968234969

theorem tailTrace_197976 : CollatzResearch.WordTrace tailWord_197976 prefixEnd_197976 20080364652764968234969 := by
  unfold tailWord_197976
  simp only [CollatzResearch.WordTrace]
  refine ⟨3610388965387119227014891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4813851953849492302686521 3610388965387119227014891)
  ·
    refine ⟨5415583448080678840522337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3610388965387119227014891 5415583448080678840522337)
    ·
      refine ⟨4061687586060509130391753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5415583448080678840522337 4061687586060509130391753)
      ·
        refine ⟨3046265689545381847793815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4061687586060509130391753 3046265689545381847793815)
        ·
          refine ⟨4569398534318072771690723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3046265689545381847793815 4569398534318072771690723)
          ·
            refine ⟨6854097801477109157536085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4569398534318072771690723 6854097801477109157536085)
            ·
              refine ⟨20080364652764968234969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 6854097801477109157536085 20080364652764968234969)
              ·
                rfl

theorem cell19_197976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 10].length) (baseStart_197976 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_197976 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_197976 prefixEnd_197976 := by exact prefixLift 197976
  have htrace : WordTrace (prefixWord ++ tailWord_197976) baseStart_197976 baseEnd_197976 := by
    simpa [prefixWord, tailWord_197976, baseEnd_197976] using wordTrace_append hprefix tailTrace_197976
  have hstable : (prefixWord ++ tailWord_197976).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_197976).length < 2 ^ (prefixWord ++ tailWord_197976).sum := by decide
  have hdescent : baseEnd_197976 < baseStart_197976 := by decide
  rcases family_descends (prefixWord ++ tailWord_197976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_198046 : List Nat := [4, 3, 1, 2, 2, 1, 2, 4]
def baseStart_198046 : Nat := 118140960795 + 198046 * 2 ^ 59
def prefixEnd_198046 : Nat := 4983230072969 + 3 ^ 40 * 198046 * 2
def baseEnd_198046 : Nat := 60262393896555483149161

theorem tailTrace_198046 : CollatzResearch.WordTrace tailWord_198046 prefixEnd_198046 60262393896555483149161 := by
  unfold tailWord_198046
  simp only [CollatzResearch.WordTrace]
  refine ⟨902916380065080051134749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 4815554027013760272718661 902916380065080051134749)
  ·
    refine ⟨338593642524405019175531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 902916380065080051134749 338593642524405019175531)
    ·
      refine ⟨507890463786607528763297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 338593642524405019175531 507890463786607528763297)
      ·
        refine ⟨380917847839955646572473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 507890463786607528763297 380917847839955646572473)
        ·
          refine ⟨285688385879966734929355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 380917847839955646572473 285688385879966734929355)
          ·
            refine ⟨428532578819950102394033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 285688385879966734929355 428532578819950102394033)
            ·
              refine ⟨321399434114962576795525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 428532578819950102394033 321399434114962576795525)
              ·
                refine ⟨60262393896555483149161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 321399434114962576795525 60262393896555483149161)
                ·
                  rfl

theorem cell19_198046_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 2, 1, 2, 4].length) (baseStart_198046 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_198046 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_198046 prefixEnd_198046 := by exact prefixLift 198046
  have htrace : WordTrace (prefixWord ++ tailWord_198046) baseStart_198046 baseEnd_198046 := by
    simpa [prefixWord, tailWord_198046, baseEnd_198046] using wordTrace_append hprefix tailTrace_198046
  have hstable : (prefixWord ++ tailWord_198046).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_198046).length < 2 ^ (prefixWord ++ tailWord_198046).sum := by decide
  have hdescent : baseEnd_198046 < baseStart_198046 := by decide
  rcases family_descends (prefixWord ++ tailWord_198046) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_198050 : List Nat := [3, 3, 1, 2, 1, 2, 1, 6]
def baseStart_198050 : Nat := 118140960795 + 198050 * 2 ^ 59
def prefixEnd_198050 : Nat := 4983230072969 + 3 ^ 40 * 198050 * 2
def baseEnd_198050 : Nat := 60263611035884659060261

theorem tailTrace_198050 : CollatzResearch.WordTrace tailWord_198050 prefixEnd_198050 60263611035884659060261 := by
  unfold tailWord_198050
  simp only [CollatzResearch.WordTrace]
  refine ⟨1805869233126537273055901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4815651288337432728149069 1805869233126537273055901)
  ·
    refine ⟨677200962422451477395963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1805869233126537273055901 677200962422451477395963)
    ·
      refine ⟨1015801443633677216093945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 677200962422451477395963 1015801443633677216093945)
      ·
        refine ⟨761851082725257912070459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1015801443633677216093945 761851082725257912070459)
        ·
          refine ⟨1142776624087886868105689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 761851082725257912070459 1142776624087886868105689)
          ·
            refine ⟨857082468065915151079267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1142776624087886868105689 857082468065915151079267)
            ·
              refine ⟨1285623702098872726618901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 857082468065915151079267 1285623702098872726618901)
              ·
                refine ⟨60263611035884659060261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1285623702098872726618901 60263611035884659060261)
                ·
                  rfl

theorem cell19_198050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 1, 6].length) (baseStart_198050 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_198050 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_198050 prefixEnd_198050 := by exact prefixLift 198050
  have htrace : WordTrace (prefixWord ++ tailWord_198050) baseStart_198050 baseEnd_198050 := by
    simpa [prefixWord, tailWord_198050, baseEnd_198050] using wordTrace_append hprefix tailTrace_198050
  have hstable : (prefixWord ++ tailWord_198050).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_198050).length < 2 ^ (prefixWord ++ tailWord_198050).sum := by decide
  have hdescent : baseEnd_198050 < baseStart_198050 := by decide
  rcases family_descends (prefixWord ++ tailWord_198050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_198069 : List Nat := [1, 3, 3, 2, 2, 1, 2, 5]
def baseStart_198069 : Nat := 118140960795 + 198069 * 2 ^ 59
def prefixEnd_198069 : Nat := 4983230072969 + 3 ^ 40 * 198069 * 2
def baseEnd_198069 : Nat := 60269392447698244637987

theorem tailTrace_198069 : CollatzResearch.WordTrace tailWord_198069 prefixEnd_198069 60269392447698244637987 := by
  unfold tailWord_198069
  simp only [CollatzResearch.WordTrace]
  refine ⟨7224169919437315337165261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4816113279624876891443507 7224169919437315337165261)
  ·
    refine ⟨2709063719788993251436973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7224169919437315337165261 2709063719788993251436973)
    ·
      refine ⟨1015898894920872469288865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2709063719788993251436973 1015898894920872469288865)
      ·
        refine ⟨761924171190654351966649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1015898894920872469288865 761924171190654351966649)
        ·
          refine ⟨571443128392990763974987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 761924171190654351966649 571443128392990763974987)
          ·
            refine ⟨857164692589486145962481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 571443128392990763974987 857164692589486145962481)
            ·
              refine ⟨642873519442114609471861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 857164692589486145962481 642873519442114609471861)
              ·
                refine ⟨60269392447698244637987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 642873519442114609471861 60269392447698244637987)
                ·
                  rfl

theorem cell19_198069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 2, 5].length) (baseStart_198069 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_198069 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_198069 prefixEnd_198069 := by exact prefixLift 198069
  have htrace : WordTrace (prefixWord ++ tailWord_198069) baseStart_198069 baseEnd_198069 := by
    simpa [prefixWord, tailWord_198069, baseEnd_198069] using wordTrace_append hprefix tailTrace_198069
  have hstable : (prefixWord ++ tailWord_198069).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_198069).length < 2 ^ (prefixWord ++ tailWord_198069).sum := by decide
  have hdescent : baseEnd_198069 < baseStart_198069 := by decide
  rcases family_descends (prefixWord ++ tailWord_198069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_198071 : List Nat := [1, 1, 3, 1, 3, 2, 1, 7]
def baseStart_198071 : Nat := 118140960795 + 198071 * 2 ^ 59
def prefixEnd_198071 : Nat := 4983230072969 + 3 ^ 40 * 198071 * 2
def baseEnd_198071 : Nat := 60270001017362832593537

theorem tailTrace_198071 : CollatzResearch.WordTrace tailWord_198071 prefixEnd_198071 60270001017362832593537 := by
  unfold tailWord_198071
  simp only [CollatzResearch.WordTrace]
  refine ⟨7224242865430069678738067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4816161910286713119158711 7224242865430069678738067)
  ·
    refine ⟨10836364298145104518107101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7224242865430069678738067 10836364298145104518107101)
    ·
      refine ⟨4063636611804414194290163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10836364298145104518107101 4063636611804414194290163)
      ·
        refine ⟨6095454917706621291435245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4063636611804414194290163 6095454917706621291435245)
        ·
          refine ⟨2285795594139982984288217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6095454917706621291435245 2285795594139982984288217)
          ·
            refine ⟨1714346695604987238216163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2285795594139982984288217 1714346695604987238216163)
            ·
              refine ⟨2571520043407480857324245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1714346695604987238216163 2571520043407480857324245)
              ·
                refine ⟨60270001017362832593537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2571520043407480857324245 60270001017362832593537)
                ·
                  rfl

theorem cell19_198071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 1, 7].length) (baseStart_198071 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_198071 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_198071 prefixEnd_198071 := by exact prefixLift 198071
  have htrace : WordTrace (prefixWord ++ tailWord_198071) baseStart_198071 baseEnd_198071 := by
    simpa [prefixWord, tailWord_198071, baseEnd_198071] using wordTrace_append hprefix tailTrace_198071
  have hstable : (prefixWord ++ tailWord_198071).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_198071).length < 2 ^ (prefixWord ++ tailWord_198071).sum := by decide
  have hdescent : baseEnd_198071 < baseStart_198071 := by decide
  rcases family_descends (prefixWord ++ tailWord_198071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_198082 : List Nat := [3, 5, 2, 1, 1, 7]
def baseStart_198082 : Nat := 118140960795 + 198082 * 2 ^ 59
def prefixEnd_198082 : Nat := 4983230072969 + 3 ^ 40 * 198082 * 2
def baseEnd_198082 : Nat := 6697038683390896261007

theorem tailTrace_198082 : CollatzResearch.WordTrace tailWord_198082 prefixEnd_198082 6697038683390896261007 := by
  unfold tailWord_198082
  simp only [CollatzResearch.WordTrace]
  refine ⟨1806161017097554639347125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4816429378926812371592333 1806161017097554639347125)
  ·
    refine ⟨169327595352895747438793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 1806161017097554639347125 169327595352895747438793)
    ·
      refine ⟨126995696514671810579095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 169327595352895747438793 126995696514671810579095)
      ·
        refine ⟨190493544772007715868643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 126995696514671810579095 190493544772007715868643)
        ·
          refine ⟨285740317158011573802965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 190493544772007715868643 285740317158011573802965)
          ·
            refine ⟨6697038683390896261007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 285740317158011573802965 6697038683390896261007)
            ·
              rfl

theorem cell19_198082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 1, 7].length) (baseStart_198082 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_198082 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_198082 prefixEnd_198082 := by exact prefixLift 198082
  have htrace : WordTrace (prefixWord ++ tailWord_198082) baseStart_198082 baseEnd_198082 := by
    simpa [prefixWord, tailWord_198082, baseEnd_198082] using wordTrace_append hprefix tailTrace_198082
  have hstable : (prefixWord ++ tailWord_198082).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_198082).length < 2 ^ (prefixWord ++ tailWord_198082).sum := by decide
  have hdescent : baseEnd_198082 < baseStart_198082 := by decide
  rcases family_descends (prefixWord ++ tailWord_198082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_198090 : List Nat := [3, 1, 2, 1, 2, 10]
def baseStart_198090 : Nat := 118140960795 + 198090 * 2 ^ 59
def prefixEnd_198090 : Nat := 4983230072969 + 3 ^ 40 * 198090 * 2
def baseEnd_198090 : Nat := 6697309158797379796807

theorem tailTrace_198090 : CollatzResearch.WordTrace tailWord_198090 prefixEnd_198090 6697309158797379796807 := by
  unfold tailWord_198090
  simp only [CollatzResearch.WordTrace]
  refine ⟨1806233963090308980919931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4816623901574157282453149 1806233963090308980919931)
  ·
    refine ⟨2709350944635463471379897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1806233963090308980919931 2709350944635463471379897)
    ·
      refine ⟨2032013208476597603534923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2709350944635463471379897 2032013208476597603534923)
      ·
        refine ⟨3048019812714896405302385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2032013208476597603534923 3048019812714896405302385)
        ·
          refine ⟨2286014859536172303976789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3048019812714896405302385 2286014859536172303976789)
          ·
            refine ⟨6697309158797379796807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 2286014859536172303976789 6697309158797379796807)
            ·
              rfl

theorem cell19_198090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 10].length) (baseStart_198090 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_198090 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_198090 prefixEnd_198090 := by exact prefixLift 198090
  have htrace : WordTrace (prefixWord ++ tailWord_198090) baseStart_198090 baseEnd_198090 := by
    simpa [prefixWord, tailWord_198090, baseEnd_198090] using wordTrace_append hprefix tailTrace_198090
  have hstable : (prefixWord ++ tailWord_198090).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_198090).length < 2 ^ (prefixWord ++ tailWord_198090).sum := by decide
  have hdescent : baseEnd_198090 < baseStart_198090 := by decide
  rcases family_descends (prefixWord ++ tailWord_198090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_198145 : List Nat := [1, 2, 4, 1, 4, 1, 6]
def baseStart_198145 : Nat := 118140960795 + 198145 * 2 ^ 59
def prefixEnd_198145 : Nat := 4983230072969 + 3 ^ 40 * 198145 * 2
def baseEnd_198145 : Nat := 20097506031650862316297

theorem tailTrace_198145 : CollatzResearch.WordTrace tailWord_198145 prefixEnd_198145 20097506031650862316297 := by
  unfold tailWord_198145
  simp only [CollatzResearch.WordTrace]
  refine ⟨7226941867161980316931889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4817961244774653544621259 7226941867161980316931889)
  ·
    refine ⟨5420206400371485237698917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7226941867161980316931889 5420206400371485237698917)
    ·
      refine ⟨1016288700069653482068547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5420206400371485237698917 1016288700069653482068547)
      ·
        refine ⟨1524433050104480223102821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1016288700069653482068547 1524433050104480223102821)
        ·
          refine ⟨285831196894590041831779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1524433050104480223102821 285831196894590041831779)
          ·
            refine ⟨428746795341885062747669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 285831196894590041831779 428746795341885062747669)
            ·
              refine ⟨20097506031650862316297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 428746795341885062747669 20097506031650862316297)
              ·
                rfl

theorem cell19_198145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 4, 1, 6].length) (baseStart_198145 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_198145 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_198145 prefixEnd_198145 := by exact prefixLift 198145
  have htrace : WordTrace (prefixWord ++ tailWord_198145) baseStart_198145 baseEnd_198145 := by
    simpa [prefixWord, tailWord_198145, baseEnd_198145] using wordTrace_append hprefix tailTrace_198145
  have hstable : (prefixWord ++ tailWord_198145).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_198145).length < 2 ^ (prefixWord ++ tailWord_198145).sum := by decide
  have hdescent : baseEnd_198145 < baseStart_198145 := by decide
  rcases family_descends (prefixWord ++ tailWord_198145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_198179 : List Nat := [1, 1, 1, 4, 6, 1, 2, 3]
def baseStart_198179 : Nat := 118140960795 + 198179 * 2 ^ 59
def prefixEnd_198179 : Nat := 4983230072969 + 3 ^ 40 * 198179 * 2
def baseEnd_198179 : Nat := 60302863779250582193243

theorem tailTrace_198179 : CollatzResearch.WordTrace tailWord_198179 prefixEnd_198179 60302863779250582193243 := by
  unfold tailWord_198179
  simp only [CollatzResearch.WordTrace]
  refine ⟨7228181949038804123669591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4818787966025869415779727 7228181949038804123669591)
  ·
    refine ⟨10842272923558206185504387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7228181949038804123669591 10842272923558206185504387)
    ·
      refine ⟨16263409385337309278256581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10842272923558206185504387 16263409385337309278256581)
      ·
        refine ⟨3049389259750745489673109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 16263409385337309278256581 3049389259750745489673109)
        ·
          refine ⟨142940121550816194828427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 3049389259750745489673109 142940121550816194828427)
          ·
            refine ⟨214410182326224292242641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 142940121550816194828427 214410182326224292242641)
            ·
              refine ⟨160807636744668219181981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 214410182326224292242641 160807636744668219181981)
              ·
                refine ⟨60302863779250582193243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 160807636744668219181981 60302863779250582193243)
                ·
                  rfl

theorem cell19_198179_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 6, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 6, 1, 2, 3].length) (baseStart_198179 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_198179 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_198179 prefixEnd_198179 := by exact prefixLift 198179
  have htrace : WordTrace (prefixWord ++ tailWord_198179) baseStart_198179 baseEnd_198179 := by
    simpa [prefixWord, tailWord_198179, baseEnd_198179] using wordTrace_append hprefix tailTrace_198179
  have hstable : (prefixWord ++ tailWord_198179).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_198179).length < 2 ^ (prefixWord ++ tailWord_198179).sum := by decide
  have hdescent : baseEnd_198179 < baseStart_198179 := by decide
  rcases family_descends (prefixWord ++ tailWord_198179) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_198198 : List Nat := [5, 1, 2, 1, 4, 1, 5]
def baseStart_198198 : Nat := 118140960795 + 198198 * 2 ^ 59
def prefixEnd_198198 : Nat := 4983230072969 + 3 ^ 40 * 198198 * 2
def baseEnd_198198 : Nat := 20102881730354722590323

theorem tailTrace_198198 : CollatzResearch.WordTrace tailWord_198198 prefixEnd_198198 20102881730354722590323 := by
  unfold tailWord_198198
  simp only [CollatzResearch.WordTrace]
  refine ⟨451804683498123148038203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 4819249957313313579074165 451804683498123148038203)
  ·
    refine ⟨677707025247184722057305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 451804683498123148038203 677707025247184722057305)
    ·
      refine ⟨508280268935388541542979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 677707025247184722057305 508280268935388541542979)
      ·
        refine ⟨762420403403082812314469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 508280268935388541542979 762420403403082812314469)
        ·
          refine ⟨142953825638078027308963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 762420403403082812314469 142953825638078027308963)
          ·
            refine ⟨214430738457117040963445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 142953825638078027308963 214430738457117040963445)
            ·
              refine ⟨20102881730354722590323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 214430738457117040963445 20102881730354722590323)
              ·
                rfl

theorem cell19_198198_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 4, 1, 5].length) (baseStart_198198 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_198198 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_198198 prefixEnd_198198 := by exact prefixLift 198198
  have htrace : WordTrace (prefixWord ++ tailWord_198198) baseStart_198198 baseEnd_198198 := by
    simpa [prefixWord, tailWord_198198, baseEnd_198198] using wordTrace_append hprefix tailTrace_198198
  have hstable : (prefixWord ++ tailWord_198198).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_198198).length < 2 ^ (prefixWord ++ tailWord_198198).sum := by decide
  have hdescent : baseEnd_198198 < baseStart_198198 := by decide
  rcases family_descends (prefixWord ++ tailWord_198198) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_198276 : List Nat := [2, 3, 2, 1, 4, 2, 1, 4]
def baseStart_198276 : Nat := 118140960795 + 198276 * 2 ^ 59
def prefixEnd_198276 : Nat := 4983230072969 + 3 ^ 40 * 198276 * 2
def baseEnd_198276 : Nat := 60332379407983098037423

theorem tailTrace_198276 : CollatzResearch.WordTrace tailWord_198276 prefixEnd_198276 60332379407983098037423 := by
  unfold tailWord_198276
  simp only [CollatzResearch.WordTrace]
  refine ⟨3615859914843694844975341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4821146553124926459967121 3615859914843694844975341)
  ·
    refine ⟨1355947468066385566865753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3615859914843694844975341 1355947468066385566865753)
    ·
      refine ⟨1016960601049789175149315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1355947468066385566865753 1016960601049789175149315)
      ·
        refine ⟨1525440901574683762723973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1016960601049789175149315 1525440901574683762723973)
        ·
          refine ⟨286020169045253205510745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1525440901574683762723973 286020169045253205510745)
          ·
            refine ⟨214515126783939904133059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 286020169045253205510745 214515126783939904133059)
            ·
              refine ⟨321772690175909856199589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 214515126783939904133059 321772690175909856199589)
              ·
                refine ⟨60332379407983098037423, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 321772690175909856199589 60332379407983098037423)
                ·
                  rfl

theorem cell19_198276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 4, 2, 1, 4].length) (baseStart_198276 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_198276 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_198276 prefixEnd_198276 := by exact prefixLift 198276
  have htrace : WordTrace (prefixWord ++ tailWord_198276) baseStart_198276 baseEnd_198276 := by
    simpa [prefixWord, tailWord_198276, baseEnd_198276] using wordTrace_append hprefix tailTrace_198276
  have hstable : (prefixWord ++ tailWord_198276).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_198276).length < 2 ^ (prefixWord ++ tailWord_198276).sum := by decide
  have hdescent : baseEnd_198276 < baseStart_198276 := by decide
  rcases family_descends (prefixWord ++ tailWord_198276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_198312 : List Nat := [2, 1, 7, 1, 1, 1, 6]
def baseStart_198312 : Nat := 118140960795 + 198312 * 2 ^ 59
def prefixEnd_198312 : Nat := 4983230072969 + 3 ^ 40 * 198312 * 2
def baseEnd_198312 : Nat := 20114444553981893745775

theorem tailTrace_198312 : CollatzResearch.WordTrace tailWord_198312 prefixEnd_198312 20114444553981893745775 := by
  unfold tailWord_198312
  simp only [CollatzResearch.WordTrace]
  refine ⟨3616516428778483919130595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4822021905037978558840793 3616516428778483919130595)
  ·
    refine ⟨5424774643167725878695893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3616516428778483919130595 5424774643167725878695893)
    ·
      refine ⟨127143155699243575281935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 5424774643167725878695893 127143155699243575281935)
      ·
        refine ⟨190714733548865362922903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 127143155699243575281935 190714733548865362922903)
        ·
          refine ⟨286072100323298044384355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 190714733548865362922903 286072100323298044384355)
          ·
            refine ⟨429108150484947066576533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 286072100323298044384355 429108150484947066576533)
            ·
              refine ⟨20114444553981893745775, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 429108150484947066576533 20114444553981893745775)
              ·
                rfl

theorem cell19_198312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 1, 1, 6].length) (baseStart_198312 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_198312 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_198312 prefixEnd_198312 := by exact prefixLift 198312
  have htrace : WordTrace (prefixWord ++ tailWord_198312) baseStart_198312 baseEnd_198312 := by
    simpa [prefixWord, tailWord_198312, baseEnd_198312] using wordTrace_append hprefix tailTrace_198312
  have hstable : (prefixWord ++ tailWord_198312).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_198312).length < 2 ^ (prefixWord ++ tailWord_198312).sum := by decide
  have hdescent : baseEnd_198312 < baseStart_198312 := by decide
  rcases family_descends (prefixWord ++ tailWord_198312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_198354 : List Nat := [3, 2, 2, 2, 2, 2, 1, 5]
def baseStart_198354 : Nat := 118140960795 + 198354 * 2 ^ 59
def prefixEnd_198354 : Nat := 4983230072969 + 3 ^ 40 * 198354 * 2
def baseEnd_198354 : Nat := 60356113624902028303877

theorem tailTrace_198354 : CollatzResearch.WordTrace tailWord_198354 prefixEnd_198354 60356113624902028303877 := by
  unfold tailWord_198354
  simp only [CollatzResearch.WordTrace]
  refine ⟨1808641180851202252822529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4823043148936539340860077 1808641180851202252822529)
  ·
    refine ⟨1356480885638401689616897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1808641180851202252822529 1356480885638401689616897)
    ·
      refine ⟨1017360664228801267212673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1356480885638401689616897 1017360664228801267212673)
      ·
        refine ⟨763020498171600950409505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1017360664228801267212673 763020498171600950409505)
        ·
          refine ⟨572265373628700712807129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 763020498171600950409505 572265373628700712807129)
          ·
            refine ⟨429199030221525534605347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 572265373628700712807129 429199030221525534605347)
            ·
              refine ⟨643798545332288301908021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 429199030221525534605347 643798545332288301908021)
              ·
                refine ⟨60356113624902028303877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 643798545332288301908021 60356113624902028303877)
                ·
                  rfl

theorem cell19_198354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 2, 1, 5].length) (baseStart_198354 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_198354 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_198354 prefixEnd_198354 := by exact prefixLift 198354
  have htrace : WordTrace (prefixWord ++ tailWord_198354) baseStart_198354 baseEnd_198354 := by
    simpa [prefixWord, tailWord_198354, baseEnd_198354] using wordTrace_append hprefix tailTrace_198354
  have hstable : (prefixWord ++ tailWord_198354).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_198354).length < 2 ^ (prefixWord ++ tailWord_198354).sum := by decide
  have hdescent : baseEnd_198354 < baseStart_198354 := by decide
  rcases family_descends (prefixWord ++ tailWord_198354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_198371 : List Nat := [1, 1, 1, 7, 3, 1, 5]
def baseStart_198371 : Nat := 118140960795 + 198371 * 2 ^ 59
def prefixEnd_198371 : Nat := 4983230072969 + 3 ^ 40 * 198371 * 2
def baseEnd_198371 : Nat := 20120428822350341975351

theorem tailTrace_198371 : CollatzResearch.WordTrace tailWord_198371 prefixEnd_198371 20120428822350341975351 := by
  unfold tailWord_198371
  simp only [CollatzResearch.WordTrace]
  refine ⟨7235184764343220914658967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4823456509562147276439311 7235184764343220914658967)
  ·
    refine ⟨10852777146514831371988451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7235184764343220914658967 10852777146514831371988451)
    ·
      refine ⟨16279165719772247057982677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10852777146514831371988451 16279165719772247057982677)
      ·
        refine ⟨381542946557162040421469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 16279165719772247057982677 381542946557162040421469)
        ·
          refine ⟨143078604958935765158051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 381542946557162040421469 143078604958935765158051)
          ·
            refine ⟨214617907438403647737077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 143078604958935765158051 214617907438403647737077)
            ·
              refine ⟨20120428822350341975351, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 214617907438403647737077 20120428822350341975351)
              ·
                rfl

theorem cell19_198371_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 3, 1, 5].length) (baseStart_198371 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_198371 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_198371 prefixEnd_198371 := by exact prefixLift 198371
  have htrace : WordTrace (prefixWord ++ tailWord_198371) baseStart_198371 baseEnd_198371 := by
    simpa [prefixWord, tailWord_198371, baseEnd_198371] using wordTrace_append hprefix tailTrace_198371
  have hstable : (prefixWord ++ tailWord_198371).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_198371).length < 2 ^ (prefixWord ++ tailWord_198371).sum := by decide
  have hdescent : baseEnd_198371 < baseStart_198371 := by decide
  rcases family_descends (prefixWord ++ tailWord_198371) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_198388 : List Nat := [2, 6, 1, 1, 1, 2, 2, 4]
def baseStart_198388 : Nat := 118140960795 + 198388 * 2 ^ 59
def prefixEnd_198388 : Nat := 4983230072969 + 3 ^ 40 * 198388 * 2
def baseEnd_198388 : Nat := 60366459309200023548229

theorem tailTrace_198388 : CollatzResearch.WordTrace tailWord_198388 prefixEnd_198388 60366459309200023548229 := by
  unfold tailWord_198388
  simp only [CollatzResearch.WordTrace]
  refine ⟨3617902402640816409013909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4823869870187755212018545 3617902402640816409013909)
  ·
    refine ⟨169589175123788269172527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 3617902402640816409013909 169589175123788269172527)
    ·
      refine ⟨254383762685682403758791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 169589175123788269172527 254383762685682403758791)
      ·
        refine ⟨381575644028523605638187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 254383762685682403758791 381575644028523605638187)
        ·
          refine ⟨572363466042785408457281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 381575644028523605638187 572363466042785408457281)
          ·
            refine ⟨429272599532089056342961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 572363466042785408457281 429272599532089056342961)
            ·
              refine ⟨321954449649066792257221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 429272599532089056342961 321954449649066792257221)
              ·
                refine ⟨60366459309200023548229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 321954449649066792257221 60366459309200023548229)
                ·
                  rfl

theorem cell19_198388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 2, 2, 4].length) (baseStart_198388 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_198388 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_198388 prefixEnd_198388 := by exact prefixLift 198388
  have htrace : WordTrace (prefixWord ++ tailWord_198388) baseStart_198388 baseEnd_198388 := by
    simpa [prefixWord, tailWord_198388, baseEnd_198388] using wordTrace_append hprefix tailTrace_198388
  have hstable : (prefixWord ++ tailWord_198388).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_198388).length < 2 ^ (prefixWord ++ tailWord_198388).sum := by decide
  have hdescent : baseEnd_198388 < baseStart_198388 := by decide
  rcases family_descends (prefixWord ++ tailWord_198388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_198449 : List Nat := [1, 2, 2, 3, 2, 4, 1, 4]
def baseStart_198449 : Nat := 118140960795 + 198449 * 2 ^ 59
def prefixEnd_198449 : Nat := 4983230072969 + 3 ^ 40 * 198449 * 2
def baseEnd_198449 : Nat := 60385020683969956192507

theorem tailTrace_198449 : CollatzResearch.WordTrace tailWord_198449 prefixEnd_198449 60385020683969956192507 := by
  unfold tailWord_198449
  simp only [CollatzResearch.WordTrace]
  refine ⟨7238029658060640235998401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4825353105373760157332267 7238029658060640235998401)
  ·
    refine ⟨5428522243545480176998801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7238029658060640235998401 5428522243545480176998801)
    ·
      refine ⟨4071391682659110132749101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5428522243545480176998801 4071391682659110132749101)
      ·
        refine ⟨1526771880997166299780913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4071391682659110132749101 1526771880997166299780913)
        ·
          refine ⟨1145078910747874724835685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1526771880997166299780913 1145078910747874724835685)
          ·
            refine ⟨214702295765226510906691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1145078910747874724835685 214702295765226510906691)
            ·
              refine ⟨322053443647839766360037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 214702295765226510906691 322053443647839766360037)
              ·
                refine ⟨60385020683969956192507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 322053443647839766360037 60385020683969956192507)
                ·
                  rfl

theorem cell19_198449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 4, 1, 4].length) (baseStart_198449 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_198449 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_198449 prefixEnd_198449 := by exact prefixLift 198449
  have htrace : WordTrace (prefixWord ++ tailWord_198449) baseStart_198449 baseEnd_198449 := by
    simpa [prefixWord, tailWord_198449, baseEnd_198449] using wordTrace_append hprefix tailTrace_198449
  have hstable : (prefixWord ++ tailWord_198449).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_198449).length < 2 ^ (prefixWord ++ tailWord_198449).sum := by decide
  have hdescent : baseEnd_198449 < baseStart_198449 := by decide
  rcases family_descends (prefixWord ++ tailWord_198449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_198542 : List Nat := [4, 1, 1, 5, 1, 2, 5]
def baseStart_198542 : Nat := 118140960795 + 198542 * 2 ^ 59
def prefixEnd_198542 : Nat := 4983230072969 + 3 ^ 40 * 198542 * 2
def baseEnd_198542 : Nat := 20137773057791098708529

theorem tailTrace_198542 : CollatzResearch.WordTrace tailWord_198542 prefixEnd_198542 20137773057791098708529 := by
  unfold tailWord_198542
  simp only [CollatzResearch.WordTrace]
  refine ⟨905177705840464639891735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 4827614431149144746089253 905177705840464639891735)
  ·
    refine ⟨1357766558760696959837603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 905177705840464639891735 1357766558760696959837603)
    ·
      refine ⟨2036649838141045439756405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1357766558760696959837603 2036649838141045439756405)
      ·
        refine ⟨190935922325723009977163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 2036649838141045439756405 190935922325723009977163)
        ·
          refine ⟨286403883488584514965745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 190935922325723009977163 286403883488584514965745)
          ·
            refine ⟨214802912616438386224309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 286403883488584514965745 214802912616438386224309)
            ·
              refine ⟨20137773057791098708529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 214802912616438386224309 20137773057791098708529)
              ·
                rfl

theorem cell19_198542_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 1, 2, 5].length) (baseStart_198542 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_198542 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_198542 prefixEnd_198542 := by exact prefixLift 198542
  have htrace : WordTrace (prefixWord ++ tailWord_198542) baseStart_198542 baseEnd_198542 := by
    simpa [prefixWord, tailWord_198542, baseEnd_198542] using wordTrace_append hprefix tailTrace_198542
  have hstable : (prefixWord ++ tailWord_198542).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_198542).length < 2 ^ (prefixWord ++ tailWord_198542).sum := by decide
  have hdescent : baseEnd_198542 < baseStart_198542 := by decide
  rcases family_descends (prefixWord ++ tailWord_198542) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_198618 : List Nat := [3, 1, 1, 2, 6, 1, 1, 4]
def baseStart_198618 : Nat := 118140960795 + 198618 * 2 ^ 59
def prefixEnd_198618 : Nat := 4983230072969 + 3 ^ 40 * 198618 * 2
def baseEnd_198618 : Nat := 60436444820627638436491

theorem tailTrace_198618 : CollatzResearch.WordTrace tailWord_198618 prefixEnd_198618 60436444820627638436491 := by
  unfold tailWord_198618
  simp only [CollatzResearch.WordTrace]
  refine ⟨1811048398612095524725127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4829462396298921399267005 1811048398612095524725127)
  ·
    refine ⟨2716572597918143287087691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1811048398612095524725127 2716572597918143287087691)
    ·
      refine ⟨4074858896877214930631537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2716572597918143287087691 4074858896877214930631537)
      ·
        refine ⟨3056144172657911197973653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4074858896877214930631537 3056144172657911197973653)
        ·
          refine ⟨143256758093339587405015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 3056144172657911197973653 143256758093339587405015)
          ·
            refine ⟨214885137140009381107523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 143256758093339587405015 214885137140009381107523)
            ·
              refine ⟨322327705710014071661285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 214885137140009381107523 322327705710014071661285)
              ·
                refine ⟨60436444820627638436491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 322327705710014071661285 60436444820627638436491)
                ·
                  rfl

theorem cell19_198618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 6, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 6, 1, 1, 4].length) (baseStart_198618 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_198618 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_198618 prefixEnd_198618 := by exact prefixLift 198618
  have htrace : WordTrace (prefixWord ++ tailWord_198618) baseStart_198618 baseEnd_198618 := by
    simpa [prefixWord, tailWord_198618, baseEnd_198618] using wordTrace_append hprefix tailTrace_198618
  have hstable : (prefixWord ++ tailWord_198618).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_198618).length < 2 ^ (prefixWord ++ tailWord_198618).sum := by decide
  have hdescent : baseEnd_198618 < baseStart_198618 := by decide
  rcases family_descends (prefixWord ++ tailWord_198618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_198643 : List Nat := [1, 1, 1, 2, 2, 2, 1, 9]
def baseStart_198643 : Nat := 118140960795 + 198643 * 2 ^ 59
def prefixEnd_198643 : Nat := 4983230072969 + 3 ^ 40 * 198643 * 2
def baseEnd_198643 : Nat := 60444051941434987880867

theorem tailTrace_198643 : CollatzResearch.WordTrace tailWord_198643 prefixEnd_198643 60444051941434987880867 := by
  unfold tailWord_198643
  simp only [CollatzResearch.WordTrace]
  refine ⟨7245105419357811368560583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4830070279571874245707055 7245105419357811368560583)
  ·
    refine ⟨10867658129036717052840875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7245105419357811368560583 10867658129036717052840875)
    ·
      refine ⟨16301487193555075579261313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10867658129036717052840875 16301487193555075579261313)
      ·
        refine ⟨12226115395166306684445985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16301487193555075579261313 12226115395166306684445985)
        ·
          refine ⟨9169586546374730013334489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12226115395166306684445985 9169586546374730013334489)
          ·
            refine ⟨6877189909781047510000867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9169586546374730013334489 6877189909781047510000867)
            ·
              refine ⟨10315784864671571265001301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6877189909781047510000867 10315784864671571265001301)
              ·
                refine ⟨60444051941434987880867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 10315784864671571265001301 60444051941434987880867)
                ·
                  rfl

theorem cell19_198643_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 9].length) (baseStart_198643 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_198643 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_198643 prefixEnd_198643 := by exact prefixLift 198643
  have htrace : WordTrace (prefixWord ++ tailWord_198643) baseStart_198643 baseEnd_198643 := by
    simpa [prefixWord, tailWord_198643, baseEnd_198643] using wordTrace_append hprefix tailTrace_198643
  have hstable : (prefixWord ++ tailWord_198643).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_198643).length < 2 ^ (prefixWord ++ tailWord_198643).sum := by decide
  have hdescent : baseEnd_198643 < baseStart_198643 := by decide
  rcases family_descends (prefixWord ++ tailWord_198643) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_198681 : List Nat := [1, 2, 1, 2, 1, 1, 3, 8]
def baseStart_198681 : Nat := 118140960795 + 198681 * 2 ^ 59
def prefixEnd_198681 : Nat := 4983230072969 + 3 ^ 40 * 198681 * 2
def baseEnd_198681 : Nat := 60455614765062159036319

theorem tailTrace_198681 : CollatzResearch.WordTrace tailWord_198681 prefixEnd_198681 60455614765062159036319 := by
  unfold tailWord_198681
  simp only [CollatzResearch.WordTrace]
  refine ⟨7246491393220143858443897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4830994262146762572295931 7246491393220143858443897)
  ·
    refine ⟨5434868544915107893832923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7246491393220143858443897 5434868544915107893832923)
    ·
      refine ⟨8152302817372661840749385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5434868544915107893832923 8152302817372661840749385)
      ·
        refine ⟨6114227113029496380562039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8152302817372661840749385 6114227113029496380562039)
        ·
          refine ⟨9171340669544244570843059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6114227113029496380562039 9171340669544244570843059)
          ·
            refine ⟨13757011004316366856264589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9171340669544244570843059 13757011004316366856264589)
            ·
              refine ⟨5158879126618637571099221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13757011004316366856264589 5158879126618637571099221)
              ·
                refine ⟨60455614765062159036319, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 5158879126618637571099221 60455614765062159036319)
                ·
                  rfl

theorem cell19_198681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 3, 8].length) (baseStart_198681 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_198681 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_198681 prefixEnd_198681 := by exact prefixLift 198681
  have htrace : WordTrace (prefixWord ++ tailWord_198681) baseStart_198681 baseEnd_198681 := by
    simpa [prefixWord, tailWord_198681, baseEnd_198681] using wordTrace_append hprefix tailTrace_198681
  have hstable : (prefixWord ++ tailWord_198681).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_198681).length < 2 ^ (prefixWord ++ tailWord_198681).sum := by decide
  have hdescent : baseEnd_198681 < baseStart_198681 := by decide
  rcases family_descends (prefixWord ++ tailWord_198681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_198692 : List Nat := [2, 3, 1, 4, 3, 1, 2, 3]
def baseStart_198692 : Nat := 118140960795 + 198692 * 2 ^ 59
def prefixEnd_198692 : Nat := 4983230072969 + 3 ^ 40 * 198692 * 2
def baseEnd_198692 : Nat := 60458961898217392791845

theorem tailTrace_198692 : CollatzResearch.WordTrace tailWord_198692 prefixEnd_198692 60458961898217392791845 := by
  unfold tailWord_198692
  simp only [CollatzResearch.WordTrace]
  refine ⟨3623446298090146368547165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4831261730786861824729553 3623446298090146368547165)
  ·
    refine ⟨1358792361783804888205187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3623446298090146368547165 1358792361783804888205187)
    ·
      refine ⟨2038188542675707332307781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1358792361783804888205187 2038188542675707332307781)
      ·
        refine ⟨382160351751695124807709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2038188542675707332307781 382160351751695124807709)
        ·
          refine ⟨143310131906885671802891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 382160351751695124807709 143310131906885671802891)
          ·
            refine ⟨214965197860328507704337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 143310131906885671802891 214965197860328507704337)
            ·
              refine ⟨161223898395246380778253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 214965197860328507704337 161223898395246380778253)
              ·
                refine ⟨60458961898217392791845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 161223898395246380778253 60458961898217392791845)
                ·
                  rfl

theorem cell19_198692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 3, 1, 2, 3].length) (baseStart_198692 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_198692 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_198692 prefixEnd_198692 := by exact prefixLift 198692
  have htrace : WordTrace (prefixWord ++ tailWord_198692) baseStart_198692 baseEnd_198692 := by
    simpa [prefixWord, tailWord_198692, baseEnd_198692] using wordTrace_append hprefix tailTrace_198692
  have hstable : (prefixWord ++ tailWord_198692).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_198692).length < 2 ^ (prefixWord ++ tailWord_198692).sum := by decide
  have hdescent : baseEnd_198692 < baseStart_198692 := by decide
  rcases family_descends (prefixWord ++ tailWord_198692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_198719 : List Nat := [1, 1, 2, 2, 3, 1, 9]
def baseStart_198719 : Nat := 118140960795 + 198719 * 2 ^ 59
def prefixEnd_198719 : Nat := 4983230072969 + 3 ^ 40 * 198719 * 2
def baseEnd_198719 : Nat := 20155725862896443397257

theorem tailTrace_198719 : CollatzResearch.WordTrace tailWord_198719 prefixEnd_198719 20155725862896443397257 := by
  unfold tailWord_198719
  simp only [CollatzResearch.WordTrace]
  refine ⟨7247877367082476348327211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4831918244721650898884807 7247877367082476348327211)
  ·
    refine ⟨10871816050623714522490817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7247877367082476348327211 10871816050623714522490817)
    ·
      refine ⟨8153862037967785891868113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10871816050623714522490817 8153862037967785891868113)
      ·
        refine ⟨6115396528475839418901085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8153862037967785891868113 6115396528475839418901085)
        ·
          refine ⟨2293273698178439782087907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6115396528475839418901085 2293273698178439782087907)
          ·
            refine ⟨3439910547267659673131861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2293273698178439782087907 3439910547267659673131861)
            ·
              refine ⟨20155725862896443397257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 3439910547267659673131861 20155725862896443397257)
              ·
                rfl

theorem cell19_198719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 9].length) (baseStart_198719 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_198719 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_198719 prefixEnd_198719 := by exact prefixLift 198719
  have htrace : WordTrace (prefixWord ++ tailWord_198719) baseStart_198719 baseEnd_198719 := by
    simpa [prefixWord, tailWord_198719, baseEnd_198719] using wordTrace_append hprefix tailTrace_198719
  have hstable : (prefixWord ++ tailWord_198719).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_198719).length < 2 ^ (prefixWord ++ tailWord_198719).sum := by decide
  have hdescent : baseEnd_198719 < baseStart_198719 := by decide
  rcases family_descends (prefixWord ++ tailWord_198719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_198774 : List Nat := [5, 1, 1, 2, 1, 9]
def baseStart_198774 : Nat := 118140960795 + 198774 * 2 ^ 59
def prefixEnd_198774 : Nat := 4983230072969 + 3 ^ 40 * 198774 * 2
def baseEnd_198774 : Nat := 6720434806051722107711

theorem tailTrace_198774 : CollatzResearch.WordTrace tailWord_198774 prefixEnd_198774 6720434806051722107711 := by
  unfold tailWord_198774
  simp only [CollatzResearch.WordTrace]
  refine ⟨453117711367701296348711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 4833255587922147161052917 453117711367701296348711)
  ·
    refine ⟨679676567051551944523067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 453117711367701296348711 679676567051551944523067)
    ·
      refine ⟨1019514850577327916784601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 679676567051551944523067 1019514850577327916784601)
      ·
        refine ⟨764636137932995937588451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1019514850577327916784601 764636137932995937588451)
        ·
          refine ⟨1146954206899493906382677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 764636137932995937588451 1146954206899493906382677)
          ·
            refine ⟨6720434806051722107711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 1146954206899493906382677 6720434806051722107711)
            ·
              rfl

theorem cell19_198774_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 9].length) (baseStart_198774 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_198774 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_198774 prefixEnd_198774 := by exact prefixLift 198774
  have htrace : WordTrace (prefixWord ++ tailWord_198774) baseStart_198774 baseEnd_198774 := by
    simpa [prefixWord, tailWord_198774, baseEnd_198774] using wordTrace_append hprefix tailTrace_198774
  have hstable : (prefixWord ++ tailWord_198774).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_198774).length < 2 ^ (prefixWord ++ tailWord_198774).sum := by decide
  have hdescent : baseEnd_198774 < baseStart_198774 := by decide
  rcases family_descends (prefixWord ++ tailWord_198774) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_198882 : List Nat := [3, 3, 4, 1, 1, 2, 5]
def baseStart_198882 : Nat := 118140960795 + 198882 * 2 ^ 59
def prefixEnd_198882 : Nat := 4983230072969 + 3 ^ 40 * 198882 * 2
def baseEnd_198882 : Nat := 20172258672117749523035

theorem tailTrace_198882 : CollatzResearch.WordTrace tailWord_198882 prefixEnd_198882 20172258672117749523035 := by
  unfold tailWord_198882
  simp only [CollatzResearch.WordTrace]
  refine ⟨1813455616372988796627725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4835881643661303457673933 1813455616372988796627725)
  ·
    refine ⟨680045856139870798735397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1813455616372988796627725 680045856139870798735397)
    ·
      refine ⟨127508598026225774762887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 680045856139870798735397 127508598026225774762887)
      ·
        refine ⟨191262897039338662144331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 127508598026225774762887 191262897039338662144331)
        ·
          refine ⟨286894345559007993216497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 191262897039338662144331 286894345559007993216497)
          ·
            refine ⟨215170759169255994912373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 286894345559007993216497 215170759169255994912373)
            ·
              refine ⟨20172258672117749523035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 215170759169255994912373 20172258672117749523035)
              ·
                rfl

theorem cell19_198882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 1, 2, 5].length) (baseStart_198882 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_198882 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_198882 prefixEnd_198882 := by exact prefixLift 198882
  have htrace : WordTrace (prefixWord ++ tailWord_198882) baseStart_198882 baseEnd_198882 := by
    simpa [prefixWord, tailWord_198882, baseEnd_198882] using wordTrace_append hprefix tailTrace_198882
  have hstable : (prefixWord ++ tailWord_198882).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_198882).length < 2 ^ (prefixWord ++ tailWord_198882).sum := by decide
  have hdescent : baseEnd_198882 < baseStart_198882 := by decide
  rcases family_descends (prefixWord ++ tailWord_198882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_198888 : List Nat := [2, 1, 4, 1, 2, 4, 5]
def baseStart_198888 : Nat := 118140960795 + 198888 * 2 ^ 59
def prefixEnd_198888 : Nat := 4983230072969 + 3 ^ 40 * 198888 * 2
def baseEnd_198888 : Nat := 20172867241782337478585

theorem tailTrace_198888 : CollatzResearch.WordTrace tailWord_198888 prefixEnd_198888 20172867241782337478585 := by
  unfold tailWord_198888
  simp only [CollatzResearch.WordTrace]
  refine ⟨3627020651735109105614659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4836027535646812140819545 3627020651735109105614659)
  ·
    refine ⟨5440530977602663658421989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3627020651735109105614659 5440530977602663658421989)
    ·
      refine ⟨1020099558300499435954123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5440530977602663658421989 1020099558300499435954123)
      ·
        refine ⟨1530149337450749153931185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1020099558300499435954123 1530149337450749153931185)
        ·
          refine ⟨1147612003088061865448389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1530149337450749153931185 1147612003088061865448389)
          ·
            refine ⟨215177250579011599771573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1147612003088061865448389 215177250579011599771573)
            ·
              refine ⟨20172867241782337478585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 215177250579011599771573 20172867241782337478585)
              ·
                rfl

theorem cell19_198888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 4, 5].length) (baseStart_198888 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_198888 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_198888 prefixEnd_198888 := by exact prefixLift 198888
  have htrace : WordTrace (prefixWord ++ tailWord_198888) baseStart_198888 baseEnd_198888 := by
    simpa [prefixWord, tailWord_198888, baseEnd_198888] using wordTrace_append hprefix tailTrace_198888
  have hstable : (prefixWord ++ tailWord_198888).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_198888).length < 2 ^ (prefixWord ++ tailWord_198888).sum := by decide
  have hdescent : baseEnd_198888 < baseStart_198888 := by decide
  rcases family_descends (prefixWord ++ tailWord_198888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_198958 : List Nat := [4, 1, 3, 3, 2, 1, 1, 4]
def baseStart_198958 : Nat := 118140960795 + 198958 * 2 ^ 59
def prefixEnd_198958 : Nat := 4983230072969 + 3 ^ 40 * 198958 * 2
def baseEnd_198958 : Nat := 60539901663607590880009

theorem tailTrace_198958 : CollatzResearch.WordTrace tailWord_198958 prefixEnd_198958 60539901663607590880009 := by
  unfold tailWord_198958
  simp only [CollatzResearch.WordTrace]
  refine ⟨907074301652077520784691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 4837729608811080110851685 907074301652077520784691)
  ·
    refine ⟨1360611452478116281177037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 907074301652077520784691 1360611452478116281177037)
    ·
      refine ⟨510229294679293605441389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1360611452478116281177037 510229294679293605441389)
      ·
        refine ⟨191335985504735102040521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 510229294679293605441389 191335985504735102040521)
        ·
          refine ⟨143501989128551326530391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 191335985504735102040521 143501989128551326530391)
          ·
            refine ⟨215252983692826989795587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 143501989128551326530391 215252983692826989795587)
            ·
              refine ⟨322879475539240484693381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 215252983692826989795587 322879475539240484693381)
              ·
                refine ⟨60539901663607590880009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 322879475539240484693381 60539901663607590880009)
                ·
                  rfl

theorem cell19_198958_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 2, 1, 1, 4].length) (baseStart_198958 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_198958 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_198958 prefixEnd_198958 := by exact prefixLift 198958
  have htrace : WordTrace (prefixWord ++ tailWord_198958) baseStart_198958 baseEnd_198958 := by
    simpa [prefixWord, tailWord_198958, baseEnd_198958] using wordTrace_append hprefix tailTrace_198958
  have hstable : (prefixWord ++ tailWord_198958).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_198958).length < 2 ^ (prefixWord ++ tailWord_198958).sum := by decide
  have hdescent : baseEnd_198958 < baseStart_198958 := by decide
  rcases family_descends (prefixWord ++ tailWord_198958) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_198962 : List Nat := [3, 2, 1, 1, 5, 2, 1, 4]
def baseStart_198962 : Nat := 118140960795 + 198962 * 2 ^ 59
def prefixEnd_198962 : Nat := 4983230072969 + 3 ^ 40 * 198962 * 2
def baseEnd_198962 : Nat := 60541118802936766791109

theorem tailTrace_198962 : CollatzResearch.WordTrace tailWord_198962 prefixEnd_198962 60541118802936766791109 := by
  unfold tailWord_198962
  simp only [CollatzResearch.WordTrace]
  refine ⟨1814185076300532212355785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4837826870134752566282093 1814185076300532212355785)
  ·
    refine ⟨1360638807225399159266839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1814185076300532212355785 1360638807225399159266839)
    ·
      refine ⟨2040958210838098738900259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1360638807225399159266839 2040958210838098738900259)
      ·
        refine ⟨3061437316257148108350389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2040958210838098738900259 3061437316257148108350389)
        ·
          refine ⟨287009748399107635157849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 3061437316257148108350389 287009748399107635157849)
          ·
            refine ⟨215257311299330726368387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 287009748399107635157849 215257311299330726368387)
            ·
              refine ⟨322885966948996089552581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 215257311299330726368387 322885966948996089552581)
              ·
                refine ⟨60541118802936766791109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 322885966948996089552581 60541118802936766791109)
                ·
                  rfl

theorem cell19_198962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 5, 2, 1, 4].length) (baseStart_198962 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_198962 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_198962 prefixEnd_198962 := by exact prefixLift 198962
  have htrace : WordTrace (prefixWord ++ tailWord_198962) baseStart_198962 baseEnd_198962 := by
    simpa [prefixWord, tailWord_198962, baseEnd_198962] using wordTrace_append hprefix tailTrace_198962
  have hstable : (prefixWord ++ tailWord_198962).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_198962).length < 2 ^ (prefixWord ++ tailWord_198962).sum := by decide
  have hdescent : baseEnd_198962 < baseStart_198962 := by decide
  rcases family_descends (prefixWord ++ tailWord_198962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_198983 : List Nat := [1, 1, 4, 1, 2, 2, 5, 3]
def baseStart_198983 : Nat := 118140960795 + 198983 * 2 ^ 59
def prefixEnd_198983 : Nat := 4983230072969 + 3 ^ 40 * 198983 * 2
def baseEnd_198983 : Nat := 60547508784414940324385

theorem tailTrace_198983 : CollatzResearch.WordTrace tailWord_198983 prefixEnd_198983 60547508784414940324385 := by
  unfold tailWord_198983
  simp only [CollatzResearch.WordTrace]
  refine ⟨7257506238126049435937603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4838337492084032957291735 7257506238126049435937603)
  ·
    refine ⟨10886259357189074153906405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7257506238126049435937603 10886259357189074153906405)
    ·
      refine ⟨2041173629472951403857451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10886259357189074153906405 2041173629472951403857451)
      ·
        refine ⟨3061760444209427105786177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2041173629472951403857451 3061760444209427105786177)
        ·
          refine ⟨2296320333157070329339633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3061760444209427105786177 2296320333157070329339633)
          ·
            refine ⟨1722240249867802747004725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2296320333157070329339633 1722240249867802747004725)
            ·
              refine ⟨161460023425106507531693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1722240249867802747004725 161460023425106507531693)
              ·
                refine ⟨60547508784414940324385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 161460023425106507531693 60547508784414940324385)
                ·
                  rfl

theorem cell19_198983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 5, 3].length) (baseStart_198983 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_198983 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_198983 prefixEnd_198983 := by exact prefixLift 198983
  have htrace : WordTrace (prefixWord ++ tailWord_198983) baseStart_198983 baseEnd_198983 := by
    simpa [prefixWord, tailWord_198983, baseEnd_198983] using wordTrace_append hprefix tailTrace_198983
  have hstable : (prefixWord ++ tailWord_198983).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_198983).length < 2 ^ (prefixWord ++ tailWord_198983).sum := by decide
  have hdescent : baseEnd_198983 < baseStart_198983 := by decide
  rcases family_descends (prefixWord ++ tailWord_198983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_199116 : List Nat := [2, 2, 1, 4, 4, 6]
def baseStart_199116 : Nat := 118140960795 + 199116 * 2 ^ 59
def prefixEnd_199116 : Nat := 4983230072969 + 3 ^ 40 * 199116 * 2
def baseEnd_199116 : Nat := 6731997629678893263163

theorem tailTrace_199116 : CollatzResearch.WordTrace tailWord_199116 prefixEnd_199116 6731997629678893263163 := by
  unfold tailWord_199116
  simp only [CollatzResearch.WordTrace]
  refine ⟨3631178573322106575264601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4841571431096142100352801 3631178573322106575264601)
  ·
    refine ⟨2723383929991579931448451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3631178573322106575264601 2723383929991579931448451)
    ·
      refine ⟨4085075894987369897172677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2723383929991579931448451 4085075894987369897172677)
      ·
        refine ⟨765951730310131855719877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4085075894987369897172677 765951730310131855719877)
        ·
          refine ⟨143615949433149722947477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 765951730310131855719877 143615949433149722947477)
          ·
            refine ⟨6731997629678893263163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 143615949433149722947477 6731997629678893263163)
            ·
              rfl

theorem cell19_199116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 4, 6].length) (baseStart_199116 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_199116 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_199116 prefixEnd_199116 := by exact prefixLift 199116
  have htrace : WordTrace (prefixWord ++ tailWord_199116) baseStart_199116 baseEnd_199116 := by
    simpa [prefixWord, tailWord_199116, baseEnd_199116] using wordTrace_append hprefix tailTrace_199116
  have hstable : (prefixWord ++ tailWord_199116).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_199116).length < 2 ^ (prefixWord ++ tailWord_199116).sum := by decide
  have hdescent : baseEnd_199116 < baseStart_199116 := by decide
  rcases family_descends (prefixWord ++ tailWord_199116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_199135 : List Nat := [1, 1, 2, 3, 3, 4, 1, 4]
def baseStart_199135 : Nat := 118140960795 + 199135 * 2 ^ 59
def prefixEnd_199135 : Nat := 4983230072969 + 3 ^ 40 * 199135 * 2
def baseEnd_199135 : Nat := 60593760078923624946193

theorem tailTrace_199135 : CollatzResearch.WordTrace tailWord_199135 prefixEnd_199135 60593760078923624946193 := by
  unfold tailWord_199135
  simp only [CollatzResearch.WordTrace]
  refine ⟨7263050133575379395470859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4842033422383586263647239 7263050133575379395470859)
  ·
    refine ⟨10894575200363069093206289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7263050133575379395470859 10894575200363069093206289)
    ·
      refine ⟨8170931400272301819904717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10894575200363069093206289 8170931400272301819904717)
      ·
        refine ⟨3064099275102113182464269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8170931400272301819904717 3064099275102113182464269)
        ·
          refine ⟨1149037228163292443424101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3064099275102113182464269 1149037228163292443424101)
          ·
            refine ⟨215444480280617333142019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1149037228163292443424101 215444480280617333142019)
            ·
              refine ⟨323166720420925999713029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 215444480280617333142019 323166720420925999713029)
              ·
                refine ⟨60593760078923624946193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 323166720420925999713029 60593760078923624946193)
                ·
                  rfl

theorem cell19_199135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 4, 1, 4].length) (baseStart_199135 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_199135 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_199135 prefixEnd_199135 := by exact prefixLift 199135
  have htrace : WordTrace (prefixWord ++ tailWord_199135) baseStart_199135 baseEnd_199135 := by
    simpa [prefixWord, tailWord_199135, baseEnd_199135] using wordTrace_append hprefix tailTrace_199135
  have hstable : (prefixWord ++ tailWord_199135).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_199135).length < 2 ^ (prefixWord ++ tailWord_199135).sum := by decide
  have hdescent : baseEnd_199135 < baseStart_199135 := by decide
  rcases family_descends (prefixWord ++ tailWord_199135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_199298 : List Nat := [3, 4, 3, 1, 2, 1, 1, 4]
def baseStart_199298 : Nat := 118140960795 + 199298 * 2 ^ 59
def prefixEnd_199298 : Nat := 4983230072969 + 3 ^ 40 * 199298 * 2
def baseEnd_199298 : Nat := 60643358506587543323527

theorem tailTrace_199298 : CollatzResearch.WordTrace tailWord_199298 prefixEnd_199298 60643358506587543323527 := by
  unfold tailWord_199298
  simp only [CollatzResearch.WordTrace]
  refine ⟨1817248807996214558413637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4845996821323238822436365 1817248807996214558413637)
  ·
    refine ⟨340734151499290229702557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1817248807996214558413637 340734151499290229702557)
    ·
      refine ⟨127775306812233836138459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 340734151499290229702557 127775306812233836138459)
      ·
        refine ⟨191662960218350754207689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 127775306812233836138459 191662960218350754207689)
        ·
          refine ⟨143747220163763065655767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 191662960218350754207689 143747220163763065655767)
          ·
            refine ⟨215620830245644598483651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 143747220163763065655767 215620830245644598483651)
            ·
              refine ⟨323431245368466897725477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 215620830245644598483651 323431245368466897725477)
              ·
                refine ⟨60643358506587543323527, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 323431245368466897725477 60643358506587543323527)
                ·
                  rfl

theorem cell19_199298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 2, 1, 1, 4].length) (baseStart_199298 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_199298 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_199298 prefixEnd_199298 := by exact prefixLift 199298
  have htrace : WordTrace (prefixWord ++ tailWord_199298) baseStart_199298 baseEnd_199298 := by
    simpa [prefixWord, tailWord_199298, baseEnd_199298] using wordTrace_append hprefix tailTrace_199298
  have hstable : (prefixWord ++ tailWord_199298).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_199298).length < 2 ^ (prefixWord ++ tailWord_199298).sum := by decide
  have hdescent : baseEnd_199298 < baseStart_199298 := by decide
  rcases family_descends (prefixWord ++ tailWord_199298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_199378 : List Nat := [3, 2, 2, 2, 4, 1, 2, 3]
def baseStart_199378 : Nat := 118140960795 + 199378 * 2 ^ 59
def prefixEnd_199378 : Nat := 4983230072969 + 3 ^ 40 * 199378 * 2
def baseEnd_199378 : Nat := 60667701293171061545531

theorem tailTrace_199378 : CollatzResearch.WordTrace tailWord_199378 prefixEnd_199378 60667701293171061545531 := by
  unfold tailWord_199378
  simp only [CollatzResearch.WordTrace]
  refine ⟨1817978267923757974141697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4847942047796687931044525 1817978267923757974141697)
  ·
    refine ⟨1363483700942818480606273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1817978267923757974141697 1363483700942818480606273)
    ·
      refine ⟨1022612775707113860454705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1363483700942818480606273 1022612775707113860454705)
      ·
        refine ⟨766959581780335395341029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1022612775707113860454705 766959581780335395341029)
        ·
          refine ⟨143804921583812886626443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 766959581780335395341029 143804921583812886626443)
          ·
            refine ⟨215707382375719329939665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 143804921583812886626443 215707382375719329939665)
            ·
              refine ⟨161780536781789497454749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 215707382375719329939665 161780536781789497454749)
              ·
                refine ⟨60667701293171061545531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 161780536781789497454749 60667701293171061545531)
                ·
                  rfl

theorem cell19_199378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 4, 1, 2, 3].length) (baseStart_199378 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_199378 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_199378 prefixEnd_199378 := by exact prefixLift 199378
  have htrace : WordTrace (prefixWord ++ tailWord_199378) baseStart_199378 baseEnd_199378 := by
    simpa [prefixWord, tailWord_199378, baseEnd_199378] using wordTrace_append hprefix tailTrace_199378
  have hstable : (prefixWord ++ tailWord_199378).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_199378).length < 2 ^ (prefixWord ++ tailWord_199378).sum := by decide
  have hdescent : baseEnd_199378 < baseStart_199378 := by decide
  rcases family_descends (prefixWord ++ tailWord_199378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_199384 : List Nat := [2, 1, 2, 2, 3, 3, 1, 5]
def baseStart_199384 : Nat := 118140960795 + 199384 * 2 ^ 59
def prefixEnd_199384 : Nat := 4983230072969 + 3 ^ 40 * 199384 * 2
def baseEnd_199384 : Nat := 60669527002164825412181

theorem tailTrace_199384 : CollatzResearch.WordTrace tailWord_199384 prefixEnd_199384 60669527002164825412181 := by
  unfold tailWord_199384
  simp only [CollatzResearch.WordTrace]
  refine ⟨3636065954836647460642603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4848087939782196614190137 3636065954836647460642603)
  ·
    refine ⟨5454098932254971190963905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3636065954836647460642603 5454098932254971190963905)
    ·
      refine ⟨4090574199191228393222929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5454098932254971190963905 4090574199191228393222929)
      ·
        refine ⟨3067930649393421294917197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4090574199191228393222929 3067930649393421294917197)
        ·
          refine ⟨1150473993522532985593949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3067930649393421294917197 1150473993522532985593949)
          ·
            refine ⟨431427747570949869597731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1150473993522532985593949 431427747570949869597731)
            ·
              refine ⟨647141621356424804396597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 431427747570949869597731 647141621356424804396597)
              ·
                refine ⟨60669527002164825412181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 647141621356424804396597 60669527002164825412181)
                ·
                  rfl

theorem cell19_199384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 3, 1, 5].length) (baseStart_199384 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_199384 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_199384 prefixEnd_199384 := by exact prefixLift 199384
  have htrace : WordTrace (prefixWord ++ tailWord_199384) baseStart_199384 baseEnd_199384 := by
    simpa [prefixWord, tailWord_199384, baseEnd_199384] using wordTrace_append hprefix tailTrace_199384
  have hstable : (prefixWord ++ tailWord_199384).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_199384).length < 2 ^ (prefixWord ++ tailWord_199384).sum := by decide
  have hdescent : baseEnd_199384 < baseStart_199384 := by decide
  rcases family_descends (prefixWord ++ tailWord_199384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_199443 : List Nat := [1, 1, 1, 2, 1, 3, 3, 7]
def baseStart_199443 : Nat := 118140960795 + 199443 * 2 ^ 59
def prefixEnd_199443 : Nat := 4983230072969 + 3 ^ 40 * 199443 * 2
def baseEnd_199443 : Nat := 60687479807270170100909

theorem tailTrace_199443 : CollatzResearch.WordTrace tailWord_199443 prefixEnd_199443 60687479807270170100909 := by
  unfold tailWord_199443
  simp only [CollatzResearch.WordTrace]
  refine ⟨7274283816459547997682983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4849522544306365331788655 7274283816459547997682983)
  ·
    refine ⟨10911425724689321996524475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7274283816459547997682983 10911425724689321996524475)
    ·
      refine ⟨16367138587033982994786713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10911425724689321996524475 16367138587033982994786713)
      ·
        refine ⟨12275353940275487246090035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16367138587033982994786713 12275353940275487246090035)
        ·
          refine ⟨18413030910413230869135053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12275353940275487246090035 18413030910413230869135053)
          ·
            refine ⟨6904886591404961575925645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18413030910413230869135053 6904886591404961575925645)
            ·
              refine ⟨2589332471776860590972117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6904886591404961575925645 2589332471776860590972117)
              ·
                refine ⟨60687479807270170100909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2589332471776860590972117 60687479807270170100909)
                ·
                  rfl

theorem cell19_199443_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 3, 7].length) (baseStart_199443 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_199443 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_199443 prefixEnd_199443 := by exact prefixLift 199443
  have htrace : WordTrace (prefixWord ++ tailWord_199443) baseStart_199443 baseEnd_199443 := by
    simpa [prefixWord, tailWord_199443, baseEnd_199443] using wordTrace_append hprefix tailTrace_199443
  have hstable : (prefixWord ++ tailWord_199443).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_199443).length < 2 ^ (prefixWord ++ tailWord_199443).sum := by decide
  have hdescent : baseEnd_199443 < baseStart_199443 := by decide
  rcases family_descends (prefixWord ++ tailWord_199443) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_199460 : List Nat := [2, 3, 1, 3, 3, 7]
def baseStart_199460 : Nat := 118140960795 + 199460 * 2 ^ 59
def prefixEnd_199460 : Nat := 4983230072969 + 3 ^ 40 * 199460 * 2
def baseEnd_199460 : Nat := 6743628072157685302565

theorem tailTrace_199460 : CollatzResearch.WordTrace tailWord_199460 prefixEnd_199460 6743628072157685302565 := by
  unfold tailWord_199460
  simp only [CollatzResearch.WordTrace]
  refine ⟨3637451928698979950525917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4849935904931973267367889 3637451928698979950525917)
  ·
    refine ⟨1364044473262117481447219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3637451928698979950525917 1364044473262117481447219)
    ·
      refine ⟨2046066709893176222170829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1364044473262117481447219 2046066709893176222170829)
      ·
        refine ⟨767275016209941083314061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2046066709893176222170829 767275016209941083314061)
        ·
          refine ⟨287728131078727906242773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 767275016209941083314061 287728131078727906242773)
          ·
            refine ⟨6743628072157685302565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 287728131078727906242773 6743628072157685302565)
            ·
              rfl

theorem cell19_199460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 3, 7].length) (baseStart_199460 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_199460 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_199460 prefixEnd_199460 := by exact prefixLift 199460
  have htrace : WordTrace (prefixWord ++ tailWord_199460) baseStart_199460 baseEnd_199460 := by
    simpa [prefixWord, tailWord_199460, baseEnd_199460] using wordTrace_append hprefix tailTrace_199460
  have hstable : (prefixWord ++ tailWord_199460).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_199460).length < 2 ^ (prefixWord ++ tailWord_199460).sum := by decide
  have hdescent : baseEnd_199460 < baseStart_199460 := by decide
  rcases family_descends (prefixWord ++ tailWord_199460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_199477 : List Nat := [1, 3, 3, 1, 3, 3, 1, 4]
def baseStart_199477 : Nat := 118140960795 + 199477 * 2 ^ 59
def prefixEnd_199477 : Nat := 4983230072969 + 3 ^ 40 * 199477 * 2
def baseEnd_199477 : Nat := 60697825491568165345261

theorem tailTrace_199477 : CollatzResearch.WordTrace tailWord_199477 prefixEnd_199477 60697825491568165345261 := by
  unfold tailWord_199477
  simp only [CollatzResearch.WordTrace]
  refine ⟨7275523898336371804420685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4850349265557581202947123 7275523898336371804420685)
  ·
    refine ⟨2728321461876139426657757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7275523898336371804420685 2728321461876139426657757)
    ·
      refine ⟨1023120548203552284996659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2728321461876139426657757 1023120548203552284996659)
      ·
        refine ⟨1534680822305328427494989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1023120548203552284996659 1534680822305328427494989)
        ·
          refine ⟨575505308364498160310621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1534680822305328427494989 575505308364498160310621)
          ·
            refine ⟨215814490636686810116483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 575505308364498160310621 215814490636686810116483)
            ·
              refine ⟨323721735955030215174725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 215814490636686810116483 323721735955030215174725)
              ·
                refine ⟨60697825491568165345261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 323721735955030215174725 60697825491568165345261)
                ·
                  rfl

theorem cell19_199477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 3, 1, 4].length) (baseStart_199477 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_199477 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_199477 prefixEnd_199477 := by exact prefixLift 199477
  have htrace : WordTrace (prefixWord ++ tailWord_199477) baseStart_199477 baseEnd_199477 := by
    simpa [prefixWord, tailWord_199477, baseEnd_199477] using wordTrace_append hprefix tailTrace_199477
  have hstable : (prefixWord ++ tailWord_199477).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_199477).length < 2 ^ (prefixWord ++ tailWord_199477).sum := by decide
  have hdescent : baseEnd_199477 < baseStart_199477 := by decide
  rcases family_descends (prefixWord ++ tailWord_199477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_199492 : List Nat := [2, 3, 4, 2, 1, 1, 3, 3]
def baseStart_199492 : Nat := 118140960795 + 199492 * 2 ^ 59
def prefixEnd_199492 : Nat := 4983230072969 + 3 ^ 40 * 199492 * 2
def baseEnd_199492 : Nat := 60702389764052575011887

theorem tailTrace_199492 : CollatzResearch.WordTrace tailWord_199492 prefixEnd_199492 60702389764052575011887 := by
  unfold tailWord_199492
  simp only [CollatzResearch.WordTrace]
  refine ⟨3638035496641014683108365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4850713995521352910811153 3638035496641014683108365)
  ·
    refine ⟨1364263311240380506165637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3638035496641014683108365 1364263311240380506165637)
    ·
      refine ⟨255799370857571344906057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1364263311240380506165637 255799370857571344906057)
      ·
        refine ⟨191849528143178508679543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 255799370857571344906057 191849528143178508679543)
        ·
          refine ⟨287774292214767763019315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 191849528143178508679543 287774292214767763019315)
          ·
            refine ⟨431661438322151644528973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 287774292214767763019315 431661438322151644528973)
            ·
              refine ⟨161873039370806866698365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 431661438322151644528973 161873039370806866698365)
              ·
                refine ⟨60702389764052575011887, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 161873039370806866698365 60702389764052575011887)
                ·
                  rfl

theorem cell19_199492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 1, 1, 3, 3].length) (baseStart_199492 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_199492 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_199492 prefixEnd_199492 := by exact prefixLift 199492
  have htrace : WordTrace (prefixWord ++ tailWord_199492) baseStart_199492 baseEnd_199492 := by
    simpa [prefixWord, tailWord_199492, baseEnd_199492] using wordTrace_append hprefix tailTrace_199492
  have hstable : (prefixWord ++ tailWord_199492).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_199492).length < 2 ^ (prefixWord ++ tailWord_199492).sum := by decide
  have hdescent : baseEnd_199492 < baseStart_199492 := by decide
  rcases family_descends (prefixWord ++ tailWord_199492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_199519 : List Nat := [1, 1, 2, 3, 1, 3, 8]
def baseStart_199519 : Nat := 118140960795 + 199519 * 2 ^ 59
def prefixEnd_199519 : Nat := 4983230072969 + 3 ^ 40 * 199519 * 2
def baseEnd_199519 : Nat := 20236868484841504137271

theorem tailTrace_199519 : CollatzResearch.WordTrace tailWord_199519 prefixEnd_199519 20236868484841504137271 := by
  unfold tailWord_199519
  simp only [CollatzResearch.WordTrace]
  refine ⟨7277055764184212977449611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4851370509456141984966407 7277055764184212977449611)
  ·
    refine ⟨10915583646276319466174417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7277055764184212977449611 10915583646276319466174417)
    ·
      refine ⟨8186687734707239599630813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10915583646276319466174417 8186687734707239599630813)
      ·
        refine ⟨3070007900515214849861555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8186687734707239599630813 3070007900515214849861555)
        ·
          refine ⟨4605011850772822274792333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3070007900515214849861555 4605011850772822274792333)
          ·
            refine ⟨1726879444039808353047125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4605011850772822274792333 1726879444039808353047125)
            ·
              refine ⟨20236868484841504137271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1726879444039808353047125 20236868484841504137271)
              ·
                rfl

theorem cell19_199519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 8].length) (baseStart_199519 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_199519 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_199519 prefixEnd_199519 := by exact prefixLift 199519
  have htrace : WordTrace (prefixWord ++ tailWord_199519) baseStart_199519 baseEnd_199519 := by
    simpa [prefixWord, tailWord_199519, baseEnd_199519] using wordTrace_append hprefix tailTrace_199519
  have hstable : (prefixWord ++ tailWord_199519).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_199519).length < 2 ^ (prefixWord ++ tailWord_199519).sum := by decide
  have hdescent : baseEnd_199519 < baseStart_199519 := by decide
  rcases family_descends (prefixWord ++ tailWord_199519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_199570 : List Nat := [3, 2, 3, 2, 3, 1, 5]
def baseStart_199570 : Nat := 118140960795 + 199570 * 2 ^ 59
def prefixEnd_199570 : Nat := 4983230072969 + 3 ^ 40 * 199570 * 2
def baseEnd_199570 : Nat := 20242041326990501759447

theorem tailTrace_199570 : CollatzResearch.WordTrace tailWord_199570 prefixEnd_199570 20242041326990501759447 := by
  unfold tailWord_199570
  simp only [CollatzResearch.WordTrace]
  refine ⟨1819728971749862171889041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4852610591332965791704109 1819728971749862171889041)
  ·
    refine ⟨1364796728812396628916781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1819728971749862171889041 1364796728812396628916781)
    ·
      refine ⟨511798773304648735843793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1364796728812396628916781 511798773304648735843793)
      ·
        refine ⟨383849079978486551882845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 511798773304648735843793 383849079978486551882845)
        ·
          refine ⟨143943404991932456956067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 383849079978486551882845 143943404991932456956067)
          ·
            refine ⟨215915107487898685434101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 143943404991932456956067 215915107487898685434101)
            ·
              refine ⟨20242041326990501759447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 215915107487898685434101 20242041326990501759447)
              ·
                rfl

theorem cell19_199570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 3, 1, 5].length) (baseStart_199570 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_199570 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_199570 prefixEnd_199570 := by exact prefixLift 199570
  have htrace : WordTrace (prefixWord ++ tailWord_199570) baseStart_199570 baseEnd_199570 := by
    simpa [prefixWord, tailWord_199570, baseEnd_199570] using wordTrace_append hprefix tailTrace_199570
  have hstable : (prefixWord ++ tailWord_199570).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_199570).length < 2 ^ (prefixWord ++ tailWord_199570).sum := by decide
  have hdescent : baseEnd_199570 < baseStart_199570 := by decide
  rcases family_descends (prefixWord ++ tailWord_199570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_199591 : List Nat := [1, 1, 6, 1, 3, 1, 2, 4]
def baseStart_199591 : Nat := 118140960795 + 199591 * 2 ^ 59
def prefixEnd_199591 : Nat := 4983230072969 + 3 ^ 40 * 199591 * 2
def baseEnd_199591 : Nat := 60732513962449678811617

theorem tailTrace_199591 : CollatzResearch.WordTrace tailWord_199591 prefixEnd_199591 60732513962449678811617 := by
  unfold tailWord_199591
  simp only [CollatzResearch.WordTrace]
  refine ⟨7279681819923369274070627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4853121213282246182713751 7279681819923369274070627)
  ·
    refine ⟨10919522729885053911105941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7279681819923369274070627 10919522729885053911105941)
    ·
      refine ⟨511852627963361902083091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 10919522729885053911105941 511852627963361902083091)
      ·
        refine ⟨767778941945042853124637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 511852627963361902083091 767778941945042853124637)
        ·
          refine ⟨287917103229391069921739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 767778941945042853124637 287917103229391069921739)
          ·
            refine ⟨431875654844086604882609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 287917103229391069921739 431875654844086604882609)
            ·
              refine ⟨323906741133064953661957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 431875654844086604882609 323906741133064953661957)
              ·
                refine ⟨60732513962449678811617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 323906741133064953661957 60732513962449678811617)
                ·
                  rfl

theorem cell19_199591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 3, 1, 2, 4].length) (baseStart_199591 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_199591 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_199591 prefixEnd_199591 := by exact prefixLift 199591
  have htrace : WordTrace (prefixWord ++ tailWord_199591) baseStart_199591 baseEnd_199591 := by
    simpa [prefixWord, tailWord_199591, baseEnd_199591] using wordTrace_append hprefix tailTrace_199591
  have hstable : (prefixWord ++ tailWord_199591).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_199591).length < 2 ^ (prefixWord ++ tailWord_199591).sum := by decide
  have hdescent : baseEnd_199591 < baseStart_199591 := by decide
  rcases family_descends (prefixWord ++ tailWord_199591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_199652 : List Nat := [2, 3, 1, 1, 1, 1, 2, 8]
def baseStart_199652 : Nat := 118140960795 + 199652 * 2 ^ 59
def prefixEnd_199652 : Nat := 4983230072969 + 3 ^ 40 * 199652 * 2
def baseEnd_199652 : Nat := 60751075337219611455895

theorem tailTrace_199652 : CollatzResearch.WordTrace tailWord_199652 prefixEnd_199652 60751075337219611455895 := by
  unfold tailWord_199652
  simp only [CollatzResearch.WordTrace]
  refine ⟨3640953336351188346020605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4854604448468251128027473 3640953336351188346020605)
  ·
    refine ⟨1365357501131695629757727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3640953336351188346020605 1365357501131695629757727)
    ·
      refine ⟨2048036251697543444636591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1365357501131695629757727 2048036251697543444636591)
      ·
        refine ⟨3072054377546315166954887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2048036251697543444636591 3072054377546315166954887)
        ·
          refine ⟨4608081566319472750432331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3072054377546315166954887 4608081566319472750432331)
          ·
            refine ⟨6912122349479209125648497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4608081566319472750432331 6912122349479209125648497)
            ·
              refine ⟨5184091762109406844236373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6912122349479209125648497 5184091762109406844236373)
              ·
                refine ⟨60751075337219611455895, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 5184091762109406844236373 60751075337219611455895)
                ·
                  rfl

theorem cell19_199652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 2, 8].length) (baseStart_199652 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_199652 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_199652 prefixEnd_199652 := by exact prefixLift 199652
  have htrace : WordTrace (prefixWord ++ tailWord_199652) baseStart_199652 baseEnd_199652 := by
    simpa [prefixWord, tailWord_199652, baseEnd_199652] using wordTrace_append hprefix tailTrace_199652
  have hstable : (prefixWord ++ tailWord_199652).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_199652).length < 2 ^ (prefixWord ++ tailWord_199652).sum := by decide
  have hdescent : baseEnd_199652 < baseStart_199652 := by decide
  rcases family_descends (prefixWord ++ tailWord_199652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_199722 : List Nat := [3, 1, 4, 1, 3, 2, 2, 3]
def baseStart_199722 : Nat := 118140960795 + 199722 * 2 ^ 59
def prefixEnd_199722 : Nat := 4983230072969 + 3 ^ 40 * 199722 * 2
def baseEnd_199722 : Nat := 60772375275480189900149

theorem tailTrace_199722 : CollatzResearch.WordTrace tailWord_199722 prefixEnd_199722 60772375275480189900149 := by
  unfold tailWord_199722
  simp only [CollatzResearch.WordTrace]
  refine ⟨1821114945612194661772355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4856306521632519098059613 1821114945612194661772355)
  ·
    refine ⟨2731672418418291992658533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1821114945612194661772355 2731672418418291992658533)
    ·
      refine ⟨512188578453429748623475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2731672418418291992658533 512188578453429748623475)
      ·
        refine ⟨768282867680144622935213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 512188578453429748623475 768282867680144622935213)
        ·
          refine ⟨288106075380054233600705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 768282867680144622935213 288106075380054233600705)
          ·
            refine ⟨216079556535040675200529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 288106075380054233600705 216079556535040675200529)
            ·
              refine ⟨162059667401280506400397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 216079556535040675200529 162059667401280506400397)
              ·
                refine ⟨60772375275480189900149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 162059667401280506400397 60772375275480189900149)
                ·
                  rfl

theorem cell19_199722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 3, 2, 2, 3].length) (baseStart_199722 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_199722 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_199722 prefixEnd_199722 := by exact prefixLift 199722
  have htrace : WordTrace (prefixWord ++ tailWord_199722) baseStart_199722 baseEnd_199722 := by
    simpa [prefixWord, tailWord_199722, baseEnd_199722] using wordTrace_append hprefix tailTrace_199722
  have hstable : (prefixWord ++ tailWord_199722).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_199722).length < 2 ^ (prefixWord ++ tailWord_199722).sum := by decide
  have hdescent : baseEnd_199722 < baseStart_199722 := by decide
  rcases family_descends (prefixWord ++ tailWord_199722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_199726 : List Nat := [4, 1, 3, 1, 1, 1, 3, 5]
def baseStart_199726 : Nat := 118140960795 + 199726 * 2 ^ 59
def prefixEnd_199726 : Nat := 4983230072969 + 3 ^ 40 * 199726 * 2
def baseEnd_199726 : Nat := 60773592414809365811249

theorem tailTrace_199726 : CollatzResearch.WordTrace tailWord_199726 prefixEnd_199726 60773592414809365811249 := by
  unfold tailWord_199726
  simp only [CollatzResearch.WordTrace]
  refine ⟨910575709304285916279379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 4856403782956191553490021 910575709304285916279379)
  ·
    refine ⟨1365863563956428874419069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 910575709304285916279379 1365863563956428874419069)
    ·
      refine ⟨512198836483660827907151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1365863563956428874419069 512198836483660827907151)
      ·
        refine ⟨768298254725491241860727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 512198836483660827907151 768298254725491241860727)
        ·
          refine ⟨1152447382088236862791091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 768298254725491241860727 1152447382088236862791091)
          ·
            refine ⟨1728671073132355294186637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1152447382088236862791091 1728671073132355294186637)
            ·
              refine ⟨648251652424633235319989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1728671073132355294186637 648251652424633235319989)
              ·
                refine ⟨60773592414809365811249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 648251652424633235319989 60773592414809365811249)
                ·
                  rfl

theorem cell19_199726_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 3, 5].length) (baseStart_199726 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_199726 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_199726 prefixEnd_199726 := by exact prefixLift 199726
  have htrace : WordTrace (prefixWord ++ tailWord_199726) baseStart_199726 baseEnd_199726 := by
    simpa [prefixWord, tailWord_199726, baseEnd_199726] using wordTrace_append hprefix tailTrace_199726
  have hstable : (prefixWord ++ tailWord_199726).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_199726).length < 2 ^ (prefixWord ++ tailWord_199726).sum := by decide
  have hdescent : baseEnd_199726 < baseStart_199726 := by decide
  rcases family_descends (prefixWord ++ tailWord_199726) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_199728 : List Nat := [2, 1, 1, 1, 2, 4, 3, 5]
def baseStart_199728 : Nat := 118140960795 + 199728 * 2 ^ 59
def prefixEnd_199728 : Nat := 4983230072969 + 3 ^ 40 * 199728 * 2
def baseEnd_199728 : Nat := 60774200984473953766799

theorem tailTrace_199728 : CollatzResearch.WordTrace tailWord_199728 prefixEnd_199728 60774200984473953766799 := by
  unfold tailWord_199728
  simp only [CollatzResearch.WordTrace]
  refine ⟨3642339310213520835903919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4856452413618027781205225 3642339310213520835903919)
  ·
    refine ⟨5463508965320281253855879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3642339310213520835903919 5463508965320281253855879)
    ·
      refine ⟨8195263447980421880783819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5463508965320281253855879 8195263447980421880783819)
      ·
        refine ⟨12292895171970632821175729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8195263447980421880783819 12292895171970632821175729)
        ·
          refine ⟨9219671378977974615881797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12292895171970632821175729 9219671378977974615881797)
          ·
            refine ⟨1728688383558370240477837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9219671378977974615881797 1728688383558370240477837)
            ·
              refine ⟨648258143834388840179189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1728688383558370240477837 648258143834388840179189)
              ·
                refine ⟨60774200984473953766799, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 648258143834388840179189 60774200984473953766799)
                ·
                  rfl

theorem cell19_199728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 3, 5].length) (baseStart_199728 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_199728 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_199728 prefixEnd_199728 := by exact prefixLift 199728
  have htrace : WordTrace (prefixWord ++ tailWord_199728) baseStart_199728 baseEnd_199728 := by
    simpa [prefixWord, tailWord_199728, baseEnd_199728] using wordTrace_append hprefix tailTrace_199728
  have hstable : (prefixWord ++ tailWord_199728).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_199728).length < 2 ^ (prefixWord ++ tailWord_199728).sum := by decide
  have hdescent : baseEnd_199728 < baseStart_199728 := by decide
  rcases family_descends (prefixWord ++ tailWord_199728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_199785 : List Nat := [1, 2, 1, 1, 1, 6, 2, 5]
def baseStart_199785 : Nat := 118140960795 + 199785 * 2 ^ 59
def prefixEnd_199785 : Nat := 4983230072969 + 3 ^ 40 * 199785 * 2
def baseEnd_199785 : Nat := 60791545219914710499977

theorem tailTrace_199785 : CollatzResearch.WordTrace tailWord_199785 prefixEnd_199785 60791545219914710499977 := by
  unfold tailWord_199785
  simp only [CollatzResearch.WordTrace]
  refine ⟨7286757581220540406632809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4857838387480360271088539 7286757581220540406632809)
  ·
    refine ⟨5465068185915405304974607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7286757581220540406632809 5465068185915405304974607)
    ·
      refine ⟨8197602278873107957461911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5465068185915405304974607 8197602278873107957461911)
      ·
        refine ⟨12296403418309661936192867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8197602278873107957461911 12296403418309661936192867)
        ·
          refine ⟨18444605127464492904289301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12296403418309661936192867 18444605127464492904289301)
          ·
            refine ⟨864590865349898104888561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 18444605127464492904289301 864590865349898104888561)
            ·
              refine ⟨648443149012423578666421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 864590865349898104888561 648443149012423578666421)
              ·
                refine ⟨60791545219914710499977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 648443149012423578666421 60791545219914710499977)
                ·
                  rfl

theorem cell19_199785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 2, 5].length) (baseStart_199785 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_199785 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_199785 prefixEnd_199785 := by exact prefixLift 199785
  have htrace : WordTrace (prefixWord ++ tailWord_199785) baseStart_199785 baseEnd_199785 := by
    simpa [prefixWord, tailWord_199785, baseEnd_199785] using wordTrace_append hprefix tailTrace_199785
  have hstable : (prefixWord ++ tailWord_199785).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_199785).length < 2 ^ (prefixWord ++ tailWord_199785).sum := by decide
  have hdescent : baseEnd_199785 < baseStart_199785 := by decide
  rcases family_descends (prefixWord ++ tailWord_199785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_199840 : List Nat := [2, 1, 1, 4, 2, 1, 5, 3]
def baseStart_199840 : Nat := 118140960795 + 199840 * 2 ^ 59
def prefixEnd_199840 : Nat := 4983230072969 + 3 ^ 40 * 199840 * 2
def baseEnd_199840 : Nat := 60808280885690879277605

theorem tailTrace_199840 : CollatzResearch.WordTrace tailWord_199840 prefixEnd_199840 60808280885690879277605 := by
  unfold tailWord_199840
  simp only [CollatzResearch.WordTrace]
  refine ⟨3644381798010642399942487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4859175730680856533256649 3644381798010642399942487)
  ·
    refine ⟨5466572697015963599913731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3644381798010642399942487 5466572697015963599913731)
    ·
      refine ⟨8199859045523945399870597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5466572697015963599913731 8199859045523945399870597)
      ·
        refine ⟨1537473571035739762475737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8199859045523945399870597 1537473571035739762475737)
        ·
          refine ⟨1153105178276804821856803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1537473571035739762475737 1153105178276804821856803)
          ·
            refine ⟨1729657767415207232785205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1153105178276804821856803 1729657767415207232785205)
            ·
              refine ⟨162155415695175678073613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1729657767415207232785205 162155415695175678073613)
              ·
                refine ⟨60808280885690879277605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 162155415695175678073613 60808280885690879277605)
                ·
                  rfl

theorem cell19_199840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 5, 3].length) (baseStart_199840 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_199840 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_199840 prefixEnd_199840 := by exact prefixLift 199840
  have htrace : WordTrace (prefixWord ++ tailWord_199840) baseStart_199840 baseEnd_199840 := by
    simpa [prefixWord, tailWord_199840, baseEnd_199840] using wordTrace_append hprefix tailTrace_199840
  have hstable : (prefixWord ++ tailWord_199840).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_199840).length < 2 ^ (prefixWord ++ tailWord_199840).sum := by decide
  have hdescent : baseEnd_199840 < baseStart_199840 := by decide
  rcases family_descends (prefixWord ++ tailWord_199840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_199918 : List Nat := [4, 1, 2, 1, 1, 1, 9]
def baseStart_199918 : Nat := 118140960795 + 199918 * 2 ^ 59
def prefixEnd_199918 : Nat := 4983230072969 + 3 ^ 40 * 199918 * 2
def baseEnd_199918 : Nat := 20277338367536603181353

theorem tailTrace_199918 : CollatzResearch.WordTrace tailWord_199918 prefixEnd_199918 20277338367536603181353 := by
  unfold tailWord_199918
  simp only [CollatzResearch.WordTrace]
  refine ⟨911451061217338015153051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 4861072326492469414149605 911451061217338015153051)
  ·
    refine ⟨1367176591826007022729577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 911451061217338015153051 1367176591826007022729577)
    ·
      refine ⟨1025382443869505267047183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1367176591826007022729577 1025382443869505267047183)
      ·
        refine ⟨1538073665804257900570775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1025382443869505267047183 1538073665804257900570775)
        ·
          refine ⟨2307110498706386850856163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1538073665804257900570775 2307110498706386850856163)
          ·
            refine ⟨3460665748059580276284245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2307110498706386850856163 3460665748059580276284245)
            ·
              refine ⟨20277338367536603181353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 3460665748059580276284245 20277338367536603181353)
              ·
                rfl

theorem cell19_199918_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 9].length) (baseStart_199918 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_199918 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_199918 prefixEnd_199918 := by exact prefixLift 199918
  have htrace : WordTrace (prefixWord ++ tailWord_199918) baseStart_199918 baseEnd_199918 := by
    simpa [prefixWord, tailWord_199918, baseEnd_199918] using wordTrace_append hprefix tailTrace_199918
  have hstable : (prefixWord ++ tailWord_199918).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_199918).length < 2 ^ (prefixWord ++ tailWord_199918).sum := by decide
  have hdescent : baseEnd_199918 < baseStart_199918 := by decide
  rcases family_descends (prefixWord ++ tailWord_199918) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_199937 : List Nat := [1, 2, 4, 1, 1, 3, 1, 6]
def baseStart_199937 : Nat := 118140960795 + 199937 * 2 ^ 59
def prefixEnd_199937 : Nat := 4983230072969 + 3 ^ 40 * 199937 * 2
def baseEnd_199937 : Nat := 60837796514423395121785

theorem tailTrace_199937 : CollatzResearch.WordTrace tailWord_199937 prefixEnd_199937 60837796514423395121785 := by
  unfold tailWord_199937
  simp only [CollatzResearch.WordTrace]
  refine ⟨7292301476669870366166065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4861534317779913577444043 7292301476669870366166065)
  ·
    refine ⟨5469226107502402774624549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7292301476669870366166065 5469226107502402774624549)
    ·
      refine ⟨1025479895156700520242103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5469226107502402774624549 1025479895156700520242103)
      ·
        refine ⟨1538219842735050780363155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1025479895156700520242103 1538219842735050780363155)
        ·
          refine ⟨2307329764102576170544733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1538219842735050780363155 2307329764102576170544733)
          ·
            refine ⟨865248661538466063954275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2307329764102576170544733 865248661538466063954275)
            ·
              refine ⟨1297872992307699095931413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 865248661538466063954275 1297872992307699095931413)
              ·
                refine ⟨60837796514423395121785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1297872992307699095931413 60837796514423395121785)
                ·
                  rfl

theorem cell19_199937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 1, 6].length) (baseStart_199937 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_199937 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_199937 prefixEnd_199937 := by exact prefixLift 199937
  have htrace : WordTrace (prefixWord ++ tailWord_199937) baseStart_199937 baseEnd_199937 := by
    simpa [prefixWord, tailWord_199937, baseEnd_199937] using wordTrace_append hprefix tailTrace_199937
  have hstable : (prefixWord ++ tailWord_199937).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_199937).length < 2 ^ (prefixWord ++ tailWord_199937).sum := by decide
  have hdescent : baseEnd_199937 < baseStart_199937 := by decide
  rcases family_descends (prefixWord ++ tailWord_199937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_200032 : List Nat := [2, 1, 1, 3, 4, 2, 6]
def baseStart_200032 : Nat := 118140960795 + 200032 * 2 ^ 59
def prefixEnd_200032 : Nat := 4983230072969 + 3 ^ 40 * 200032 * 2
def baseEnd_200032 : Nat := 20288901191163774336805

theorem tailTrace_200032 : CollatzResearch.WordTrace tailWord_200032 prefixEnd_200032 20288901191163774336805 := by
  unfold tailWord_200032
  simp only [CollatzResearch.WordTrace]
  refine ⟨3647883205662850795437175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4863844274217134393916233 3647883205662850795437175)
  ·
    refine ⟨5471824808494276193155763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3647883205662850795437175 5471824808494276193155763)
    ·
      refine ⟨8207737212741414289733645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5471824808494276193155763 8207737212741414289733645)
      ·
        refine ⟨3077901454778030358650117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8207737212741414289733645 3077901454778030358650117)
        ·
          refine ⟨577106522770880692246897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3077901454778030358650117 577106522770880692246897)
          ·
            refine ⟨432829892078160519185173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 577106522770880692246897 432829892078160519185173)
            ·
              refine ⟨20288901191163774336805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 432829892078160519185173 20288901191163774336805)
              ·
                rfl

theorem cell19_200032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 2, 6].length) (baseStart_200032 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_200032 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_200032 prefixEnd_200032 := by exact prefixLift 200032
  have htrace : WordTrace (prefixWord ++ tailWord_200032) baseStart_200032 baseEnd_200032 := by
    simpa [prefixWord, tailWord_200032, baseEnd_200032] using wordTrace_append hprefix tailTrace_200032
  have hstable : (prefixWord ++ tailWord_200032).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_200032).length < 2 ^ (prefixWord ++ tailWord_200032).sum := by decide
  have hdescent : baseEnd_200032 < baseStart_200032 := by decide
  rcases family_descends (prefixWord ++ tailWord_200032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_200062 : List Nat := [4, 2, 3, 2, 1, 2, 2, 3]
def baseStart_200062 : Nat := 118140960795 + 200062 * 2 ^ 59
def prefixEnd_200062 : Nat := 4983230072969 + 3 ^ 40 * 200062 * 2
def baseEnd_200062 : Nat := 60875832118460142343667

theorem tailTrace_200062 : CollatzResearch.WordTrace tailWord_200062 prefixEnd_200062 60875832118460142343667 := by
  unfold tailWord_200062
  simp only [CollatzResearch.WordTrace]
  refine ⟨912107575152127089308305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 4864573734144677809644293 912107575152127089308305)
  ·
    refine ⟨684080681364095316981229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 912107575152127089308305 684080681364095316981229)
    ·
      refine ⟨256530255511535743867961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 684080681364095316981229 256530255511535743867961)
      ·
        refine ⟨192397691633651807900971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 256530255511535743867961 192397691633651807900971)
        ·
          refine ⟨288596537450477711851457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 192397691633651807900971 288596537450477711851457)
          ·
            refine ⟨216447403087858283888593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 288596537450477711851457 216447403087858283888593)
            ·
              refine ⟨162335552315893712916445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 216447403087858283888593 162335552315893712916445)
              ·
                refine ⟨60875832118460142343667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 162335552315893712916445 60875832118460142343667)
                ·
                  rfl

theorem cell19_200062_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 1, 2, 2, 3].length) (baseStart_200062 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_200062 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_200062 prefixEnd_200062 := by exact prefixLift 200062
  have htrace : WordTrace (prefixWord ++ tailWord_200062) baseStart_200062 baseEnd_200062 := by
    simpa [prefixWord, tailWord_200062, baseEnd_200062] using wordTrace_append hprefix tailTrace_200062
  have hstable : (prefixWord ++ tailWord_200062).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_200062).length < 2 ^ (prefixWord ++ tailWord_200062).sum := by decide
  have hdescent : baseEnd_200062 < baseStart_200062 := by decide
  rcases family_descends (prefixWord ++ tailWord_200062) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_200066 : List Nat := [3, 4, 2, 1, 1, 2, 1, 5]
def baseStart_200066 : Nat := 118140960795 + 200066 * 2 ^ 59
def prefixEnd_200066 : Nat := 4983230072969 + 3 ^ 40 * 200066 * 2
def baseEnd_200066 : Nat := 60877049257789318254767

theorem tailTrace_200066 : CollatzResearch.WordTrace tailWord_200066 prefixEnd_200066 60877049257789318254767 := by
  unfold tailWord_200066
  simp only [CollatzResearch.WordTrace]
  refine ⟨1824251623300631349403013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4864670995468350265074701 1824251623300631349403013)
  ·
    refine ⟨342047179368868378013065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1824251623300631349403013 342047179368868378013065)
    ·
      refine ⟨256535384526651283509799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 342047179368868378013065 256535384526651283509799)
      ·
        refine ⟨384803076789976925264699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 256535384526651283509799 384803076789976925264699)
        ·
          refine ⟨577204615184965387897049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 384803076789976925264699 577204615184965387897049)
          ·
            refine ⟨432903461388724040922787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 577204615184965387897049 432903461388724040922787)
            ·
              refine ⟨649355192083086061384181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 432903461388724040922787 649355192083086061384181)
              ·
                refine ⟨60877049257789318254767, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 649355192083086061384181 60877049257789318254767)
                ·
                  rfl

theorem cell19_200066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 2, 1, 5].length) (baseStart_200066 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_200066 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_200066 prefixEnd_200066 := by exact prefixLift 200066
  have htrace : WordTrace (prefixWord ++ tailWord_200066) baseStart_200066 baseEnd_200066 := by
    simpa [prefixWord, tailWord_200066, baseEnd_200066] using wordTrace_append hprefix tailTrace_200066
  have hstable : (prefixWord ++ tailWord_200066).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_200066).length < 2 ^ (prefixWord ++ tailWord_200066).sum := by decide
  have hdescent : baseEnd_200066 < baseStart_200066 := by decide
  rcases family_descends (prefixWord ++ tailWord_200066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_200068 : List Nat := [2, 3, 2, 1, 1, 3, 4, 3]
def baseStart_200068 : Nat := 118140960795 + 200068 * 2 ^ 59
def prefixEnd_200068 : Nat := 4983230072969 + 3 ^ 40 * 200068 * 2
def baseEnd_200068 : Nat := 60877657827453906210317

theorem tailTrace_200068 : CollatzResearch.WordTrace tailWord_200068 prefixEnd_200068 60877657827453906210317 := by
  unfold tailWord_200068
  simp only [CollatzResearch.WordTrace]
  refine ⟨3648539719597639869592429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4864719626130186492789905 3648539719597639869592429)
  ·
    refine ⟨1368202394849114951097161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3648539719597639869592429 1368202394849114951097161)
    ·
      refine ⟨1026151796136836213322871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1368202394849114951097161 1026151796136836213322871)
      ·
        refine ⟨1539227694205254319984307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1026151796136836213322871 1539227694205254319984307)
        ·
          refine ⟨2308841541307881479976461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1539227694205254319984307 2308841541307881479976461)
          ·
            refine ⟨865815577990455554991173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2308841541307881479976461 865815577990455554991173)
            ·
              refine ⟨162340420873210416560845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 865815577990455554991173 162340420873210416560845)
              ·
                refine ⟨60877657827453906210317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 162340420873210416560845 60877657827453906210317)
                ·
                  rfl

theorem cell19_200068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 4, 3].length) (baseStart_200068 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_200068 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_200068 prefixEnd_200068 := by exact prefixLift 200068
  have htrace : WordTrace (prefixWord ++ tailWord_200068) baseStart_200068 baseEnd_200068 := by
    simpa [prefixWord, tailWord_200068, baseEnd_200068] using wordTrace_append hprefix tailTrace_200068
  have hstable : (prefixWord ++ tailWord_200068).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_200068).length < 2 ^ (prefixWord ++ tailWord_200068).sum := by decide
  have hdescent : baseEnd_200068 < baseStart_200068 := by decide
  rcases family_descends (prefixWord ++ tailWord_200068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_200089 : List Nat := [1, 2, 1, 2, 1, 7, 5]
def baseStart_200089 : Nat := 118140960795 + 200089 * 2 ^ 59
def prefixEnd_200089 : Nat := 4983230072969 + 3 ^ 40 * 200089 * 2
def baseEnd_200089 : Nat := 20294682602977359914531

theorem tailTrace_200089 : CollatzResearch.WordTrace tailWord_200089 prefixEnd_200089 20294682602977359914531 := by
  unfold tailWord_200089
  simp only [CollatzResearch.WordTrace]
  refine ⟨7297845372119200325699321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4865230248079466883799547 7297845372119200325699321)
  ·
    refine ⟨5473384029089400244274491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7297845372119200325699321 5473384029089400244274491)
    ·
      refine ⟨8210076043634100366411737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5473384029089400244274491 8210076043634100366411737)
      ·
        refine ⟨6157557032725575274808803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8210076043634100366411737 6157557032725575274808803)
        ·
          refine ⟨9236335549088362912213205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6157557032725575274808803 9236335549088362912213205)
          ·
            refine ⟨216476614431758505754997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 9236335549088362912213205 216476614431758505754997)
            ·
              refine ⟨20294682602977359914531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 216476614431758505754997 20294682602977359914531)
              ·
                rfl

theorem cell19_200089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 7, 5].length) (baseStart_200089 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_200089 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_200089 prefixEnd_200089 := by exact prefixLift 200089
  have htrace : WordTrace (prefixWord ++ tailWord_200089) baseStart_200089 baseEnd_200089 := by
    simpa [prefixWord, tailWord_200089, baseEnd_200089] using wordTrace_append hprefix tailTrace_200089
  have hstable : (prefixWord ++ tailWord_200089).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_200089).length < 2 ^ (prefixWord ++ tailWord_200089).sum := by decide
  have hdescent : baseEnd_200089 < baseStart_200089 := by decide
  rcases family_descends (prefixWord ++ tailWord_200089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_200104 : List Nat := [2, 1, 6, 1, 2, 1, 2, 4]
def baseStart_200104 : Nat := 118140960795 + 200104 * 2 ^ 59
def prefixEnd_200104 : Nat := 4983230072969 + 3 ^ 40 * 200104 * 2
def baseEnd_200104 : Nat := 60888612081416489410219

theorem tailTrace_200104 : CollatzResearch.WordTrace tailWord_200104 prefixEnd_200104 60888612081416489410219 := by
  unfold tailWord_200104
  simp only [CollatzResearch.WordTrace]
  refine ⟨3649196233532428943747683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4865594978043238591663577 3649196233532428943747683)
  ·
    refine ⟨5473794350298643415621525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3649196233532428943747683 5473794350298643415621525)
    ·
      refine ⟨256584110170248910107259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 5473794350298643415621525 256584110170248910107259)
      ·
        refine ⟨384876165255373365160889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 256584110170248910107259 384876165255373365160889)
        ·
          refine ⟨288657123941530023870667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 384876165255373365160889 288657123941530023870667)
          ·
            refine ⟨432985685912295035806001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 288657123941530023870667 432985685912295035806001)
            ·
              refine ⟨324739264434221276854501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 432985685912295035806001 324739264434221276854501)
              ·
                refine ⟨60888612081416489410219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 324739264434221276854501 60888612081416489410219)
                ·
                  rfl

theorem cell19_200104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 2, 1, 2, 4].length) (baseStart_200104 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_200104 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_200104 prefixEnd_200104 := by exact prefixLift 200104
  have htrace : WordTrace (prefixWord ++ tailWord_200104) baseStart_200104 baseEnd_200104 := by
    simpa [prefixWord, tailWord_200104, baseEnd_200104] using wordTrace_append hprefix tailTrace_200104
  have hstable : (prefixWord ++ tailWord_200104).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_200104).length < 2 ^ (prefixWord ++ tailWord_200104).sum := by decide
  have hdescent : baseEnd_200104 < baseStart_200104 := by decide
  rcases family_descends (prefixWord ++ tailWord_200104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_200163 : List Nat := [1, 1, 1, 6, 2, 3, 1, 4]
def baseStart_200163 : Nat := 118140960795 + 200163 * 2 ^ 59
def prefixEnd_200163 : Nat := 4983230072969 + 3 ^ 40 * 200163 * 2
def baseEnd_200163 : Nat := 60906564886521834098947

theorem tailTrace_200163 : CollatzResearch.WordTrace tailWord_200163 prefixEnd_200163 60906564886521834098947 := by
  unfold tailWord_200163
  simp only [CollatzResearch.WordTrace]
  refine ⟨7300544373851110963893143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4867029582567407309262095 7300544373851110963893143)
  ·
    refine ⟨10950816560776666445839715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7300544373851110963893143 10950816560776666445839715)
    ·
      refine ⟨16426224841164999668759573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10950816560776666445839715 16426224841164999668759573)
      ·
        refine ⟨769979289429609359473105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 16426224841164999668759573 769979289429609359473105)
        ·
          refine ⟨577484467072207019604829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 769979289429609359473105 577484467072207019604829)
          ·
            refine ⟨216556675152077632351811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 577484467072207019604829 216556675152077632351811)
            ·
              refine ⟨324835012728116448527717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 216556675152077632351811 324835012728116448527717)
              ·
                refine ⟨60906564886521834098947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 324835012728116448527717 60906564886521834098947)
                ·
                  rfl

theorem cell19_200163_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 3, 1, 4].length) (baseStart_200163 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_200163 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_200163 prefixEnd_200163 := by exact prefixLift 200163
  have htrace : WordTrace (prefixWord ++ tailWord_200163) baseStart_200163 baseEnd_200163 := by
    simpa [prefixWord, tailWord_200163, baseEnd_200163] using wordTrace_append hprefix tailTrace_200163
  have hstable : (prefixWord ++ tailWord_200163).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_200163).length < 2 ^ (prefixWord ++ tailWord_200163).sum := by decide
  have hdescent : baseEnd_200163 < baseStart_200163 := by decide
  rcases family_descends (prefixWord ++ tailWord_200163) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_200203 : List Nat := [1, 1, 1, 1, 8, 1, 6]
def baseStart_200203 : Nat := 118140960795 + 200203 * 2 ^ 59
def prefixEnd_200203 : Nat := 4983230072969 + 3 ^ 40 * 200203 * 2
def baseEnd_200203 : Nat := 20306245426604531069983

theorem tailTrace_200203 : CollatzResearch.WordTrace tailWord_200203 prefixEnd_200203 20306245426604531069983 := by
  unfold tailWord_200203
  simp only [CollatzResearch.WordTrace]
  refine ⟨7302003293706197795349263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4868002195804131863566175 7302003293706197795349263)
  ·
    refine ⟨10953004940559296693023895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7302003293706197795349263 10953004940559296693023895)
    ·
      refine ⟨16429507410838945039535843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10953004940559296693023895 16429507410838945039535843)
      ·
        refine ⟨24644261116258417559303765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16429507410838945039535843 24644261116258417559303765)
        ·
          refine ⟨288799934956153330773091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 24644261116258417559303765 288799934956153330773091)
          ·
            refine ⟨433199902434229996159637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 288799934956153330773091 433199902434229996159637)
            ·
              refine ⟨20306245426604531069983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 433199902434229996159637 20306245426604531069983)
              ·
                rfl

theorem cell19_200203_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 8, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 8, 1, 6].length) (baseStart_200203 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_200203 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_200203 prefixEnd_200203 := by exact prefixLift 200203
  have htrace : WordTrace (prefixWord ++ tailWord_200203) baseStart_200203 baseEnd_200203 := by
    simpa [prefixWord, tailWord_200203, baseEnd_200203] using wordTrace_append hprefix tailTrace_200203
  have hstable : (prefixWord ++ tailWord_200203).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_200203).length < 2 ^ (prefixWord ++ tailWord_200203).sum := by decide
  have hdescent : baseEnd_200203 < baseStart_200203 := by decide
  rcases family_descends (prefixWord ++ tailWord_200203) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_200279 : List Nat := [1, 1, 3, 2, 2, 4, 2, 4]
def baseStart_200279 : Nat := 118140960795 + 200279 * 2 ^ 59
def prefixEnd_200279 : Nat := 4983230072969 + 3 ^ 40 * 200279 * 2
def baseEnd_200279 : Nat := 60941861927067935520853

theorem tailTrace_200279 : CollatzResearch.WordTrace tailWord_200279 prefixEnd_200279 60941861927067935520853 := by
  unfold tailWord_200279
  simp only [CollatzResearch.WordTrace]
  refine ⟨7304775241430862775115891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4869850160953908516743927 7304775241430862775115891)
  ·
    refine ⟨10957162862146294162673837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7304775241430862775115891 10957162862146294162673837)
    ·
      refine ⟨4108936073304860311002689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10957162862146294162673837 4108936073304860311002689)
      ·
        refine ⟨3081702054978645233252017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4108936073304860311002689 3081702054978645233252017)
        ·
          refine ⟨2311276541233983924939013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3081702054978645233252017 2311276541233983924939013)
          ·
            refine ⟨433364351481371985926065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2311276541233983924939013 433364351481371985926065)
            ·
              refine ⟨325023263611028989444549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 433364351481371985926065 325023263611028989444549)
              ·
                refine ⟨60941861927067935520853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 325023263611028989444549 60941861927067935520853)
                ·
                  rfl

theorem cell19_200279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 4, 2, 4].length) (baseStart_200279 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_200279 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_200279 prefixEnd_200279 := by exact prefixLift 200279
  have htrace : WordTrace (prefixWord ++ tailWord_200279) baseStart_200279 baseEnd_200279 := by
    simpa [prefixWord, tailWord_200279, baseEnd_200279] using wordTrace_append hprefix tailTrace_200279
  have hstable : (prefixWord ++ tailWord_200279).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_200279).length < 2 ^ (prefixWord ++ tailWord_200279).sum := by decide
  have hdescent : baseEnd_200279 < baseStart_200279 := by decide
  rcases family_descends (prefixWord ++ tailWord_200279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_200298 : List Nat := [3, 1, 3, 2, 1, 2, 2, 5]
def baseStart_200298 : Nat := 118140960795 + 200298 * 2 ^ 59
def prefixEnd_200298 : Nat := 4983230072969 + 3 ^ 40 * 200298 * 2
def baseEnd_200298 : Nat := 60947643338881521098579

theorem tailTrace_200298 : CollatzResearch.WordTrace tailWord_200298 prefixEnd_200298 60947643338881521098579 := by
  unfold tailWord_200298
  simp only [CollatzResearch.WordTrace]
  refine ⟨1826367057090507255014387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4870312152241352680038365 1826367057090507255014387)
  ·
    refine ⟨2739550585635760882521581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1826367057090507255014387 2739550585635760882521581)
    ·
      refine ⟨1027331469613410330945593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2739550585635760882521581 1027331469613410330945593)
      ·
        refine ⟨770498602210057748209195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1027331469613410330945593 770498602210057748209195)
        ·
          refine ⟨1155747903315086622313793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 770498602210057748209195 1155747903315086622313793)
          ·
            refine ⟨866810927486314966735345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1155747903315086622313793 866810927486314966735345)
            ·
              refine ⟨650108195614736225051509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 866810927486314966735345 650108195614736225051509)
              ·
                refine ⟨60947643338881521098579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 650108195614736225051509 60947643338881521098579)
                ·
                  rfl

theorem cell19_200298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 2, 5].length) (baseStart_200298 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_200298 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_200298 prefixEnd_200298 := by exact prefixLift 200298
  have htrace : WordTrace (prefixWord ++ tailWord_200298) baseStart_200298 baseEnd_200298 := by
    simpa [prefixWord, tailWord_200298, baseEnd_200298] using wordTrace_append hprefix tailTrace_200298
  have hstable : (prefixWord ++ tailWord_200298).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_200298).length < 2 ^ (prefixWord ++ tailWord_200298).sum := by decide
  have hdescent : baseEnd_200298 < baseStart_200298 := by decide
  rcases family_descends (prefixWord ++ tailWord_200298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_200334 : List Nat := [4, 1, 1, 3, 1, 4, 1, 4]
def baseStart_200334 : Nat := 118140960795 + 200334 * 2 ^ 59
def prefixEnd_200334 : Nat := 4983230072969 + 3 ^ 40 * 200334 * 2
def baseEnd_200334 : Nat := 60958597592844104298481

theorem tailTrace_200334 : CollatzResearch.WordTrace tailWord_200334 prefixEnd_200334 60958597592844104298481 := by
  unfold tailWord_200334
  simp only [CollatzResearch.WordTrace]
  refine ⟨913347657028950896046007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 4871187504154404778912037 913347657028950896046007)
  ·
    refine ⟨1370021485543426344069011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 913347657028950896046007 1370021485543426344069011)
    ·
      refine ⟨2055032228315139516103517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1370021485543426344069011 2055032228315139516103517)
      ·
        refine ⟨770637085618177318538819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2055032228315139516103517 770637085618177318538819)
        ·
          refine ⟨1155955628427265977808229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 770637085618177318538819 1155955628427265977808229)
          ·
            refine ⟨216741680330112370839043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1155955628427265977808229 216741680330112370839043)
            ·
              refine ⟨325112520495168556258565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 216741680330112370839043 325112520495168556258565)
              ·
                refine ⟨60958597592844104298481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 325112520495168556258565 60958597592844104298481)
                ·
                  rfl

theorem cell19_200334_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 4, 1, 4].length) (baseStart_200334 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_200334 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_200334 prefixEnd_200334 := by exact prefixLift 200334
  have htrace : WordTrace (prefixWord ++ tailWord_200334) baseStart_200334 baseEnd_200334 := by
    simpa [prefixWord, tailWord_200334, baseEnd_200334] using wordTrace_append hprefix tailTrace_200334
  have hstable : (prefixWord ++ tailWord_200334).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_200334).length < 2 ^ (prefixWord ++ tailWord_200334).sum := by decide
  have hdescent : baseEnd_200334 < baseStart_200334 := by decide
  rcases family_descends (prefixWord ++ tailWord_200334) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_200351 : List Nat := [1, 1, 2, 7, 1, 1, 3, 3]
def baseStart_200351 : Nat := 118140960795 + 200351 * 2 ^ 59
def prefixEnd_200351 : Nat := 4983230072969 + 3 ^ 40 * 200351 * 2
def baseEnd_200351 : Nat := 60963770434993101920657

theorem tailTrace_200351 : CollatzResearch.WordTrace tailWord_200351 prefixEnd_200351 60963770434993101920657 := by
  unfold tailWord_200351
  simp only [CollatzResearch.WordTrace]
  refine ⟨7307401297170019071736907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4871600864780012714491271 7307401297170019071736907)
  ·
    refine ⟨10961101945755028607605361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7307401297170019071736907 10961101945755028607605361)
    ·
      refine ⟨8220826459316271455704021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10961101945755028607605361 8220826459316271455704021)
      ·
        refine ⟨192675620140225112243063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 8220826459316271455704021 192675620140225112243063)
        ·
          refine ⟨289013430210337668364595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 192675620140225112243063 289013430210337668364595)
          ·
            refine ⟨433520145315506502546893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 289013430210337668364595 433520145315506502546893)
            ·
              refine ⟨162570054493314938455085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 433520145315506502546893 162570054493314938455085)
              ·
                refine ⟨60963770434993101920657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 162570054493314938455085 60963770434993101920657)
                ·
                  rfl

theorem cell19_200351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 1, 1, 3, 3].length) (baseStart_200351 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_200351 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_200351 prefixEnd_200351 := by exact prefixLift 200351
  have htrace : WordTrace (prefixWord ++ tailWord_200351) baseStart_200351 baseEnd_200351 := by
    simpa [prefixWord, tailWord_200351, baseEnd_200351] using wordTrace_append hprefix tailTrace_200351
  have hstable : (prefixWord ++ tailWord_200351).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_200351).length < 2 ^ (prefixWord ++ tailWord_200351).sum := by decide
  have hdescent : baseEnd_200351 < baseStart_200351 := by decide
  rcases family_descends (prefixWord ++ tailWord_200351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_200353 : List Nat := [1, 2, 3, 3, 2, 2, 3, 3]
def baseStart_200353 : Nat := 118140960795 + 200353 * 2 ^ 59
def prefixEnd_200353 : Nat := 4983230072969 + 3 ^ 40 * 200353 * 2
def baseEnd_200353 : Nat := 60964379004657689876207

theorem tailTrace_200353 : CollatzResearch.WordTrace tailWord_200353 prefixEnd_200353 60964379004657689876207 := by
  unfold tailWord_200353
  simp only [CollatzResearch.WordTrace]
  refine ⟨7307474243162773413309713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4871649495441848942206475 7307474243162773413309713)
  ·
    refine ⟨5480605682372080059982285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7307474243162773413309713 5480605682372080059982285)
    ·
      refine ⟨2055227130889530022493357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5480605682372080059982285 2055227130889530022493357)
      ·
        refine ⟨770710174083573758435009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2055227130889530022493357 770710174083573758435009)
        ·
          refine ⟨578032630562680318826257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 770710174083573758435009 578032630562680318826257)
          ·
            refine ⟨433524472922010239119693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 578032630562680318826257 433524472922010239119693)
            ·
              refine ⟨162571677345753839669885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 433524472922010239119693 162571677345753839669885)
              ·
                refine ⟨60964379004657689876207, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 162571677345753839669885 60964379004657689876207)
                ·
                  rfl

theorem cell19_200353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 2, 3, 3].length) (baseStart_200353 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_200353 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_200353 prefixEnd_200353 := by exact prefixLift 200353
  have htrace : WordTrace (prefixWord ++ tailWord_200353) baseStart_200353 baseEnd_200353 := by
    simpa [prefixWord, tailWord_200353, baseEnd_200353] using wordTrace_append hprefix tailTrace_200353
  have hstable : (prefixWord ++ tailWord_200353).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_200353).length < 2 ^ (prefixWord ++ tailWord_200353).sum := by decide
  have hdescent : baseEnd_200353 < baseStart_200353 := by decide
  rcases family_descends (prefixWord ++ tailWord_200353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_200355 : List Nat := [1, 1, 1, 4, 1, 1, 7, 3]
def baseStart_200355 : Nat := 118140960795 + 200355 * 2 ^ 59
def prefixEnd_200355 : Nat := 4983230072969 + 3 ^ 40 * 200355 * 2
def baseEnd_200355 : Nat := 60964987574322277831757

theorem tailTrace_200355 : CollatzResearch.WordTrace tailWord_200355 prefixEnd_200355 60964987574322277831757 := by
  unfold tailWord_200355
  simp only [CollatzResearch.WordTrace]
  refine ⟨7307547189155527754882519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4871698126103685169921679 7307547189155527754882519)
  ·
    refine ⟨10961320783733291632323779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7307547189155527754882519 10961320783733291632323779)
    ·
      refine ⟨16441981175599937448485669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10961320783733291632323779 16441981175599937448485669)
      ·
        refine ⟨3082871470424988271591063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 16441981175599937448485669 3082871470424988271591063)
        ·
          refine ⟨4624307205637482407386595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3082871470424988271591063 4624307205637482407386595)
          ·
            refine ⟨6936460808456223611079893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4624307205637482407386595 6936460808456223611079893)
            ·
              refine ⟨162573300198192740884685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 6936460808456223611079893 162573300198192740884685)
              ·
                refine ⟨60964987574322277831757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 162573300198192740884685 60964987574322277831757)
                ·
                  rfl

theorem cell19_200355_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 7, 3].length) (baseStart_200355 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_200355 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_200355 prefixEnd_200355 := by exact prefixLift 200355
  have htrace : WordTrace (prefixWord ++ tailWord_200355) baseStart_200355 baseEnd_200355 := by
    simpa [prefixWord, tailWord_200355, baseEnd_200355] using wordTrace_append hprefix tailTrace_200355
  have hstable : (prefixWord ++ tailWord_200355).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_200355).length < 2 ^ (prefixWord ++ tailWord_200355).sum := by decide
  have hdescent : baseEnd_200355 < baseStart_200355 := by decide
  rcases family_descends (prefixWord ++ tailWord_200355) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_200357 : List Nat := [1, 3, 1, 2, 1, 2, 2, 7]
def baseStart_200357 : Nat := 118140960795 + 200357 * 2 ^ 59
def prefixEnd_200357 : Nat := 4983230072969 + 3 ^ 40 * 200357 * 2
def baseEnd_200357 : Nat := 60965596143986865787307

theorem tailTrace_200357 : CollatzResearch.WordTrace tailWord_200357 prefixEnd_200357 60965596143986865787307 := by
  unfold tailWord_200357
  simp only [CollatzResearch.WordTrace]
  refine ⟨7307620135148282096455325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4871746756765521397636883 7307620135148282096455325)
  ·
    refine ⟨2740357550680605786170747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7307620135148282096455325 2740357550680605786170747)
    ·
      refine ⟨4110536326020908679256121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2740357550680605786170747 4110536326020908679256121)
      ·
        refine ⟨3082902244515681509442091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4110536326020908679256121 3082902244515681509442091)
        ·
          refine ⟨4624353366773522264163137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3082902244515681509442091 4624353366773522264163137)
          ·
            refine ⟨3468265025080141698122353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4624353366773522264163137 3468265025080141698122353)
            ·
              refine ⟨2601198768810106273591765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3468265025080141698122353 2601198768810106273591765)
              ·
                refine ⟨60965596143986865787307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2601198768810106273591765 60965596143986865787307)
                ·
                  rfl

theorem cell19_200357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 2, 7].length) (baseStart_200357 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_200357 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_200357 prefixEnd_200357 := by exact prefixLift 200357
  have htrace : WordTrace (prefixWord ++ tailWord_200357) baseStart_200357 baseEnd_200357 := by
    simpa [prefixWord, tailWord_200357, baseEnd_200357] using wordTrace_append hprefix tailTrace_200357
  have hstable : (prefixWord ++ tailWord_200357).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_200357).length < 2 ^ (prefixWord ++ tailWord_200357).sum := by decide
  have hdescent : baseEnd_200357 < baseStart_200357 := by decide
  rcases family_descends (prefixWord ++ tailWord_200357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_200410 : List Nat := [3, 1, 1, 2, 2, 5, 2, 3]
def baseStart_200410 : Nat := 118140960795 + 200410 * 2 ^ 59
def prefixEnd_200410 : Nat := 4983230072969 + 3 ^ 40 * 200410 * 2
def baseEnd_200410 : Nat := 60981723240098446609385

theorem tailTrace_200410 : CollatzResearch.WordTrace tailWord_200410 prefixEnd_200410 60981723240098446609385 := by
  unfold tailWord_200410
  simp only [CollatzResearch.WordTrace]
  refine ⟨1827388300989068037033671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4873035469304181432089789 1827388300989068037033671)
  ·
    refine ⟨2741082451483602055550507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1827388300989068037033671 2741082451483602055550507)
    ·
      refine ⟨4111623677225403083325761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2741082451483602055550507 4111623677225403083325761)
      ·
        refine ⟨3083717757919052312494321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4111623677225403083325761 3083717757919052312494321)
        ·
          refine ⟨2312788318439289234370741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3083717757919052312494321 2312788318439289234370741)
          ·
            refine ⟨216823904853683365722257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 2312788318439289234370741 216823904853683365722257)
            ·
              refine ⟨162617928640262524291693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 216823904853683365722257 162617928640262524291693)
              ·
                refine ⟨60981723240098446609385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 162617928640262524291693 60981723240098446609385)
                ·
                  rfl

theorem cell19_200410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 5, 2, 3].length) (baseStart_200410 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_200410 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_200410 prefixEnd_200410 := by exact prefixLift 200410
  have htrace : WordTrace (prefixWord ++ tailWord_200410) baseStart_200410 baseEnd_200410 := by
    simpa [prefixWord, tailWord_200410, baseEnd_200410] using wordTrace_append hprefix tailTrace_200410
  have hstable : (prefixWord ++ tailWord_200410).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_200410).length < 2 ^ (prefixWord ++ tailWord_200410).sum := by decide
  have hdescent : baseEnd_200410 < baseStart_200410 := by decide
  rcases family_descends (prefixWord ++ tailWord_200410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_200433 : List Nat := [1, 2, 2, 2, 2, 3, 7]
def baseStart_200433 : Nat := 118140960795 + 200433 * 2 ^ 59
def prefixEnd_200433 : Nat := 4983230072969 + 3 ^ 40 * 200433 * 2
def baseEnd_200433 : Nat := 20329573930413736032737

theorem tailTrace_200433 : CollatzResearch.WordTrace tailWord_200433 prefixEnd_200433 20329573930413736032737 := by
  unfold tailWord_200433
  simp only [CollatzResearch.WordTrace]
  refine ⟨7310392082872947076221953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4873594721915298050814635 7310392082872947076221953)
  ·
    refine ⟨5482794062154710307166465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7310392082872947076221953 5482794062154710307166465)
    ·
      refine ⟨4112095546616032730374849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5482794062154710307166465 4112095546616032730374849)
      ·
        refine ⟨3084071659962024547781137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4112095546616032730374849 3084071659962024547781137)
        ·
          refine ⟨2313053744971518410835853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3084071659962024547781137 2313053744971518410835853)
          ·
            refine ⟨867395154364319404063445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2313053744971518410835853 867395154364319404063445)
            ·
              refine ⟨20329573930413736032737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 867395154364319404063445 20329573930413736032737)
              ·
                rfl

theorem cell19_200433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 7].length) (baseStart_200433 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_200433 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_200433 prefixEnd_200433 := by exact prefixLift 200433
  have htrace : WordTrace (prefixWord ++ tailWord_200433) baseStart_200433 baseEnd_200433 := by
    simpa [prefixWord, tailWord_200433, baseEnd_200433] using wordTrace_append hprefix tailTrace_200433
  have hstable : (prefixWord ++ tailWord_200433).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_200433).length < 2 ^ (prefixWord ++ tailWord_200433).sum := by decide
  have hdescent : baseEnd_200433 < baseStart_200433 := by decide
  rcases family_descends (prefixWord ++ tailWord_200433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_200490 : List Nat := [3, 1, 4, 11]
def baseStart_200490 : Nat := 118140960795 + 200490 * 2 ^ 59
def prefixEnd_200490 : Nat := 4983230072969 + 3 ^ 40 * 200490 * 2
def baseEnd_200490 : Nat := 753161308971382281869

theorem tailTrace_200490 : CollatzResearch.WordTrace tailWord_200490 prefixEnd_200490 753161308971382281869 := by
  unfold tailWord_200490
  simp only [CollatzResearch.WordTrace]
  refine ⟨1828117760916611452761731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4874980695777630540697949 1828117760916611452761731)
  ·
    refine ⟨2742176641374917179142597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1828117760916611452761731 2742176641374917179142597)
    ·
      refine ⟨514158120257796971089237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2742176641374917179142597 514158120257796971089237)
      ·
        refine ⟨753161308971382281869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 11 514158120257796971089237 753161308971382281869)
        ·
          rfl

theorem cell19_200490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 11].length) (baseStart_200490 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_200490 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_200490 prefixEnd_200490 := by exact prefixLift 200490
  have htrace : WordTrace (prefixWord ++ tailWord_200490) baseStart_200490 baseEnd_200490 := by
    simpa [prefixWord, tailWord_200490, baseEnd_200490] using wordTrace_append hprefix tailTrace_200490
  have hstable : (prefixWord ++ tailWord_200490).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_200490).length < 2 ^ (prefixWord ++ tailWord_200490).sum := by decide
  have hdescent : baseEnd_200490 < baseStart_200490 := by decide
  rcases family_descends (prefixWord ++ tailWord_200490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_200524 : List Nat := [2, 2, 1, 3, 4, 1, 3, 3]
def baseStart_200524 : Nat := 118140960795 + 200524 * 2 ^ 59
def prefixEnd_200524 : Nat := 4983230072969 + 3 ^ 40 * 200524 * 2
def baseEnd_200524 : Nat := 61016411710979960075741

theorem tailTrace_200524 : CollatzResearch.WordTrace tailWord_200524 prefixEnd_200524 61016411710979960075741 := by
  unfold tailWord_200524
  simp only [CollatzResearch.WordTrace]
  refine ⟨3656855562771634808892313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4875807417028846411856417 3656855562771634808892313)
  ·
    refine ⟨2742641672078726106669235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3656855562771634808892313 2742641672078726106669235)
    ·
      refine ⟨4113962508118089160003853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2742641672078726106669235 4113962508118089160003853)
      ·
        refine ⟨1542735940544283435001445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4113962508118089160003853 1542735940544283435001445)
        ·
          refine ⟨289262988852053144062771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1542735940544283435001445 289262988852053144062771)
          ·
            refine ⟨433894483278079716094157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 289262988852053144062771 433894483278079716094157)
            ·
              refine ⟨162710431229279893535309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 433894483278079716094157 162710431229279893535309)
              ·
                refine ⟨61016411710979960075741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 162710431229279893535309 61016411710979960075741)
                ·
                  rfl

theorem cell19_200524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 4, 1, 3, 3].length) (baseStart_200524 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_200524 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_200524 prefixEnd_200524 := by exact prefixLift 200524
  have htrace : WordTrace (prefixWord ++ tailWord_200524) baseStart_200524 baseEnd_200524 := by
    simpa [prefixWord, tailWord_200524, baseEnd_200524] using wordTrace_append hprefix tailTrace_200524
  have hstable : (prefixWord ++ tailWord_200524).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_200524).length < 2 ^ (prefixWord ++ tailWord_200524).sum := by decide
  have hdescent : baseEnd_200524 < baseStart_200524 := by decide
  rcases family_descends (prefixWord ++ tailWord_200524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_200577 : List Nat := [1, 2, 4, 4, 2, 1, 2, 3]
def baseStart_200577 : Nat := 118140960795 + 200577 * 2 ^ 59
def prefixEnd_200577 : Nat := 4983230072969 + 3 ^ 40 * 200577 * 2
def baseEnd_200577 : Nat := 61032538807091540897819

theorem tailTrace_200577 : CollatzResearch.WordTrace tailWord_200577 prefixEnd_200577 61032538807091540897819 := by
  unfold tailWord_200577
  simp only [CollatzResearch.WordTrace]
  refine ⟨7315644194351259669463985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4877096129567506446309323 7315644194351259669463985)
  ·
    refine ⟨5486733145763444752097989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7315644194351259669463985 5486733145763444752097989)
    ·
      refine ⟨1028762464830645891018373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5486733145763444752097989 1028762464830645891018373)
      ·
        refine ⟨192892962155746104565945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1028762464830645891018373 192892962155746104565945)
        ·
          refine ⟨144669721616809578424459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 192892962155746104565945 144669721616809578424459)
          ·
            refine ⟨217004582425214367636689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 144669721616809578424459 217004582425214367636689)
            ·
              refine ⟨162753436818910775727517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 217004582425214367636689 162753436818910775727517)
              ·
                refine ⟨61032538807091540897819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 162753436818910775727517 61032538807091540897819)
                ·
                  rfl

theorem cell19_200577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 2, 1, 2, 3].length) (baseStart_200577 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_200577 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_200577 prefixEnd_200577 := by exact prefixLift 200577
  have htrace : WordTrace (prefixWord ++ tailWord_200577) baseStart_200577 baseEnd_200577 := by
    simpa [prefixWord, tailWord_200577, baseEnd_200577] using wordTrace_append hprefix tailTrace_200577
  have hstable : (prefixWord ++ tailWord_200577).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_200577).length < 2 ^ (prefixWord ++ tailWord_200577).sum := by decide
  have hdescent : baseEnd_200577 < baseStart_200577 := by decide
  rcases family_descends (prefixWord ++ tailWord_200577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_200583 : List Nat := [1, 1, 4, 2, 4, 1, 1, 5]
def baseStart_200583 : Nat := 118140960795 + 200583 * 2 ^ 59
def prefixEnd_200583 : Nat := 4983230072969 + 3 ^ 40 * 200583 * 2
def baseEnd_200583 : Nat := 61034364516085304764469

theorem tailTrace_200583 : CollatzResearch.WordTrace tailWord_200583 prefixEnd_200583 61034364516085304764469 := by
  unfold tailWord_200583
  simp only [CollatzResearch.WordTrace]
  refine ⟨7315863032329522694182403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4877242021553015129454935 7315863032329522694182403)
  ·
    refine ⟨10973794548494284041273605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7315863032329522694182403 10973794548494284041273605)
    ·
      refine ⟨2057586477842678257738801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10973794548494284041273605 2057586477842678257738801)
      ·
        refine ⟨1543189858382008693304101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2057586477842678257738801 1543189858382008693304101)
        ·
          refine ⟨289348098446626629994519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1543189858382008693304101 289348098446626629994519)
          ·
            refine ⟨434022147669939944991779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 289348098446626629994519 434022147669939944991779)
            ·
              refine ⟨651033221504909917487669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 434022147669939944991779 651033221504909917487669)
              ·
                refine ⟨61034364516085304764469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 651033221504909917487669 61034364516085304764469)
                ·
                  rfl

theorem cell19_200583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 4, 1, 1, 5].length) (baseStart_200583 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_200583 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_200583 prefixEnd_200583 := by exact prefixLift 200583
  have htrace : WordTrace (prefixWord ++ tailWord_200583) baseStart_200583 baseEnd_200583 := by
    simpa [prefixWord, tailWord_200583, baseEnd_200583] using wordTrace_append hprefix tailTrace_200583
  have hstable : (prefixWord ++ tailWord_200583).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_200583).length < 2 ^ (prefixWord ++ tailWord_200583).sum := by decide
  have hdescent : baseEnd_200583 < baseStart_200583 := by decide
  rcases family_descends (prefixWord ++ tailWord_200583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_200585 : List Nat := [1, 2, 1, 1, 5, 1, 3, 5]
def baseStart_200585 : Nat := 118140960795 + 200585 * 2 ^ 59
def prefixEnd_200585 : Nat := 4983230072969 + 3 ^ 40 * 200585 * 2
def baseEnd_200585 : Nat := 61034973085749892720019

theorem tailTrace_200585 : CollatzResearch.WordTrace tailWord_200585 prefixEnd_200585 61034973085749892720019 := by
  unfold tailWord_200585
  simp only [CollatzResearch.WordTrace]
  refine ⟨7315935978322277035755209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4877290652214851357170139 7315935978322277035755209)
  ·
    refine ⟨5486951983741707776816407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7315935978322277035755209 5486951983741707776816407)
    ·
      refine ⟨8230427975612561665224611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5486951983741707776816407 8230427975612561665224611)
      ·
        refine ⟨12345641963418842497836917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8230427975612561665224611 12345641963418842497836917)
        ·
          refine ⟨1157403934070516484172211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 12345641963418842497836917 1157403934070516484172211)
          ·
            refine ⟨1736105901105774726258317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1157403934070516484172211 1736105901105774726258317)
            ·
              refine ⟨651039712914665522346869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1736105901105774726258317 651039712914665522346869)
              ·
                refine ⟨61034973085749892720019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 651039712914665522346869 61034973085749892720019)
                ·
                  rfl

theorem cell19_200585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 3, 5].length) (baseStart_200585 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_200585 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_200585 prefixEnd_200585 := by exact prefixLift 200585
  have htrace : WordTrace (prefixWord ++ tailWord_200585) baseStart_200585 baseEnd_200585 := by
    simpa [prefixWord, tailWord_200585, baseEnd_200585] using wordTrace_append hprefix tailTrace_200585
  have hstable : (prefixWord ++ tailWord_200585).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_200585).length < 2 ^ (prefixWord ++ tailWord_200585).sum := by decide
  have hdescent : baseEnd_200585 < baseStart_200585 := by decide
  rcases family_descends (prefixWord ++ tailWord_200585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_200600 : List Nat := [2, 1, 2, 6, 1, 2, 5]
def baseStart_200600 : Nat := 118140960795 + 200600 * 2 ^ 59
def prefixEnd_200600 : Nat := 4983230072969 + 3 ^ 40 * 200600 * 2
def baseEnd_200600 : Nat := 20346512452744767462215

theorem tailTrace_200600 : CollatzResearch.WordTrace tailWord_200600 prefixEnd_200600 20346512452744767462215 := by
  unfold tailWord_200600
  simp only [CollatzResearch.WordTrace]
  refine ⟨3658241536633967298775627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4877655382178623065034169 3658241536633967298775627)
  ·
    refine ⟨5487362304950950948163441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3658241536633967298775627 5487362304950950948163441)
    ·
      refine ⟨4115521728713213211122581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5487362304950950948163441 4115521728713213211122581)
      ·
        refine ⟨192915081033431869271371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 4115521728713213211122581 192915081033431869271371)
        ·
          refine ⟨289372621550147803907057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 192915081033431869271371 289372621550147803907057)
          ·
            refine ⟨217029466162610852930293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 289372621550147803907057 217029466162610852930293)
            ·
              refine ⟨20346512452744767462215, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 217029466162610852930293 20346512452744767462215)
              ·
                rfl

theorem cell19_200600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 1, 2, 5].length) (baseStart_200600 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_200600 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_200600 prefixEnd_200600 := by exact prefixLift 200600
  have htrace : WordTrace (prefixWord ++ tailWord_200600) baseStart_200600 baseEnd_200600 := by
    simpa [prefixWord, tailWord_200600, baseEnd_200600] using wordTrace_append hprefix tailTrace_200600
  have hstable : (prefixWord ++ tailWord_200600).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_200600).length < 2 ^ (prefixWord ++ tailWord_200600).sum := by decide
  have hdescent : baseEnd_200600 < baseStart_200600 := by decide
  rcases family_descends (prefixWord ++ tailWord_200600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_200602 : List Nat := [3, 1, 1, 4, 2, 3, 5]
def baseStart_200602 : Nat := 118140960795 + 200602 * 2 ^ 59
def prefixEnd_200602 : Nat := 4983230072969 + 3 ^ 40 * 200602 * 2
def baseEnd_200602 : Nat := 20346715309299630114065

theorem tailTrace_200602 : CollatzResearch.WordTrace tailWord_200602 prefixEnd_200602 20346715309299630114065 := by
  unfold tailWord_200602
  simp only [CollatzResearch.WordTrace]
  refine ⟨1829139004815172234781015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4877704012840459292749373 1829139004815172234781015)
  ·
    refine ⟨2743708507222758352171523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1829139004815172234781015 2743708507222758352171523)
    ·
      refine ⟨4115562760834137528257285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2743708507222758352171523 4115562760834137528257285)
      ·
        refine ⟨771668017656400786548241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4115562760834137528257285 771668017656400786548241)
        ·
          refine ⟨578751013242300589911181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 771668017656400786548241 578751013242300589911181)
          ·
            refine ⟨217031629965862721216693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 578751013242300589911181 217031629965862721216693)
            ·
              refine ⟨20346715309299630114065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 217031629965862721216693 20346715309299630114065)
              ·
                rfl

theorem cell19_200602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 3, 5].length) (baseStart_200602 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_200602 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_200602 prefixEnd_200602 := by exact prefixLift 200602
  have htrace : WordTrace (prefixWord ++ tailWord_200602) baseStart_200602 baseEnd_200602 := by
    simpa [prefixWord, tailWord_200602, baseEnd_200602] using wordTrace_append hprefix tailTrace_200602
  have hstable : (prefixWord ++ tailWord_200602).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_200602).length < 2 ^ (prefixWord ++ tailWord_200602).sum := by decide
  have hdescent : baseEnd_200602 < baseStart_200602 := by decide
  rcases family_descends (prefixWord ++ tailWord_200602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_200623 : List Nat := [1, 1, 2, 1, 2, 2, 6, 4]
def baseStart_200623 : Nat := 118140960795 + 200623 * 2 ^ 59
def prefixEnd_200623 : Nat := 4983230072969 + 3 ^ 40 * 200623 * 2
def baseEnd_200623 : Nat := 61046535909377063875471

theorem tailTrace_200623 : CollatzResearch.WordTrace tailWord_200623 prefixEnd_200623 61046535909377063875471 := by
  unfold tailWord_200623
  simp only [CollatzResearch.WordTrace]
  refine ⟨7317321952184609525638523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4878214634789739683759015 7317321952184609525638523)
  ·
    refine ⟨10975982928276914288457785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7317321952184609525638523 10975982928276914288457785)
    ·
      refine ⟨8231987196207685716343339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10975982928276914288457785 8231987196207685716343339)
      ·
        refine ⟨12347980794311528574515009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8231987196207685716343339 12347980794311528574515009)
        ·
          refine ⟨9260985595733646430886257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12347980794311528574515009 9260985595733646430886257)
          ·
            refine ⟨6945739196800234823164693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9260985595733646430886257 6945739196800234823164693)
            ·
              refine ⟨325581524850011007335845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 6945739196800234823164693 325581524850011007335845)
              ·
                refine ⟨61046535909377063875471, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 325581524850011007335845 61046535909377063875471)
                ·
                  rfl

theorem cell19_200623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 6, 4].length) (baseStart_200623 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_200623 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_200623 prefixEnd_200623 := by exact prefixLift 200623
  have htrace : WordTrace (prefixWord ++ tailWord_200623) baseStart_200623 baseEnd_200623 := by
    simpa [prefixWord, tailWord_200623, baseEnd_200623] using wordTrace_append hprefix tailTrace_200623
  have hstable : (prefixWord ++ tailWord_200623).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_200623).length < 2 ^ (prefixWord ++ tailWord_200623).sum := by decide
  have hdescent : baseEnd_200623 < baseStart_200623 := by decide
  rcases family_descends (prefixWord ++ tailWord_200623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_200661 : List Nat := [1, 3, 2, 3, 2, 8]
def baseStart_200661 : Nat := 118140960795 + 200661 * 2 ^ 59
def prefixEnd_200661 : Nat := 4983230072969 + 3 ^ 40 * 200661 * 2
def baseEnd_200661 : Nat := 6784233192556026114547

theorem tailTrace_200661 : CollatzResearch.WordTrace tailWord_200661 prefixEnd_200661 6784233192556026114547 := by
  unfold tailWord_200661
  simp only [CollatzResearch.WordTrace]
  refine ⟨7318707926046942015521837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4879138617364628010347891 7318707926046942015521837)
  ·
    refine ⟨2744515472267603255820689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7318707926046942015521837 2744515472267603255820689)
    ·
      refine ⟨2058386604200702441865517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2744515472267603255820689 2058386604200702441865517)
      ·
        refine ⟨771894976575263415699569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2058386604200702441865517 771894976575263415699569)
        ·
          refine ⟨578921232431447561774677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 771894976575263415699569 578921232431447561774677)
          ·
            refine ⟨6784233192556026114547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 578921232431447561774677 6784233192556026114547)
            ·
              rfl

theorem cell19_200661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 8].length) (baseStart_200661 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_200661 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_200661 prefixEnd_200661 := by exact prefixLift 200661
  have htrace : WordTrace (prefixWord ++ tailWord_200661) baseStart_200661 baseEnd_200661 := by
    simpa [prefixWord, tailWord_200661, baseEnd_200661] using wordTrace_append hprefix tailTrace_200661
  have hstable : (prefixWord ++ tailWord_200661).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_200661).length < 2 ^ (prefixWord ++ tailWord_200661).sum := by decide
  have hdescent : baseEnd_200661 < baseStart_200661 := by decide
  rcases family_descends (prefixWord ++ tailWord_200661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_200674 : List Nat := [3, 3, 3, 1, 2, 2, 1, 4]
def baseStart_200674 : Nat := 118140960795 + 200674 * 2 ^ 59
def prefixEnd_200674 : Nat := 4983230072969 + 3 ^ 40 * 200674 * 2
def baseEnd_200674 : Nat := 61062054435824056741999

theorem tailTrace_200674 : CollatzResearch.WordTrace tailWord_200674 prefixEnd_200674 61062054435824056741999 := by
  unfold tailWord_200674
  simp only [CollatzResearch.WordTrace]
  refine ⟨1829795518749961308936269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4879454716666563490496717 1829795518749961308936269)
  ·
    refine ⟨686173319531235490851101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1829795518749961308936269 686173319531235490851101)
    ·
      refine ⟨257314994824213309069163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 686173319531235490851101 257314994824213309069163)
      ·
        refine ⟨385972492236319963603745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 257314994824213309069163 385972492236319963603745)
        ·
          refine ⟨289479369177239972702809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 385972492236319963603745 289479369177239972702809)
          ·
            refine ⟨217109526882929979527107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 289479369177239972702809 217109526882929979527107)
            ·
              refine ⟨325664290324394969290661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 217109526882929979527107 325664290324394969290661)
              ·
                refine ⟨61062054435824056741999, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 325664290324394969290661 61062054435824056741999)
                ·
                  rfl

theorem cell19_200674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 2, 2, 1, 4].length) (baseStart_200674 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_200674 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_200674 prefixEnd_200674 := by exact prefixLift 200674
  have htrace : WordTrace (prefixWord ++ tailWord_200674) baseStart_200674 baseEnd_200674 := by
    simpa [prefixWord, tailWord_200674, baseEnd_200674] using wordTrace_append hprefix tailTrace_200674
  have hstable : (prefixWord ++ tailWord_200674).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_200674).length < 2 ^ (prefixWord ++ tailWord_200674).sum := by decide
  have hdescent : baseEnd_200674 < baseStart_200674 := by decide
  rcases family_descends (prefixWord ++ tailWord_200674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_200697 : List Nat := [1, 2, 1, 3, 1, 5, 3, 3]
def baseStart_200697 : Nat := 118140960795 + 200697 * 2 ^ 59
def prefixEnd_200697 : Nat := 4983230072969 + 3 ^ 40 * 200697 * 2
def baseEnd_200697 : Nat := 61069052986966818230825

theorem tailTrace_200697 : CollatzResearch.WordTrace tailWord_200697 prefixEnd_200697 61069052986966818230825 := by
  unfold tailWord_200697
  simp only [CollatzResearch.WordTrace]
  refine ⟨7320020953916520163832345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4880013969277680109221563 7320020953916520163832345)
  ·
    refine ⟨5490015715437390122874259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7320020953916520163832345 5490015715437390122874259)
    ·
      refine ⟨8235023573156085184311389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5490015715437390122874259 8235023573156085184311389)
      ·
        refine ⟨3088133839933531944116771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8235023573156085184311389 3088133839933531944116771)
        ·
          refine ⟨4632200759900297916175157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3088133839933531944116771 4632200759900297916175157)
          ·
            refine ⟨434268821240652929641421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 4632200759900297916175157 434268821240652929641421)
            ·
              refine ⟨162850807965244848615533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 434268821240652929641421 162850807965244848615533)
              ·
                refine ⟨61069052986966818230825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 162850807965244848615533 61069052986966818230825)
                ·
                  rfl

theorem cell19_200697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 5, 3, 3].length) (baseStart_200697 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_200697 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_200697 prefixEnd_200697 := by exact prefixLift 200697
  have htrace : WordTrace (prefixWord ++ tailWord_200697) baseStart_200697 baseEnd_200697 := by
    simpa [prefixWord, tailWord_200697, baseEnd_200697] using wordTrace_append hprefix tailTrace_200697
  have hstable : (prefixWord ++ tailWord_200697).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_200697).length < 2 ^ (prefixWord ++ tailWord_200697).sum := by decide
  have hdescent : baseEnd_200697 < baseStart_200697 := by decide
  rcases family_descends (prefixWord ++ tailWord_200697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_200710 : List Nat := [6, 2, 1, 2, 1, 1, 6]
def baseStart_200710 : Nat := 118140960795 + 200710 * 2 ^ 59
def prefixEnd_200710 : Nat := 4983230072969 + 3 ^ 40 * 200710 * 2
def baseEnd_200710 : Nat := 20357669563262213313967

theorem tailTrace_200710 : CollatzResearch.WordTrace tailWord_200710 prefixEnd_200710 20357669563262213313967 := by
  unfold tailWord_200710
  simp only [CollatzResearch.WordTrace]
  refine ⟨228765471964669480751737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 4880330068579615589370389 228765471964669480751737)
  ·
    refine ⟨171574103973502110563803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 228765471964669480751737 171574103973502110563803)
    ·
      refine ⟨257361155960253165845705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 171574103973502110563803 257361155960253165845705)
      ·
        refine ⟨193020866970189874384279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 257361155960253165845705 193020866970189874384279)
        ·
          refine ⟨289531300455284811576419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 193020866970189874384279 289531300455284811576419)
          ·
            refine ⟨434296950682927217364629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 289531300455284811576419 434296950682927217364629)
            ·
              refine ⟨20357669563262213313967, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 434296950682927217364629 20357669563262213313967)
              ·
                rfl

theorem cell19_200710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 1, 1, 6].length) (baseStart_200710 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_200710 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_200710 prefixEnd_200710 := by exact prefixLift 200710
  have htrace : WordTrace (prefixWord ++ tailWord_200710) baseStart_200710 baseEnd_200710 := by
    simpa [prefixWord, tailWord_200710, baseEnd_200710] using wordTrace_append hprefix tailTrace_200710
  have hstable : (prefixWord ++ tailWord_200710).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_200710).length < 2 ^ (prefixWord ++ tailWord_200710).sum := by decide
  have hdescent : baseEnd_200710 < baseStart_200710 := by decide
  rcases family_descends (prefixWord ++ tailWord_200710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_200718 : List Nat := [4, 1, 1, 2, 2, 1, 8]
def baseStart_200718 : Nat := 118140960795 + 200718 * 2 ^ 59
def prefixEnd_200718 : Nat := 4983230072969 + 3 ^ 40 * 200718 * 2
def baseEnd_200718 : Nat := 20358480989481663921367

theorem tailTrace_200718 : CollatzResearch.WordTrace tailWord_200718 prefixEnd_200718 20358480989481663921367 := by
  unfold tailWord_200718
  simp only [CollatzResearch.WordTrace]
  refine ⟨915098360855055093793351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 4880524591226960500231205 915098360855055093793351)
  ·
    refine ⟨1372647541282582640690027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 915098360855055093793351 1372647541282582640690027)
    ·
      refine ⟨2058971311923873961035041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1372647541282582640690027 2058971311923873961035041)
      ·
        refine ⟨1544228483942905470776281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2058971311923873961035041 1544228483942905470776281)
        ·
          refine ⟨1158171362957179103082211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1544228483942905470776281 1158171362957179103082211)
          ·
            refine ⟨1737257044435768654623317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1158171362957179103082211 1737257044435768654623317)
            ·
              refine ⟨20358480989481663921367, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1737257044435768654623317 20358480989481663921367)
              ·
                rfl

theorem cell19_200718_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 8].length) (baseStart_200718 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_200718 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_200718 prefixEnd_200718 := by exact prefixLift 200718
  have htrace : WordTrace (prefixWord ++ tailWord_200718) baseStart_200718 baseEnd_200718 := by
    simpa [prefixWord, tailWord_200718, baseEnd_200718] using wordTrace_append hprefix tailTrace_200718
  have hstable : (prefixWord ++ tailWord_200718).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_200718).length < 2 ^ (prefixWord ++ tailWord_200718).sum := by decide
  have hdescent : baseEnd_200718 < baseStart_200718 := by decide
  rcases family_descends (prefixWord ++ tailWord_200718) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_200754 : List Nat := [3, 2, 1, 1, 2, 3, 4, 3]
def baseStart_200754 : Nat := 118140960795 + 200754 * 2 ^ 59
def prefixEnd_200754 : Nat := 4983230072969 + 3 ^ 40 * 200754 * 2
def baseEnd_200754 : Nat := 61086397222407574964003

theorem tailTrace_200754 : CollatzResearch.WordTrace tailWord_200754 prefixEnd_200754 61086397222407574964003 := by
  unfold tailWord_200754
  simp only [CollatzResearch.WordTrace]
  refine ⟨1830524978677504724664329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4881399943140012599104877 1830524978677504724664329)
  ·
    refine ⟨1372893734008128543498247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1830524978677504724664329 1372893734008128543498247)
    ·
      refine ⟨2059340601012192815247371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1372893734008128543498247 2059340601012192815247371)
      ·
        refine ⟨3089010901518289222871057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2059340601012192815247371 3089010901518289222871057)
        ·
          refine ⟨2316758176138716917153293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3089010901518289222871057 2316758176138716917153293)
          ·
            refine ⟨868784316052018843932485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2316758176138716917153293 868784316052018843932485)
            ·
              refine ⟨162897059259753533237341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 868784316052018843932485 162897059259753533237341)
              ·
                refine ⟨61086397222407574964003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 162897059259753533237341 61086397222407574964003)
                ·
                  rfl

theorem cell19_200754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 4, 3].length) (baseStart_200754 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_200754 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_200754 prefixEnd_200754 := by exact prefixLift 200754
  have htrace : WordTrace (prefixWord ++ tailWord_200754) baseStart_200754 baseEnd_200754 := by
    simpa [prefixWord, tailWord_200754, baseEnd_200754] using wordTrace_append hprefix tailTrace_200754
  have hstable : (prefixWord ++ tailWord_200754).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_200754).length < 2 ^ (prefixWord ++ tailWord_200754).sum := by decide
  have hdescent : baseEnd_200754 < baseStart_200754 := by decide
  rcases family_descends (prefixWord ++ tailWord_200754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_200790 : List Nat := [5, 2, 2, 1, 1, 1, 1, 6]
def baseStart_200790 : Nat := 118140960795 + 200790 * 2 ^ 59
def prefixEnd_200790 : Nat := 4983230072969 + 3 ^ 40 * 200790 * 2
def baseEnd_200790 : Nat := 61097351476370158163905

theorem tailTrace_200790 : CollatzResearch.WordTrace tailWord_200790 prefixEnd_200790 61097351476370158163905 := by
  unfold tailWord_200790
  simp only [CollatzResearch.WordTrace]
  refine ⟨457713308911224815435489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 4882275295053064697978549 457713308911224815435489)
  ·
    refine ⟨343284981683418611576617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 457713308911224815435489 343284981683418611576617)
    ·
      refine ⟨257463736262563958682463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 343284981683418611576617 257463736262563958682463)
      ·
        refine ⟨386195604393845938023695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 257463736262563958682463 386195604393845938023695)
        ·
          refine ⟨579293406590768907035543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 386195604393845938023695 579293406590768907035543)
          ·
            refine ⟨868940109886153360553315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 579293406590768907035543 868940109886153360553315)
            ·
              refine ⟨1303410164829230040829973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 868940109886153360553315 1303410164829230040829973)
              ·
                refine ⟨61097351476370158163905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1303410164829230040829973 61097351476370158163905)
                ·
                  rfl

theorem cell19_200790_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 1, 6].length) (baseStart_200790 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_200790 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_200790 prefixEnd_200790 := by exact prefixLift 200790
  have htrace : WordTrace (prefixWord ++ tailWord_200790) baseStart_200790 baseEnd_200790 := by
    simpa [prefixWord, tailWord_200790, baseEnd_200790] using wordTrace_append hprefix tailTrace_200790
  have hstable : (prefixWord ++ tailWord_200790).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_200790).length < 2 ^ (prefixWord ++ tailWord_200790).sum := by decide
  have hdescent : baseEnd_200790 < baseStart_200790 := by decide
  rcases family_descends (prefixWord ++ tailWord_200790) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_200794 : List Nat := [3, 1, 1, 2, 1, 1, 6, 4]
def baseStart_200794 : Nat := 118140960795 + 200794 * 2 ^ 59
def prefixEnd_200794 : Nat := 4983230072969 + 3 ^ 40 * 200794 * 2
def baseEnd_200794 : Nat := 61098568615699334075005

theorem tailTrace_200794 : CollatzResearch.WordTrace tailWord_200794 prefixEnd_200794 61098568615699334075005 := by
  unfold tailWord_200794
  simp only [CollatzResearch.WordTrace]
  refine ⟨1830889708641276432528359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4882372556376737153408957 1830889708641276432528359)
  ·
    refine ⟨2746334562961914648792539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1830889708641276432528359 2746334562961914648792539)
    ·
      refine ⟨4119501844442871973188809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2746334562961914648792539 4119501844442871973188809)
      ·
        refine ⟨3089626383332153979891607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4119501844442871973188809 3089626383332153979891607)
        ·
          refine ⟨4634439574998230969837411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3089626383332153979891607 4634439574998230969837411)
          ·
            refine ⟨6951659362497346454756117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4634439574998230969837411 6951659362497346454756117)
            ·
              refine ⟨325859032617063115066693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 6951659362497346454756117 325859032617063115066693)
              ·
                refine ⟨61098568615699334075005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 325859032617063115066693 61098568615699334075005)
                ·
                  rfl

theorem cell19_200794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 6, 4].length) (baseStart_200794 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_200794 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_200794 prefixEnd_200794 := by exact prefixLift 200794
  have htrace : WordTrace (prefixWord ++ tailWord_200794) baseStart_200794 baseEnd_200794 := by
    simpa [prefixWord, tailWord_200794, baseEnd_200794] using wordTrace_append hprefix tailTrace_200794
  have hstable : (prefixWord ++ tailWord_200794).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_200794).length < 2 ^ (prefixWord ++ tailWord_200794).sum := by decide
  have hdescent : baseEnd_200794 < baseStart_200794 := by decide
  rcases family_descends (prefixWord ++ tailWord_200794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_200813 : List Nat := [1, 5, 1, 1, 2, 1, 1, 7]
def baseStart_200813 : Nat := 118140960795 + 200813 * 2 ^ 59
def prefixEnd_200813 : Nat := 4983230072969 + 3 ^ 40 * 200813 * 2
def baseEnd_200813 : Nat := 61104350027512919652731

theorem tailTrace_200813 : CollatzResearch.WordTrace tailWord_200813 prefixEnd_200813 61104350027512919652731 := by
  unfold tailWord_200813
  simp only [CollatzResearch.WordTrace]
  refine ⟨7324251821496271975055093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4882834547664181316703395 7324251821496271975055093)
  ·
    refine ⟨686648608265275497661415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 7324251821496271975055093 686648608265275497661415)
    ·
      refine ⟨1029972912397913246492123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 686648608265275497661415 1029972912397913246492123)
      ·
        refine ⟨1544959368596869869738185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1029972912397913246492123 1544959368596869869738185)
        ·
          refine ⟨1158719526447652402303639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1544959368596869869738185 1158719526447652402303639)
          ·
            refine ⟨1738079289671478603455459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1158719526447652402303639 1738079289671478603455459)
            ·
              refine ⟨2607118934507217905183189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1738079289671478603455459 2607118934507217905183189)
              ·
                refine ⟨61104350027512919652731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2607118934507217905183189 61104350027512919652731)
                ·
                  rfl

theorem cell19_200813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 1, 7].length) (baseStart_200813 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_200813 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_200813 prefixEnd_200813 := by exact prefixLift 200813
  have htrace : WordTrace (prefixWord ++ tailWord_200813) baseStart_200813 baseEnd_200813 := by
    simpa [prefixWord, tailWord_200813, baseEnd_200813] using wordTrace_append hprefix tailTrace_200813
  have hstable : (prefixWord ++ tailWord_200813).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_200813).length < 2 ^ (prefixWord ++ tailWord_200813).sum := by decide
  have hdescent : baseEnd_200813 < baseStart_200813 := by decide
  rcases family_descends (prefixWord ++ tailWord_200813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_200830 : List Nat := [4, 2, 4, 9]
def baseStart_200830 : Nat := 118140960795 + 200830 * 2 ^ 59
def prefixEnd_200830 : Nat := 4983230072969 + 3 ^ 40 * 200830 * 2
def baseEnd_200830 : Nat := 754438553946443423147

theorem tailTrace_200830 : CollatzResearch.WordTrace tailWord_200830 prefixEnd_200830 754438553946443423147 := by
  unfold tailWord_200830
  simp only [CollatzResearch.WordTrace]
  refine ⟨915608982804335484802993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 4883247908289789252282629 915608982804335484802993)
  ·
    refine ⟨686706737103251613602245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 915608982804335484802993 686706737103251613602245)
    ·
      refine ⟨128757513206859677550421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 686706737103251613602245 128757513206859677550421)
      ·
        refine ⟨754438553946443423147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 9 128757513206859677550421 754438553946443423147)
        ·
          rfl

theorem cell19_200830_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 9].length) (baseStart_200830 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_200830 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_200830 prefixEnd_200830 := by exact prefixLift 200830
  have htrace : WordTrace (prefixWord ++ tailWord_200830) baseStart_200830 baseEnd_200830 := by
    simpa [prefixWord, tailWord_200830, baseEnd_200830] using wordTrace_append hprefix tailTrace_200830
  have hstable : (prefixWord ++ tailWord_200830).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_200830).length < 2 ^ (prefixWord ++ tailWord_200830).sum := by decide
  have hdescent : baseEnd_200830 < baseStart_200830 := by decide
  rcases family_descends (prefixWord ++ tailWord_200830) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_200866 : List Nat := [3, 3, 1, 3, 1, 2, 3, 3]
def baseStart_200866 : Nat := 118140960795 + 200866 * 2 ^ 59
def prefixEnd_200866 : Nat := 4983230072969 + 3 ^ 40 * 200866 * 2
def baseEnd_200866 : Nat := 61120477123624500474809

theorem tailTrace_200866 : CollatzResearch.WordTrace tailWord_200866 prefixEnd_200866 61120477123624500474809 := by
  unfold tailWord_200866
  simp only [CollatzResearch.WordTrace]
  refine ⟨1831546222576065506683613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4884123260202841351156301 1831546222576065506683613)
  ·
    refine ⟨686829833466024565006355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1831546222576065506683613 686829833466024565006355)
    ·
      refine ⟨1030244750199036847509533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 686829833466024565006355 1030244750199036847509533)
      ·
        refine ⟨386341781324638817816075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1030244750199036847509533 386341781324638817816075)
        ·
          refine ⟨579512671986958226724113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 386341781324638817816075 579512671986958226724113)
          ·
            refine ⟨434634503990218670043085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 579512671986958226724113 434634503990218670043085)
            ·
              refine ⟨162987938996332001266157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 434634503990218670043085 162987938996332001266157)
              ·
                refine ⟨61120477123624500474809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 162987938996332001266157 61120477123624500474809)
                ·
                  rfl

theorem cell19_200866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 2, 3, 3].length) (baseStart_200866 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_200866 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_200866 prefixEnd_200866 := by exact prefixLift 200866
  have htrace : WordTrace (prefixWord ++ tailWord_200866) baseStart_200866 baseEnd_200866 := by
    simpa [prefixWord, tailWord_200866, baseEnd_200866] using wordTrace_append hprefix tailTrace_200866
  have hstable : (prefixWord ++ tailWord_200866).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_200866).length < 2 ^ (prefixWord ++ tailWord_200866).sum := by decide
  have hdescent : baseEnd_200866 < baseStart_200866 := by decide
  rcases family_descends (prefixWord ++ tailWord_200866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_200891 : List Nat := [1, 1, 1, 1, 1, 2, 12]
def baseStart_200891 : Nat := 118140960795 + 200891 * 2 ^ 59
def prefixEnd_200891 : Nat := 4983230072969 + 3 ^ 40 * 200891 * 2
def baseEnd_200891 : Nat := 20376028081477283306395

theorem tailTrace_200891 : CollatzResearch.WordTrace tailWord_200891 prefixEnd_200891 20376028081477283306395 := by
  unfold tailWord_200891
  simp only [CollatzResearch.WordTrace]
  refine ⟨7327096715213691296394527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4884731143475794197596351 7327096715213691296394527)
  ·
    refine ⟨10990645072820536944591791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7327096715213691296394527 10990645072820536944591791)
    ·
      refine ⟨16485967609230805416887687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10990645072820536944591791 16485967609230805416887687)
      ·
        refine ⟨24728951413846208125331531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16485967609230805416887687 24728951413846208125331531)
        ·
          refine ⟨37093427120769312187997297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24728951413846208125331531 37093427120769312187997297)
          ·
            refine ⟨27820070340576984140997973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37093427120769312187997297 27820070340576984140997973)
            ·
              refine ⟨20376028081477283306395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 12 27820070340576984140997973 20376028081477283306395)
              ·
                rfl

theorem cell19_200891_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 12].length) (baseStart_200891 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_200891 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_200891 prefixEnd_200891 := by exact prefixLift 200891
  have htrace : WordTrace (prefixWord ++ tailWord_200891) baseStart_200891 baseEnd_200891 := by
    simpa [prefixWord, tailWord_200891, baseEnd_200891] using wordTrace_append hprefix tailTrace_200891
  have hstable : (prefixWord ++ tailWord_200891).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_200891).length < 2 ^ (prefixWord ++ tailWord_200891).sum := by decide
  have hdescent : baseEnd_200891 < baseStart_200891 := by decide
  rcases family_descends (prefixWord ++ tailWord_200891) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_200925 : List Nat := [1, 4, 3, 2, 1, 2, 1, 5]
def baseStart_200925 : Nat := 118140960795 + 200925 * 2 ^ 59
def prefixEnd_200925 : Nat := 4983230072969 + 3 ^ 40 * 200925 * 2
def baseEnd_200925 : Nat := 61138429928729845163537

theorem tailTrace_200925 : CollatzResearch.WordTrace tailWord_200925 prefixEnd_200925 61138429928729845163537 := by
  unfold tailWord_200925
  simp only [CollatzResearch.WordTrace]
  refine ⟨7328336797090515103132229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4885557864727010068754819 7328336797090515103132229)
  ·
    refine ⟨1374063149454471581837293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7328336797090515103132229 1374063149454471581837293)
    ·
      refine ⟨515273681045426843188985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1374063149454471581837293 515273681045426843188985)
      ·
        refine ⟨386455260784070132391739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 515273681045426843188985 386455260784070132391739)
        ·
          refine ⟨579682891176105198587609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 386455260784070132391739 579682891176105198587609)
          ·
            refine ⟨434762168382078898940707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 579682891176105198587609 434762168382078898940707)
            ·
              refine ⟨652143252573118348411061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 434762168382078898940707 652143252573118348411061)
              ·
                refine ⟨61138429928729845163537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 652143252573118348411061 61138429928729845163537)
                ·
                  rfl

theorem cell19_200925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 2, 1, 5].length) (baseStart_200925 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_200925 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_200925 prefixEnd_200925 := by exact prefixLift 200925
  have htrace : WordTrace (prefixWord ++ tailWord_200925) baseStart_200925 baseEnd_200925 := by
    simpa [prefixWord, tailWord_200925, baseEnd_200925] using wordTrace_append hprefix tailTrace_200925
  have hstable : (prefixWord ++ tailWord_200925).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_200925).length < 2 ^ (prefixWord ++ tailWord_200925).sum := by decide
  have hdescent : baseEnd_200925 < baseStart_200925 := by decide
  rcases family_descends (prefixWord ++ tailWord_200925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_200946 : List Nat := [3, 2, 1, 3, 2, 1, 7]
def baseStart_200946 : Nat := 118140960795 + 200946 * 2 ^ 59
def prefixEnd_200946 : Nat := 4983230072969 + 3 ^ 40 * 200946 * 2
def baseEnd_200946 : Nat := 20381606636736006232271

theorem tailTrace_200946 : CollatzResearch.WordTrace tailWord_200946 prefixEnd_200946 20381606636736006232271 := by
  unfold tailWord_200946
  simp only [CollatzResearch.WordTrace]
  refine ⟨1832275682503608922411673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4886068486676290459764461 1832275682503608922411673)
  ·
    refine ⟨1374206761877706691808755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1832275682503608922411673 1374206761877706691808755)
    ·
      refine ⟨2061310142816560037713133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1374206761877706691808755 2061310142816560037713133)
      ·
        refine ⟨772991303556210014142425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2061310142816560037713133 772991303556210014142425)
        ·
          refine ⟨579743477667157510606819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 772991303556210014142425 579743477667157510606819)
          ·
            refine ⟨869615216500736265910229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 579743477667157510606819 869615216500736265910229)
            ·
              refine ⟨20381606636736006232271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 869615216500736265910229 20381606636736006232271)
              ·
                rfl

theorem cell19_200946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 7].length) (baseStart_200946 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_200946 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_200946 prefixEnd_200946 := by exact prefixLift 200946
  have htrace : WordTrace (prefixWord ++ tailWord_200946) baseStart_200946 baseEnd_200946 := by
    simpa [prefixWord, tailWord_200946, baseEnd_200946] using wordTrace_append hprefix tailTrace_200946
  have hstable : (prefixWord ++ tailWord_200946).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_200946).length < 2 ^ (prefixWord ++ tailWord_200946).sum := by decide
  have hdescent : baseEnd_200946 < baseStart_200946 := by decide
  rcases family_descends (prefixWord ++ tailWord_200946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_200999 : List Nat := [1, 1, 8, 1, 1, 7]
def baseStart_200999 : Nat := 118140960795 + 200999 * 2 ^ 59
def prefixEnd_200999 : Nat := 4983230072969 + 3 ^ 40 * 200999 * 2
def baseEnd_200999 : Nat := 6795660778479955502099

theorem tailTrace_200999 : CollatzResearch.WordTrace tailWord_200999 prefixEnd_200999 6795660778479955502099 := by
  unfold tailWord_200999
  simp only [CollatzResearch.WordTrace]
  refine ⟨7331035798822425741326051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4887357199214950494217367 7331035798822425741326051)
  ·
    refine ⟨10996553698233638611989077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7331035798822425741326051 10996553698233638611989077)
    ·
      refine ⟨128865863651175452484247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 8 10996553698233638611989077 128865863651175452484247)
      ·
        refine ⟨193298795476763178726371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 128865863651175452484247 193298795476763178726371)
        ·
          refine ⟨289948193215144768089557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 193298795476763178726371 289948193215144768089557)
          ·
            refine ⟨6795660778479955502099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 289948193215144768089557 6795660778479955502099)
            ·
              rfl

theorem cell19_200999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 1, 7].length) (baseStart_200999 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_200999 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_200999 prefixEnd_200999 := by exact prefixLift 200999
  have htrace : WordTrace (prefixWord ++ tailWord_200999) baseStart_200999 baseEnd_200999 := by
    simpa [prefixWord, tailWord_200999, baseEnd_200999] using wordTrace_append hprefix tailTrace_200999
  have hstable : (prefixWord ++ tailWord_200999).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_200999).length < 2 ^ (prefixWord ++ tailWord_200999).sum := by decide
  have hdescent : baseEnd_200999 < baseStart_200999 := by decide
  rcases family_descends (prefixWord ++ tailWord_200999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_201024 : List Nat := [2, 1, 1, 2, 2, 1, 2, 8]
def baseStart_201024 : Nat := 118140960795 + 201024 * 2 ^ 59
def prefixEnd_201024 : Nat := 4983230072969 + 3 ^ 40 * 201024 * 2
def baseEnd_201024 : Nat := 61168554127126948963267

theorem tailTrace_201024 : CollatzResearch.WordTrace tailWord_201024 prefixEnd_201024 61168554127126948963267 := by
  unfold tailWord_201024
  simp only [CollatzResearch.WordTrace]
  refine ⟨3665973811865927505493063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4887965082487903340657417 3665973811865927505493063)
  ·
    refine ⟨5498960717798891258239595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3665973811865927505493063 5498960717798891258239595)
    ·
      refine ⟨8248441076698336887359393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5498960717798891258239595 8248441076698336887359393)
      ·
        refine ⟨6186330807523752665519545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8248441076698336887359393 6186330807523752665519545)
        ·
          refine ⟨4639748105642814499139659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6186330807523752665519545 4639748105642814499139659)
          ·
            refine ⟨6959622158464221748709489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4639748105642814499139659 6959622158464221748709489)
            ·
              refine ⟨5219716618848166311532117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6959622158464221748709489 5219716618848166311532117)
              ·
                refine ⟨61168554127126948963267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 5219716618848166311532117 61168554127126948963267)
                ·
                  rfl

theorem cell19_201024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 2, 8].length) (baseStart_201024 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_201024 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_201024 prefixEnd_201024 := by exact prefixLift 201024
  have htrace : WordTrace (prefixWord ++ tailWord_201024) baseStart_201024 baseEnd_201024 := by
    simpa [prefixWord, tailWord_201024, baseEnd_201024] using wordTrace_append hprefix tailTrace_201024
  have hstable : (prefixWord ++ tailWord_201024).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_201024).length < 2 ^ (prefixWord ++ tailWord_201024).sum := by decide
  have hdescent : baseEnd_201024 < baseStart_201024 := by decide
  rcases family_descends (prefixWord ++ tailWord_201024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_201081 : List Nat := [1, 2, 1, 3, 2, 1, 1, 8]
def baseStart_201081 : Nat := 118140960795 + 201081 * 2 ^ 59
def prefixEnd_201081 : Nat := 4983230072969 + 3 ^ 40 * 201081 * 2
def baseEnd_201081 : Nat := 61185898362567705696445

theorem tailTrace_201081 : CollatzResearch.WordTrace tailWord_201081 prefixEnd_201081 61185898362567705696445 := by
  unfold tailWord_201081
  simp only [CollatzResearch.WordTrace]
  refine ⟨7334026584525353745811097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4889351056350235830540731 7334026584525353745811097)
  ·
    refine ⟨5500519938394015309358323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7334026584525353745811097 5500519938394015309358323)
    ·
      refine ⟨8250779907591022964037485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5500519938394015309358323 8250779907591022964037485)
      ·
        refine ⟨3094042465346633611514057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8250779907591022964037485 3094042465346633611514057)
        ·
          refine ⟨2320531849009975208635543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3094042465346633611514057 2320531849009975208635543)
          ·
            refine ⟨3480797773514962812953315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2320531849009975208635543 3480797773514962812953315)
            ·
              refine ⟨5221196660272444219429973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3480797773514962812953315 5221196660272444219429973)
              ·
                refine ⟨61185898362567705696445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 5221196660272444219429973 61185898362567705696445)
                ·
                  rfl

theorem cell19_201081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 1, 8].length) (baseStart_201081 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_201081 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_201081 prefixEnd_201081 := by exact prefixLift 201081
  have htrace : WordTrace (prefixWord ++ tailWord_201081) baseStart_201081 baseEnd_201081 := by
    simpa [prefixWord, tailWord_201081, baseEnd_201081] using wordTrace_append hprefix tailTrace_201081
  have hstable : (prefixWord ++ tailWord_201081).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_201081).length < 2 ^ (prefixWord ++ tailWord_201081).sum := by decide
  have hdescent : baseEnd_201081 < baseStart_201081 := by decide
  rcases family_descends (prefixWord ++ tailWord_201081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_201090 : List Nat := [3, 4, 2, 1, 3, 1, 2, 3]
def baseStart_201090 : Nat := 118140960795 + 201090 * 2 ^ 59
def prefixEnd_201090 : Nat := 4983230072969 + 3 ^ 40 * 201090 * 2
def baseEnd_201090 : Nat := 61188636926058351496421

theorem tailTrace_201090 : CollatzResearch.WordTrace tailWord_201090 prefixEnd_201090 61188636926058351496421 := by
  unfold tailWord_201090
  simp only [CollatzResearch.WordTrace]
  refine ⟨1833588710373187070722181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4889569894328498855259149 1833588710373187070722181)
  ·
    refine ⟨343797883194972575760409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1833588710373187070722181 343797883194972575760409)
    ·
      refine ⟨257848412396229431820307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 343797883194972575760409 257848412396229431820307)
      ·
        refine ⟨386772618594344147730461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 257848412396229431820307 386772618594344147730461)
        ·
          refine ⟨145039731972879055398923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 386772618594344147730461 145039731972879055398923)
          ·
            refine ⟨217559597959318583098385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 145039731972879055398923 217559597959318583098385)
            ·
              refine ⟨163169698469488937323789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 217559597959318583098385 163169698469488937323789)
              ·
                refine ⟨61188636926058351496421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 163169698469488937323789 61188636926058351496421)
                ·
                  rfl

theorem cell19_201090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 3, 1, 2, 3].length) (baseStart_201090 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_201090 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_201090 prefixEnd_201090 := by exact prefixLift 201090
  have htrace : WordTrace (prefixWord ++ tailWord_201090) baseStart_201090 baseEnd_201090 := by
    simpa [prefixWord, tailWord_201090, baseEnd_201090] using wordTrace_append hprefix tailTrace_201090
  have hstable : (prefixWord ++ tailWord_201090).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_201090).length < 2 ^ (prefixWord ++ tailWord_201090).sum := by decide
  have hdescent : baseEnd_201090 < baseStart_201090 := by decide
  rcases family_descends (prefixWord ++ tailWord_201090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_201130 : List Nat := [3, 1, 6, 1, 1, 1, 2, 4]
def baseStart_201130 : Nat := 118140960795 + 201130 * 2 ^ 59
def prefixEnd_201130 : Nat := 4983230072969 + 3 ^ 40 * 201130 * 2
def baseEnd_201130 : Nat := 61200808319350110607423

theorem tailTrace_201130 : CollatzResearch.WordTrace tailWord_201130 prefixEnd_201130 61200808319350110607423 := by
  unfold tailWord_201130
  simp only [CollatzResearch.WordTrace]
  refine ⟨1833953440336958778586211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4890542507565223409563229 1833953440336958778586211)
  ·
    refine ⟨2750930160505438167879317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1833953440336958778586211 2750930160505438167879317)
    ·
      refine ⟨128949851273692414119343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 2750930160505438167879317 128949851273692414119343)
      ·
        refine ⟨193424776910538621179015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 128949851273692414119343 193424776910538621179015)
        ·
          refine ⟨290137165365807931768523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 193424776910538621179015 290137165365807931768523)
          ·
            refine ⟨435205748048711897652785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 290137165365807931768523 435205748048711897652785)
            ·
              refine ⟨326404311036533923239589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 435205748048711897652785 326404311036533923239589)
              ·
                refine ⟨61200808319350110607423, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 326404311036533923239589 61200808319350110607423)
                ·
                  rfl

theorem cell19_201130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 1, 1, 2, 4].length) (baseStart_201130 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_201130 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_201130 prefixEnd_201130 := by exact prefixLift 201130
  have htrace : WordTrace (prefixWord ++ tailWord_201130) baseStart_201130 baseEnd_201130 := by
    simpa [prefixWord, tailWord_201130, baseEnd_201130] using wordTrace_append hprefix tailTrace_201130
  have hstable : (prefixWord ++ tailWord_201130).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_201130).length < 2 ^ (prefixWord ++ tailWord_201130).sum := by decide
  have hdescent : baseEnd_201130 < baseStart_201130 := by decide
  rcases family_descends (prefixWord ++ tailWord_201130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_201189 : List Nat := [1, 3, 1, 5, 3, 1, 1, 4]
def baseStart_201189 : Nat := 118140960795 + 201189 * 2 ^ 59
def prefixEnd_201189 : Nat := 4983230072969 + 3 ^ 40 * 201189 * 2
def baseEnd_201189 : Nat := 61218761124455455296151

theorem tailTrace_201189 : CollatzResearch.WordTrace tailWord_201189 prefixEnd_201189 61218761124455455296151 := by
  unfold tailWord_201189
  simp only [CollatzResearch.WordTrace]
  refine ⟨7337965668134088190742621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4891977112089392127161747 7337965668134088190742621)
  ·
    refine ⟨2751737125550283071528483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7337965668134088190742621 2751737125550283071528483)
    ·
      refine ⟨4127605688325424607292725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2751737125550283071528483 4127605688325424607292725)
      ·
        refine ⟨386963033280508556933693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 4127605688325424607292725 386963033280508556933693)
        ·
          refine ⟨145111137480190708850135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 386963033280508556933693 145111137480190708850135)
          ·
            refine ⟨217666706220286063275203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 145111137480190708850135 217666706220286063275203)
            ·
              refine ⟨326500059330429094912805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 217666706220286063275203 326500059330429094912805)
              ·
                refine ⟨61218761124455455296151, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 326500059330429094912805 61218761124455455296151)
                ·
                  rfl

theorem cell19_201189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 3, 1, 1, 4].length) (baseStart_201189 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_201189 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_201189 prefixEnd_201189 := by exact prefixLift 201189
  have htrace : WordTrace (prefixWord ++ tailWord_201189) baseStart_201189 baseEnd_201189 := by
    simpa [prefixWord, tailWord_201189, baseEnd_201189] using wordTrace_append hprefix tailTrace_201189
  have hstable : (prefixWord ++ tailWord_201189).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_201189).length < 2 ^ (prefixWord ++ tailWord_201189).sum := by decide
  have hdescent : baseEnd_201189 < baseStart_201189 := by decide
  rcases family_descends (prefixWord ++ tailWord_201189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_201261 : List Nat := [1, 5, 4, 1, 1, 2, 2, 3]
def baseStart_201261 : Nat := 118140960795 + 201261 * 2 ^ 59
def prefixEnd_201261 : Nat := 4983230072969 + 3 ^ 40 * 201261 * 2
def baseEnd_201261 : Nat := 61240669632380621695955

theorem tailTrace_201261 : CollatzResearch.WordTrace tailWord_201261 prefixEnd_201261 61240669632380621695955 := by
  unfold tailWord_201261
  simp only [CollatzResearch.WordTrace]
  refine ⟨7340591723873244487363637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4893727815915496324909091 7340591723873244487363637)
  ·
    refine ⟨688180474113116670690341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 7340591723873244487363637 688180474113116670690341)
    ·
      refine ⟨129033838896209375754439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 688180474113116670690341 129033838896209375754439)
      ·
        refine ⟨193550758344314063631659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 129033838896209375754439 193550758344314063631659)
        ·
          refine ⟨290326137516471095447489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 193550758344314063631659 290326137516471095447489)
          ·
            refine ⟨217744603137353321585617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 290326137516471095447489 217744603137353321585617)
            ·
              refine ⟨163308452353014991189213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 217744603137353321585617 163308452353014991189213)
              ·
                refine ⟨61240669632380621695955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 163308452353014991189213 61240669632380621695955)
                ·
                  rfl

theorem cell19_201261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 1, 2, 2, 3].length) (baseStart_201261 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_201261 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_201261 prefixEnd_201261 := by exact prefixLift 201261
  have htrace : WordTrace (prefixWord ++ tailWord_201261) baseStart_201261 baseEnd_201261 := by
    simpa [prefixWord, tailWord_201261, baseEnd_201261] using wordTrace_append hprefix tailTrace_201261
  have hstable : (prefixWord ++ tailWord_201261).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_201261).length < 2 ^ (prefixWord ++ tailWord_201261).sum := by decide
  have hdescent : baseEnd_201261 < baseStart_201261 := by decide
  rcases family_descends (prefixWord ++ tailWord_201261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_201271 : List Nat := [1, 1, 3, 1, 2, 3, 3, 5]
def baseStart_201271 : Nat := 118140960795 + 201271 * 2 ^ 59
def prefixEnd_201271 : Nat := 4983230072969 + 3 ^ 40 * 201271 * 2
def baseEnd_201271 : Nat := 61243712480703561473705

theorem tailTrace_201271 : CollatzResearch.WordTrace tailWord_201271 prefixEnd_201271 61243712480703561473705 := by
  unfold tailWord_201271
  simp only [CollatzResearch.WordTrace]
  refine ⟨7340956453837016195227667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4893970969224677463485111 7340956453837016195227667)
  ·
    refine ⟨11011434680755524292841501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7340956453837016195227667 11011434680755524292841501)
    ·
      refine ⟨4129288005283321609815563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11011434680755524292841501 4129288005283321609815563)
      ·
        refine ⟨6193932007924982414723345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4129288005283321609815563 6193932007924982414723345)
        ·
          refine ⟨4645449005943736811042509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6193932007924982414723345 4645449005943736811042509)
          ·
            refine ⟨1742043377228901304140941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4645449005943736811042509 1742043377228901304140941)
            ·
              refine ⟨653266266460837989052853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1742043377228901304140941 653266266460837989052853)
              ·
                refine ⟨61243712480703561473705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 653266266460837989052853 61243712480703561473705)
                ·
                  rfl

theorem cell19_201271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 3, 5].length) (baseStart_201271 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_201271 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_201271 prefixEnd_201271 := by exact prefixLift 201271
  have htrace : WordTrace (prefixWord ++ tailWord_201271) baseStart_201271 baseEnd_201271 := by
    simpa [prefixWord, tailWord_201271, baseEnd_201271] using wordTrace_append hprefix tailTrace_201271
  have hstable : (prefixWord ++ tailWord_201271).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_201271).length < 2 ^ (prefixWord ++ tailWord_201271).sum := by decide
  have hdescent : baseEnd_201271 < baseStart_201271 := by decide
  rcases family_descends (prefixWord ++ tailWord_201271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_201286 : List Nat := [6, 1, 1, 1, 2, 1, 7]
def baseStart_201286 : Nat := 118140960795 + 201286 * 2 ^ 59
def prefixEnd_201286 : Nat := 4983230072969 + 3 ^ 40 * 201286 * 2
def baseEnd_201286 : Nat := 20416092251062657046777

theorem tailTrace_201286 : CollatzResearch.WordTrace tailWord_201286 prefixEnd_201286 20416092251062657046777 := by
  unfold tailWord_201286
  simp only [CollatzResearch.WordTrace]
  refine ⟨229421985899458554906991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 4894335699188449171349141 229421985899458554906991)
  ·
    refine ⟨344132978849187832360487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 229421985899458554906991 344132978849187832360487)
    ·
      refine ⟨516199468273781748540731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 344132978849187832360487 516199468273781748540731)
      ·
        refine ⟨774299202410672622811097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 516199468273781748540731 774299202410672622811097)
        ·
          refine ⟨580724401808004467108323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 774299202410672622811097 580724401808004467108323)
          ·
            refine ⟨871086602712006700662485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 580724401808004467108323 871086602712006700662485)
            ·
              refine ⟨20416092251062657046777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 871086602712006700662485 20416092251062657046777)
              ·
                rfl

theorem cell19_201286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 7].length) (baseStart_201286 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_201286 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_201286 prefixEnd_201286 := by exact prefixLift 201286
  have htrace : WordTrace (prefixWord ++ tailWord_201286) baseStart_201286 baseEnd_201286 := by
    simpa [prefixWord, tailWord_201286, baseEnd_201286] using wordTrace_append hprefix tailTrace_201286
  have hstable : (prefixWord ++ tailWord_201286).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_201286).length < 2 ^ (prefixWord ++ tailWord_201286).sum := by decide
  have hdescent : baseEnd_201286 < baseStart_201286 := by decide
  rcases family_descends (prefixWord ++ tailWord_201286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_201290 : List Nat := [3, 1, 2, 1, 1, 4, 7]
def baseStart_201290 : Nat := 118140960795 + 201290 * 2 ^ 59
def prefixEnd_201290 : Nat := 4983230072969 + 3 ^ 40 * 201290 * 2
def baseEnd_201290 : Nat := 20416497964172382350477

theorem tailTrace_201290 : CollatzResearch.WordTrace tailWord_201290 prefixEnd_201290 20416497964172382350477 := by
  unfold tailWord_201290
  simp only [CollatzResearch.WordTrace]
  refine ⟨1835412360192045610042331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4894432960512121626779549 1835412360192045610042331)
  ·
    refine ⟨2753118540288068415063497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1835412360192045610042331 2753118540288068415063497)
    ·
      refine ⟨2064838905216051311297623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2753118540288068415063497 2064838905216051311297623)
      ·
        refine ⟨3097258357824076966946435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2064838905216051311297623 3097258357824076966946435)
        ·
          refine ⟨4645887536736115450419653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3097258357824076966946435 4645887536736115450419653)
          ·
            refine ⟨871103913138021646953685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4645887536736115450419653 871103913138021646953685)
            ·
              refine ⟨20416497964172382350477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 871103913138021646953685 20416497964172382350477)
              ·
                rfl

theorem cell19_201290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 7].length) (baseStart_201290 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_201290 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_201290 prefixEnd_201290 := by exact prefixLift 201290
  have htrace : WordTrace (prefixWord ++ tailWord_201290) baseStart_201290 baseEnd_201290 := by
    simpa [prefixWord, tailWord_201290, baseEnd_201290] using wordTrace_append hprefix tailTrace_201290
  have hstable : (prefixWord ++ tailWord_201290).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_201290).length < 2 ^ (prefixWord ++ tailWord_201290).sum := by decide
  have hdescent : baseEnd_201290 < baseStart_201290 := by decide
  rcases family_descends (prefixWord ++ tailWord_201290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_201326 : List Nat := [4, 1, 2, 2, 2, 1, 2, 5]
def baseStart_201326 : Nat := 118140960795 + 201326 * 2 ^ 59
def prefixEnd_201326 : Nat := 4983230072969 + 3 ^ 40 * 201326 * 2
def baseEnd_201326 : Nat := 61260448146479730251333

theorem tailTrace_201326 : CollatzResearch.WordTrace tailWord_201326 prefixEnd_201326 61260448146479730251333 := by
  unfold tailWord_201326
  simp only [CollatzResearch.WordTrace]
  refine ⟨917870308579720073559979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 4895308312425173725653221 917870308579720073559979)
  ·
    refine ⟨1376805462869580110339969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 917870308579720073559979 1376805462869580110339969)
    ·
      refine ⟨1032604097152185082754977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1376805462869580110339969 1032604097152185082754977)
      ·
        refine ⟨774453072864138812066233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1032604097152185082754977 774453072864138812066233)
        ·
          refine ⟨580839804648104109049675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 774453072864138812066233 580839804648104109049675)
          ·
            refine ⟨871259706972156163574513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 580839804648104109049675 871259706972156163574513)
            ·
              refine ⟨653444780229117122680885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 871259706972156163574513 653444780229117122680885)
              ·
                refine ⟨61260448146479730251333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 653444780229117122680885 61260448146479730251333)
                ·
                  rfl

theorem cell19_201326_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 2, 5].length) (baseStart_201326 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_201326 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_201326 prefixEnd_201326 := by exact prefixLift 201326
  have htrace : WordTrace (prefixWord ++ tailWord_201326) baseStart_201326 baseEnd_201326 := by
    simpa [prefixWord, tailWord_201326, baseEnd_201326] using wordTrace_append hprefix tailTrace_201326
  have hstable : (prefixWord ++ tailWord_201326).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_201326).length < 2 ^ (prefixWord ++ tailWord_201326).sum := by decide
  have hdescent : baseEnd_201326 < baseStart_201326 := by decide
  rcases family_descends (prefixWord ++ tailWord_201326) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_201362 : List Nat := [3, 2, 3, 1, 2, 3, 1, 4]
def baseStart_201362 : Nat := 118140960795 + 201362 * 2 ^ 59
def prefixEnd_201362 : Nat := 4983230072969 + 3 ^ 40 * 201362 * 2
def baseEnd_201362 : Nat := 61271402400442313451235

theorem tailTrace_201362 : CollatzResearch.WordTrace tailWord_201362 prefixEnd_201362 61271402400442313451235 := by
  unfold tailWord_201362
  simp only [CollatzResearch.WordTrace]
  refine ⟨1836068874126834684197585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4896183664338225824526893 1836068874126834684197585)
  ·
    refine ⟨1377051655595126013148189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1836068874126834684197585 1377051655595126013148189)
    ·
      refine ⟨516394370848172254930571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1377051655595126013148189 516394370848172254930571)
      ·
        refine ⟨774591556272258382395857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 516394370848172254930571 774591556272258382395857)
        ·
          refine ⟨580943667204193786796893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 774591556272258382395857 580943667204193786796893)
          ·
            refine ⟨217853875201572670048835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 580943667204193786796893 217853875201572670048835)
            ·
              refine ⟨326780812802359005073253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 217853875201572670048835 326780812802359005073253)
              ·
                refine ⟨61271402400442313451235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 326780812802359005073253 61271402400442313451235)
                ·
                  rfl

theorem cell19_201362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 3, 1, 4].length) (baseStart_201362 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_201362 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_201362 prefixEnd_201362 := by exact prefixLift 201362
  have htrace : WordTrace (prefixWord ++ tailWord_201362) baseStart_201362 baseEnd_201362 := by
    simpa [prefixWord, tailWord_201362, baseEnd_201362] using wordTrace_append hprefix tailTrace_201362
  have hstable : (prefixWord ++ tailWord_201362).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_201362).length < 2 ^ (prefixWord ++ tailWord_201362).sum := by decide
  have hdescent : baseEnd_201362 < baseStart_201362 := by decide
  rcases family_descends (prefixWord ++ tailWord_201362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_201404 : List Nat := [2, 2, 2, 3, 1, 1, 8]
def baseStart_201404 : Nat := 118140960795 + 201404 * 2 ^ 59
def prefixEnd_201404 : Nat := 4983230072969 + 3 ^ 40 * 201404 * 2
def baseEnd_201404 : Nat := 20428060787799553505929

theorem tailTrace_201404 : CollatzResearch.WordTrace tailWord_201404 prefixEnd_201404 20428060787799553505929 := by
  unfold tailWord_201404
  simp only [CollatzResearch.WordTrace]
  refine ⟨3672903681177589954909633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4897204908236786606546177 3672903681177589954909633)
  ·
    refine ⟨2754677760883192466182225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3672903681177589954909633 2754677760883192466182225)
    ·
      refine ⟨2066008320662394349636669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2754677760883192466182225 2066008320662394349636669)
      ·
        refine ⟨774753120248397881113751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2066008320662394349636669 774753120248397881113751)
        ·
          refine ⟨1162129680372596821670627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 774753120248397881113751 1162129680372596821670627)
          ·
            refine ⟨1743194520558895232505941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1162129680372596821670627 1743194520558895232505941)
            ·
              refine ⟨20428060787799553505929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1743194520558895232505941 20428060787799553505929)
              ·
                rfl

theorem cell19_201404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 8].length) (baseStart_201404 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_201404 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_201404 prefixEnd_201404 := by exact prefixLift 201404
  have htrace : WordTrace (prefixWord ++ tailWord_201404) baseStart_201404 baseEnd_201404 := by
    simpa [prefixWord, tailWord_201404, baseEnd_201404] using wordTrace_append hprefix tailTrace_201404
  have hstable : (prefixWord ++ tailWord_201404).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_201404).length < 2 ^ (prefixWord ++ tailWord_201404).sum := by decide
  have hdescent : baseEnd_201404 < baseStart_201404 := by decide
  rcases family_descends (prefixWord ++ tailWord_201404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_201436 : List Nat := [2, 2, 5, 1, 1, 3, 2, 3]
def baseStart_201436 : Nat := 118140960795 + 201436 * 2 ^ 59
def prefixEnd_201436 : Nat := 4983230072969 + 3 ^ 40 * 201436 * 2
def baseEnd_201436 : Nat := 61293919478032067806589

theorem tailTrace_201436 : CollatzResearch.WordTrace tailWord_201436 prefixEnd_201436 61293919478032067806589 := by
  unfold tailWord_201436
  simp only [CollatzResearch.WordTrace]
  refine ⟨3673487249119624687492081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4897982998826166249989441 3673487249119624687492081)
  ·
    refine ⟨2755115436839718515619061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3673487249119624687492081 2755115436839718515619061)
    ·
      refine ⟨258292072203723610839287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 2755115436839718515619061 258292072203723610839287)
      ·
        refine ⟨387438108305585416258931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 258292072203723610839287 387438108305585416258931)
        ·
          refine ⟨581157162458378124388397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 387438108305585416258931 581157162458378124388397)
          ·
            refine ⟨217933935921891796645649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 581157162458378124388397 217933935921891796645649)
            ·
              refine ⟨163450451941418847484237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 217933935921891796645649 163450451941418847484237)
              ·
                refine ⟨61293919478032067806589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 163450451941418847484237 61293919478032067806589)
                ·
                  rfl

theorem cell19_201436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 3, 2, 3].length) (baseStart_201436 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_201436 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_201436 prefixEnd_201436 := by exact prefixLift 201436
  have htrace : WordTrace (prefixWord ++ tailWord_201436) baseStart_201436 baseEnd_201436 := by
    simpa [prefixWord, tailWord_201436, baseEnd_201436] using wordTrace_append hprefix tailTrace_201436
  have hstable : (prefixWord ++ tailWord_201436).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_201436).length < 2 ^ (prefixWord ++ tailWord_201436).sum := by decide
  have hdescent : baseEnd_201436 < baseStart_201436 := by decide
  rcases family_descends (prefixWord ++ tailWord_201436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_201480 : List Nat := [2, 1, 3, 2, 2, 2, 1, 6]
def baseStart_201480 : Nat := 118140960795 + 201480 * 2 ^ 59
def prefixEnd_201480 : Nat := 4983230072969 + 3 ^ 40 * 201480 * 2
def baseEnd_201480 : Nat := 61307308010653002828691

theorem tailTrace_201480 : CollatzResearch.WordTrace tailWord_201480 prefixEnd_201480 61307308010653002828691 := by
  unfold tailWord_201480
  simp only [CollatzResearch.WordTrace]
  refine ⟨3674289655039922444792947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4899052873386563259723929 3674289655039922444792947)
  ·
    refine ⟨5511434482559883667189421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3674289655039922444792947 5511434482559883667189421)
    ·
      refine ⟨2066787930959956375196033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5511434482559883667189421 2066787930959956375196033)
      ·
        refine ⟨1550090948219967281397025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2066787930959956375196033 1550090948219967281397025)
        ·
          refine ⟨1162568211164975461047769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1550090948219967281397025 1162568211164975461047769)
          ·
            refine ⟨871926158373731595785827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1162568211164975461047769 871926158373731595785827)
            ·
              refine ⟨1307889237560597393678741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 871926158373731595785827 1307889237560597393678741)
              ·
                refine ⟨61307308010653002828691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1307889237560597393678741 61307308010653002828691)
                ·
                  rfl

theorem cell19_201480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 1, 6].length) (baseStart_201480 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_201480 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_201480 prefixEnd_201480 := by exact prefixLift 201480
  have htrace : WordTrace (prefixWord ++ tailWord_201480) baseStart_201480 baseEnd_201480 := by
    simpa [prefixWord, tailWord_201480, baseEnd_201480] using wordTrace_append hprefix tailTrace_201480
  have hstable : (prefixWord ++ tailWord_201480).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_201480).length < 2 ^ (prefixWord ++ tailWord_201480).sum := by decide
  have hdescent : baseEnd_201480 < baseStart_201480 := by decide
  rcases family_descends (prefixWord ++ tailWord_201480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_201514 : List Nat := [3, 1, 4, 3, 2, 6]
def baseStart_201514 : Nat := 118140960795 + 201514 * 2 ^ 59
def prefixEnd_201514 : Nat := 4983230072969 + 3 ^ 40 * 201514 * 2
def baseEnd_201514 : Nat := 6813072632772333119227

theorem tailTrace_201514 : CollatzResearch.WordTrace tailWord_201514 prefixEnd_201514 6813072632772333119227 := by
  unfold tailWord_201514
  simp only [CollatzResearch.WordTrace]
  refine ⟨1837454847989167174080899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4899879594637779130882397 1837454847989167174080899)
  ·
    refine ⟨2756182271983750761121349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1837454847989167174080899 2756182271983750761121349)
    ·
      refine ⟨516784175996953267710253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2756182271983750761121349 516784175996953267710253)
      ·
        refine ⟨193794065998857475391345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 516784175996953267710253 193794065998857475391345)
        ·
          refine ⟨145345549499143106543509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 193794065998857475391345 145345549499143106543509)
          ·
            refine ⟨6813072632772333119227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 145345549499143106543509 6813072632772333119227)
            ·
              rfl

theorem cell19_201514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 2, 6].length) (baseStart_201514 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_201514 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_201514 prefixEnd_201514 := by exact prefixLift 201514
  have htrace : WordTrace (prefixWord ++ tailWord_201514) baseStart_201514 baseEnd_201514 := by
    simpa [prefixWord, tailWord_201514, baseEnd_201514] using wordTrace_append hprefix tailTrace_201514
  have hstable : (prefixWord ++ tailWord_201514).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_201514).length < 2 ^ (prefixWord ++ tailWord_201514).sum := by decide
  have hdescent : baseEnd_201514 < baseStart_201514 := by decide
  rcases family_descends (prefixWord ++ tailWord_201514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_201533 : List Nat := [1, 4, 1, 4, 2, 2, 1, 4]
def baseStart_201533 : Nat := 118140960795 + 201533 * 2 ^ 59
def prefixEnd_201533 : Nat := 4983230072969 + 3 ^ 40 * 201533 * 2
def baseEnd_201533 : Nat := 61323435106764583650769

theorem tailTrace_201533 : CollatzResearch.WordTrace tailWord_201533 prefixEnd_201533 61323435106764583650769 := by
  unfold tailWord_201533
  simp only [CollatzResearch.WordTrace]
  refine ⟨7350512378887834941265253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4900341585925223294176835 7350512378887834941265253)
  ·
    refine ⟨1378221071041469051487235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7350512378887834941265253 1378221071041469051487235)
    ·
      refine ⟨2067331606562203577230853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1378221071041469051487235 2067331606562203577230853)
      ·
        refine ⟨387624676230413170730785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2067331606562203577230853 387624676230413170730785)
        ·
          refine ⟨290718507172809878048089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 387624676230413170730785 290718507172809878048089)
          ·
            refine ⟨218038880379607408536067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 290718507172809878048089 218038880379607408536067)
            ·
              refine ⟨327058320569411112804101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 218038880379607408536067 327058320569411112804101)
              ·
                refine ⟨61323435106764583650769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 327058320569411112804101 61323435106764583650769)
                ·
                  rfl

theorem cell19_201533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 2, 2, 1, 4].length) (baseStart_201533 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_201533 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_201533 prefixEnd_201533 := by exact prefixLift 201533
  have htrace : WordTrace (prefixWord ++ tailWord_201533) baseStart_201533 baseEnd_201533 := by
    simpa [prefixWord, tailWord_201533, baseEnd_201533] using wordTrace_append hprefix tailTrace_201533
  have hstable : (prefixWord ++ tailWord_201533).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_201533).length < 2 ^ (prefixWord ++ tailWord_201533).sum := by decide
  have hdescent : baseEnd_201533 < baseStart_201533 := by decide
  rcases family_descends (prefixWord ++ tailWord_201533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan19Incremental
