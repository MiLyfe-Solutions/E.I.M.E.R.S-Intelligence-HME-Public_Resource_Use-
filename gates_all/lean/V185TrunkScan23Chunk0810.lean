import V185TrunkScan23Chunk0809

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_4791506 : List Nat := [3, 2, 2, 2, 1, 1, 4, 1, 2, 5]
def baseStart_4791506 : Nat := 118140960795 + 4791506 * 2 ^ 59
def prefixEnd_4791506 : Nat := 4983230072969 + 3 ^ 40 * 4791506 * 2
def baseEnd_4791506 : Nat := 820115212300678481479757

theorem tailTrace_4791506 : CollatzResearch.WordTrace tailWord_4791506 prefixEnd_4791506 820115212300678481479757 := by
  unfold tailWord_4791506
  simp only [CollatzResearch.WordTrace]
  refine ⟨43690145244799890229950593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 116507053986133040613201581 43690145244799890229950593)
  ·
    refine ⟨32767608933599917672462945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43690145244799890229950593 32767608933599917672462945)
    ·
      refine ⟨24575706700199938254347209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32767608933599917672462945 24575706700199938254347209)
      ·
        refine ⟨18431780025149953690760407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24575706700199938254347209 18431780025149953690760407)
        ·
          refine ⟨27647670037724930536140611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18431780025149953690760407 27647670037724930536140611)
          ·
            refine ⟨41471505056587395804210917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27647670037724930536140611 41471505056587395804210917)
            ·
              refine ⟨7775907198110136713289547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 41471505056587395804210917 7775907198110136713289547)
              ·
                refine ⟨11663860797165205069934321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7775907198110136713289547 11663860797165205069934321)
                ·
                  refine ⟨8747895597873903802450741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11663860797165205069934321 8747895597873903802450741)
                  ·
                    refine ⟨820115212300678481479757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8747895597873903802450741 820115212300678481479757)
                    ·
                      rfl

theorem cell23_4791506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 4, 1, 2, 5].length) (baseStart_4791506 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4791506 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4791506 prefixEnd_4791506 := by exact prefixLift 4791506
  have htrace : WordTrace (prefixWord ++ tailWord_4791506) baseStart_4791506 baseEnd_4791506 := by
    simpa [prefixWord, tailWord_4791506, baseEnd_4791506] using wordTrace_append hprefix tailTrace_4791506
  have hstable : (prefixWord ++ tailWord_4791506).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4791506).length < 2 ^ (prefixWord ++ tailWord_4791506).sum := by decide
  have hdescent : baseEnd_4791506 < baseStart_4791506 := by decide
  rcases family_descends (prefixWord ++ tailWord_4791506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4791527 : List Nat := [1, 1, 5, 3, 3, 1, 2, 2, 5]
def baseStart_4791527 : Nat := 118140960795 + 4791527 * 2 ^ 59
def prefixEnd_4791527 : Nat := 4983230072969 + 3 ^ 40 * 4791527 * 2
def baseEnd_4791527 : Nat := 273372935555086651364075

theorem tailTrace_4791527 : CollatzResearch.WordTrace tailWord_4791527 prefixEnd_4791527 273372935555086651364075 := by
  unfold tailWord_4791527
  simp only [CollatzResearch.WordTrace]
  refine ⟨174761346912123481506316835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116507564608082321004211223 174761346912123481506316835)
  ·
    refine ⟨262142020368185222259475253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 174761346912123481506316835 262142020368185222259475253)
    ·
      refine ⟨24575814409517364586825805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 262142020368185222259475253 24575814409517364586825805)
      ·
        refine ⟨9215930403569011720059677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24575814409517364586825805 9215930403569011720059677)
        ·
          refine ⟨3455973901338379395022379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9215930403569011720059677 3455973901338379395022379)
          ·
            refine ⟨5183960852007569092533569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3455973901338379395022379 5183960852007569092533569)
            ·
              refine ⟨3887970639005676819400177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5183960852007569092533569 3887970639005676819400177)
              ·
                refine ⟨2915977979254257614550133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3887970639005676819400177 2915977979254257614550133)
                ·
                  refine ⟨273372935555086651364075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2915977979254257614550133 273372935555086651364075)
                  ·
                    rfl

theorem cell23_4791527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 3, 1, 2, 2, 5].length) (baseStart_4791527 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4791527 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4791527 prefixEnd_4791527 := by exact prefixLift 4791527
  have htrace : WordTrace (prefixWord ++ tailWord_4791527) baseStart_4791527 baseEnd_4791527 := by
    simpa [prefixWord, tailWord_4791527, baseEnd_4791527] using wordTrace_append hprefix tailTrace_4791527
  have hstable : (prefixWord ++ tailWord_4791527).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4791527).length < 2 ^ (prefixWord ++ tailWord_4791527).sum := by decide
  have hdescent : baseEnd_4791527 < baseStart_4791527 := by decide
  rcases family_descends (prefixWord ++ tailWord_4791527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4791560 : List Nat := [2, 1, 3, 2, 5, 1, 1, 1, 2, 1, 4]
def baseStart_4791560 : Nat := 118140960795 + 4791560 * 2 ^ 59
def prefixEnd_4791560 : Nat := 4983230072969 + 3 ^ 40 * 4791560 * 2
def baseEnd_4791560 : Nat := 2460373364857378233164023

theorem tailTrace_4791560 : CollatzResearch.WordTrace tailWord_4791560 prefixEnd_4791560 2460373364857378233164023 := by
  unfold tailWord_4791560
  simp only [CollatzResearch.WordTrace]
  refine ⟨87381275260501964071134067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116508367014002618761512089 87381275260501964071134067)
  ·
    refine ⟨131071912890752946106701101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87381275260501964071134067 131071912890752946106701101)
    ·
      refine ⟨49151967334032354790012913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 131071912890752946106701101 49151967334032354790012913)
      ·
        refine ⟨36863975500524266092509685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49151967334032354790012913 36863975500524266092509685)
        ·
          refine ⟨3455997703174149946172783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 36863975500524266092509685 3455997703174149946172783)
          ·
            refine ⟨5183996554761224919259175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3455997703174149946172783 5183996554761224919259175)
            ·
              refine ⟨7775994832141837378888763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5183996554761224919259175 7775994832141837378888763)
              ·
                refine ⟨11663992248212756068333145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7775994832141837378888763 11663992248212756068333145)
                ·
                  refine ⟨8747994186159567051249859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11663992248212756068333145 8747994186159567051249859)
                  ·
                    refine ⟨13121991279239350576874789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8747994186159567051249859 13121991279239350576874789)
                    ·
                      refine ⟨2460373364857378233164023, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13121991279239350576874789 2460373364857378233164023)
                      ·
                        rfl

theorem cell23_4791560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 5, 1, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 5, 1, 1, 1, 2, 1, 4].length) (baseStart_4791560 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4791560 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4791560 prefixEnd_4791560 := by exact prefixLift 4791560
  have htrace : WordTrace (prefixWord ++ tailWord_4791560) baseStart_4791560 baseEnd_4791560 := by
    simpa [prefixWord, tailWord_4791560, baseEnd_4791560] using wordTrace_append hprefix tailTrace_4791560
  have hstable : (prefixWord ++ tailWord_4791560).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4791560).length < 2 ^ (prefixWord ++ tailWord_4791560).sum := by decide
  have hdescent : baseEnd_4791560 < baseStart_4791560 := by decide
  rcases family_descends (prefixWord ++ tailWord_4791560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4791563 : List Nat := [1, 1, 1, 1, 5, 5, 1, 1, 2, 2, 3]
def baseStart_4791563 : Nat := 118140960795 + 4791563 * 2 ^ 59
def prefixEnd_4791563 : Nat := 4983230072969 + 3 ^ 40 * 4791563 * 2
def baseEnd_4791563 : Nat := 2460374905299341721426509

theorem tailTrace_4791563 : CollatzResearch.WordTrace tailWord_4791563 prefixEnd_4791563 2460374905299341721426509 := by
  unfold tailWord_4791563
  simp only [CollatzResearch.WordTrace]
  refine ⟨174762659939993059654627343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116508439959995373103084895 174762659939993059654627343)
  ·
    refine ⟨262143989909989589481941015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 174762659939993059654627343 262143989909989589481941015)
    ·
      refine ⟨393215984864984384222911523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 262143989909989589481941015 393215984864984384222911523)
      ·
        refine ⟨589823977297476576334367285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 393215984864984384222911523 589823977297476576334367285)
        ·
          refine ⟨55295997871638429031346933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 589823977297476576334367285 55295997871638429031346933)
          ·
            refine ⟨5183999800466102721688775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 55295997871638429031346933 5183999800466102721688775)
            ·
              refine ⟨7775999700699154082533163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5183999800466102721688775 7775999700699154082533163)
              ·
                refine ⟨11663999551048731123799745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7775999700699154082533163 11663999551048731123799745)
                ·
                  refine ⟨8747999663286548342849809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11663999551048731123799745 8747999663286548342849809)
                  ·
                    refine ⟨6560999747464911257137357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8747999663286548342849809 6560999747464911257137357)
                    ·
                      refine ⟨2460374905299341721426509, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6560999747464911257137357 2460374905299341721426509)
                      ·
                        rfl

theorem cell23_4791563_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 5, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 5, 1, 1, 2, 2, 3].length) (baseStart_4791563 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4791563 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4791563 prefixEnd_4791563 := by exact prefixLift 4791563
  have htrace : WordTrace (prefixWord ++ tailWord_4791563) baseStart_4791563 baseEnd_4791563 := by
    simpa [prefixWord, tailWord_4791563, baseEnd_4791563] using wordTrace_append hprefix tailTrace_4791563
  have hstable : (prefixWord ++ tailWord_4791563).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4791563).length < 2 ^ (prefixWord ++ tailWord_4791563).sum := by decide
  have hdescent : baseEnd_4791563 < baseStart_4791563 := by decide
  rcases family_descends (prefixWord ++ tailWord_4791563) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4791583 : List Nat := [1, 1, 2, 4, 4, 2, 1, 2, 6]
def baseStart_4791583 : Nat := 118140960795 + 4791583 * 2 ^ 59
def prefixEnd_4791583 : Nat := 4983230072969 + 3 ^ 40 * 4791583 * 2
def baseEnd_4791583 : Nat := 273376130545825738130713

theorem tailTrace_4791583 : CollatzResearch.WordTrace tailWord_4791583 prefixEnd_4791583 273376130545825738130713 := by
  unfold tailWord_4791583
  simp only [CollatzResearch.WordTrace]
  refine ⟨174763389399920603070355403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116508926266613735380236935 174763389399920603070355403)
  ·
    refine ⟨262145084099880904605533105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 174763389399920603070355403 262145084099880904605533105)
    ·
      refine ⟨196608813074910678454149829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 262145084099880904605533105 196608813074910678454149829)
      ·
        refine ⟨36864152451545752210153093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 196608813074910678454149829 36864152451545752210153093)
        ·
          refine ⟨6912028584664828539403705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 36864152451545752210153093 6912028584664828539403705)
          ·
            refine ⟨5184021438498621404552779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6912028584664828539403705 5184021438498621404552779)
            ·
              refine ⟨7776032157747932106829169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5184021438498621404552779 7776032157747932106829169)
              ·
                refine ⟨5832024118310949080121877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7776032157747932106829169 5832024118310949080121877)
                ·
                  refine ⟨273376130545825738130713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5832024118310949080121877 273376130545825738130713)
                  ·
                    rfl

theorem cell23_4791583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 4, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 4, 2, 1, 2, 6].length) (baseStart_4791583 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4791583 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4791583 prefixEnd_4791583 := by exact prefixLift 4791583
  have htrace : WordTrace (prefixWord ++ tailWord_4791583) baseStart_4791583 baseEnd_4791583 := by
    simpa [prefixWord, tailWord_4791583, baseEnd_4791583] using wordTrace_append hprefix tailTrace_4791583
  have hstable : (prefixWord ++ tailWord_4791583).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4791583).length < 2 ^ (prefixWord ++ tailWord_4791583).sum := by decide
  have hdescent : baseEnd_4791583 < baseStart_4791583 := by decide
  rcases family_descends (prefixWord ++ tailWord_4791583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4791616 : List Nat := [2, 1, 1, 2, 2, 1, 3, 1, 2, 6, 2]
def baseStart_4791616 : Nat := 118140960795 + 4791616 * 2 ^ 59
def prefixEnd_4791616 : Nat := 4983230072969 + 3 ^ 40 * 4791616 * 2
def baseEnd_4791616 : Nat := 2460402119774030014063765

theorem tailTrace_4791616 : CollatzResearch.WordTrace tailWord_4791616 prefixEnd_4791616 2460402119774030014063765 := by
  unfold tailWord_4791616
  simp only [CollatzResearch.WordTrace]
  refine ⟨87382296504400524853153351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116509728672534033137537801 87382296504400524853153351)
  ·
    refine ⟨131073444756600787279730027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87382296504400524853153351 131073444756600787279730027)
    ·
      refine ⟨196610167134901180919595041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 131073444756600787279730027 196610167134901180919595041)
      ·
        refine ⟨147457625351175885689696281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 196610167134901180919595041 147457625351175885689696281)
        ·
          refine ⟨110593219013381914267272211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 147457625351175885689696281 110593219013381914267272211)
          ·
            refine ⟨165889828520072871400908317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 110593219013381914267272211 165889828520072871400908317)
            ·
              refine ⟨62208685695027326775340619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 165889828520072871400908317 62208685695027326775340619)
              ·
                refine ⟨93313028542540990163010929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 62208685695027326775340619 93313028542540990163010929)
                ·
                  refine ⟨69984771406905742622258197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 93313028542540990163010929 69984771406905742622258197)
                  ·
                    refine ⟨3280536159698706685418353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 69984771406905742622258197 3280536159698706685418353)
                    ·
                      refine ⟨2460402119774030014063765, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3280536159698706685418353 2460402119774030014063765)
                      ·
                        rfl

theorem cell23_4791616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 3, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 3, 1, 2, 6, 2].length) (baseStart_4791616 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4791616 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4791616 prefixEnd_4791616 := by exact prefixLift 4791616
  have htrace : WordTrace (prefixWord ++ tailWord_4791616) baseStart_4791616 baseEnd_4791616 := by
    simpa [prefixWord, tailWord_4791616, baseEnd_4791616] using wordTrace_append hprefix tailTrace_4791616
  have hstable : (prefixWord ++ tailWord_4791616).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4791616).length < 2 ^ (prefixWord ++ tailWord_4791616).sum := by decide
  have hdescent : baseEnd_4791616 < baseStart_4791616 := by decide
  rcases family_descends (prefixWord ++ tailWord_4791616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4791619 : List Nat := [1, 1, 1, 3, 1, 3, 1, 1, 5, 1, 5]
def baseStart_4791619 : Nat := 118140960795 + 4791619 * 2 ^ 59
def prefixEnd_4791619 : Nat := 4983230072969 + 3 ^ 40 * 4791619 * 2
def baseEnd_4791619 : Nat := 2460403660215993502326251

theorem tailTrace_4791619 : CollatzResearch.WordTrace tailWord_4791619 prefixEnd_4791619 2460403660215993502326251 := by
  unfold tailWord_4791619
  simp only [CollatzResearch.WordTrace]
  refine ⟨174764702427790181218665911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116509801618526787479110607 174764702427790181218665911)
  ·
    refine ⟨262147053641685271827998867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 174764702427790181218665911 262147053641685271827998867)
    ·
      refine ⟨393220580462527907741998301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 262147053641685271827998867 393220580462527907741998301)
      ·
        refine ⟨147457717673447965403249363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 393220580462527907741998301 147457717673447965403249363)
        ·
          refine ⟨221186576510171948104874045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 147457717673447965403249363 221186576510171948104874045)
          ·
            refine ⟨82944966191314480539327767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 221186576510171948104874045 82944966191314480539327767)
            ·
              refine ⟨124417449286971720808991651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 82944966191314480539327767 124417449286971720808991651)
              ·
                refine ⟨186626173930457581213487477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 124417449286971720808991651 186626173930457581213487477)
                ·
                  refine ⟨17496203805980398238764451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 186626173930457581213487477 17496203805980398238764451)
                  ·
                    refine ⟨26244305708970597358146677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17496203805980398238764451 26244305708970597358146677)
                    ·
                      refine ⟨2460403660215993502326251, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26244305708970597358146677 2460403660215993502326251)
                      ·
                        rfl

theorem cell23_4791619_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 1, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 1, 1, 5, 1, 5].length) (baseStart_4791619 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4791619 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4791619 prefixEnd_4791619 := by exact prefixLift 4791619
  have htrace : WordTrace (prefixWord ++ tailWord_4791619) baseStart_4791619 baseEnd_4791619 := by
    simpa [prefixWord, tailWord_4791619, baseEnd_4791619] using wordTrace_append hprefix tailTrace_4791619
  have hstable : (prefixWord ++ tailWord_4791619).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4791619).length < 2 ^ (prefixWord ++ tailWord_4791619).sum := by decide
  have hdescent : baseEnd_4791619 < baseStart_4791619 := by decide
  rcases family_descends (prefixWord ++ tailWord_4791619) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4791620 : List Nat := [2, 3, 4, 1, 1, 1, 2, 1, 1, 5, 2]
def baseStart_4791620 : Nat := 118140960795 + 4791620 * 2 ^ 59
def prefixEnd_4791620 : Nat := 4983230072969 + 3 ^ 40 * 4791620 * 2
def baseEnd_4791620 : Nat := 2460404173696647998413747

theorem tailTrace_4791620 : CollatzResearch.WordTrace tailWord_4791620 prefixEnd_4791620 2460404173696647998413747 := by
  unfold tailWord_4791620
  simp only [CollatzResearch.WordTrace]
  refine ⟨87382369450393279194726157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116509825933857705592968209 87382369450393279194726157)
  ·
    refine ⟨32768388543897479698022309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 87382369450393279194726157 32768388543897479698022309)
    ·
      refine ⟨6144072851980777443379183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 32768388543897479698022309 6144072851980777443379183)
      ·
        refine ⟨9216109277971166165068775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6144072851980777443379183 9216109277971166165068775)
        ·
          refine ⟨13824163916956749247603163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9216109277971166165068775 13824163916956749247603163)
          ·
            refine ⟨20736245875435123871404745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13824163916956749247603163 20736245875435123871404745)
            ·
              refine ⟨15552184406576342903553559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20736245875435123871404745 15552184406576342903553559)
              ·
                refine ⟨23328276609864514355330339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15552184406576342903553559 23328276609864514355330339)
                ·
                  refine ⟨34992414914796771532995509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23328276609864514355330339 34992414914796771532995509)
                  ·
                    refine ⟨3280538898262197331218329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 34992414914796771532995509 3280538898262197331218329)
                    ·
                      refine ⟨2460404173696647998413747, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3280538898262197331218329 2460404173696647998413747)
                      ·
                        rfl

theorem cell23_4791620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 2, 1, 1, 5, 2].length) (baseStart_4791620 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4791620 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4791620 prefixEnd_4791620 := by exact prefixLift 4791620
  have htrace : WordTrace (prefixWord ++ tailWord_4791620) baseStart_4791620 baseEnd_4791620 := by
    simpa [prefixWord, tailWord_4791620, baseEnd_4791620] using wordTrace_append hprefix tailTrace_4791620
  have hstable : (prefixWord ++ tailWord_4791620).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4791620).length < 2 ^ (prefixWord ++ tailWord_4791620).sum := by decide
  have hdescent : baseEnd_4791620 < baseStart_4791620 := by decide
  rcases family_descends (prefixWord ++ tailWord_4791620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4791638 : List Nat := [5, 2, 3, 1, 1, 1, 3, 2, 1, 4]
def baseStart_4791638 : Nat := 118140960795 + 4791638 * 2 ^ 59
def prefixEnd_4791638 : Nat := 4983230072969 + 3 ^ 40 * 4791638 * 2
def baseEnd_4791638 : Nat := 820137805449476309329555

theorem tailTrace_4791638 : CollatzResearch.WordTrace tailWord_4791638 prefixEnd_4791638 820137805449476309329555 := by
  unfold tailWord_4791638
  simp only [CollatzResearch.WordTrace]
  refine ⟨10922837213420084216475473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 116510263609814231642405045 10922837213420084216475473)
  ·
    refine ⟨8192127910065063162356605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10922837213420084216475473 8192127910065063162356605)
    ·
      refine ⟨3072047966274398685883727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8192127910065063162356605 3072047966274398685883727)
      ·
        refine ⟨4608071949411598028825591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3072047966274398685883727 4608071949411598028825591)
        ·
          refine ⟨6912107924117397043238387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4608071949411598028825591 6912107924117397043238387)
          ·
            refine ⟨10368161886176095564857581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6912107924117397043238387 10368161886176095564857581)
            ·
              refine ⟨3888060707316035836821593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10368161886176095564857581 3888060707316035836821593)
              ·
                refine ⟨2916045530487026877616195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3888060707316035836821593 2916045530487026877616195)
                ·
                  refine ⟨4374068295730540316424293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2916045530487026877616195 4374068295730540316424293)
                  ·
                    refine ⟨820137805449476309329555, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4374068295730540316424293 820137805449476309329555)
                    ·
                      rfl

theorem cell23_4791638_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 1, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 1, 1, 3, 2, 1, 4].length) (baseStart_4791638 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4791638 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4791638 prefixEnd_4791638 := by exact prefixLift 4791638
  have htrace : WordTrace (prefixWord ++ tailWord_4791638) baseStart_4791638 baseEnd_4791638 := by
    simpa [prefixWord, tailWord_4791638, baseEnd_4791638] using wordTrace_append hprefix tailTrace_4791638
  have hstable : (prefixWord ++ tailWord_4791638).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4791638).length < 2 ^ (prefixWord ++ tailWord_4791638).sum := by decide
  have hdescent : baseEnd_4791638 < baseStart_4791638 := by decide
  rcases family_descends (prefixWord ++ tailWord_4791638) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4791639 : List Nat := [1, 1, 3, 2, 3, 2, 11]
def baseStart_4791639 : Nat := 118140960795 + 4791639 * 2 ^ 59
def prefixEnd_4791639 : Nat := 4983230072969 + 3 ^ 40 * 4791639 * 2
def baseEnd_4791639 : Nat := 30375480615173869433039

theorem tailTrace_4791639 : CollatzResearch.WordTrace tailWord_4791639 prefixEnd_4791639 30375480615173869433039 := by
  unfold tailWord_4791639
  simp only [CollatzResearch.WordTrace]
  refine ⟨174765431887717724634393971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116510287925145149756262647 174765431887717724634393971)
  ·
    refine ⟨262148147831576586951590957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 174765431887717724634393971 262148147831576586951590957)
    ·
      refine ⟨98305555436841220106846609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 262148147831576586951590957 98305555436841220106846609)
      ·
        refine ⟨73729166577630915080134957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 98305555436841220106846609 73729166577630915080134957)
        ·
          refine ⟨27648437466611593155050609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 73729166577630915080134957 27648437466611593155050609)
          ·
            refine ⟨20736328099958694866287957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27648437466611593155050609 20736328099958694866287957)
            ·
              refine ⟨30375480615173869433039, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 20736328099958694866287957 30375480615173869433039)
              ·
                rfl

theorem cell23_4791639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 11].length) (baseStart_4791639 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4791639 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4791639 prefixEnd_4791639 := by exact prefixLift 4791639
  have htrace : WordTrace (prefixWord ++ tailWord_4791639) baseStart_4791639 baseEnd_4791639 := by
    simpa [prefixWord, tailWord_4791639, baseEnd_4791639] using wordTrace_append hprefix tailTrace_4791639
  have hstable : (prefixWord ++ tailWord_4791639).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4791639).length < 2 ^ (prefixWord ++ tailWord_4791639).sum := by decide
  have hdescent : baseEnd_4791639 < baseStart_4791639 := by decide
  rcases family_descends (prefixWord ++ tailWord_4791639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4791660 : List Nat := [2, 2, 1, 1, 5, 1, 4, 1, 2, 4]
def baseStart_4791660 : Nat := 118140960795 + 4791660 * 2 ^ 59
def prefixEnd_4791660 : Nat := 4983230072969 + 3 ^ 40 * 4791660 * 2
def baseEnd_4791660 : Nat := 820141570974275947304521

theorem tailTrace_4791660 : CollatzResearch.WordTrace tailWord_4791660 prefixEnd_4791660 820141570974275947304521 := by
  unfold tailWord_4791660
  simp only [CollatzResearch.WordTrace]
  refine ⟨87383098910320822610454217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116510798547094430147272289 87383098910320822610454217)
  ·
    refine ⟨65537324182740616957840663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 87383098910320822610454217 65537324182740616957840663)
    ·
      refine ⟨98305986274110925436760995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65537324182740616957840663 98305986274110925436760995)
      ·
        refine ⟨147458979411166388155141493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 98305986274110925436760995 147458979411166388155141493)
        ·
          refine ⟨13824279319796848889544515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 147458979411166388155141493 13824279319796848889544515)
          ·
            refine ⟨20736418979695273334316773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13824279319796848889544515 20736418979695273334316773)
            ·
              refine ⟨3888078558692863750184395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 20736418979695273334316773 3888078558692863750184395)
              ·
                refine ⟨5832117838039295625276593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3888078558692863750184395 5832117838039295625276593)
                ·
                  refine ⟨4374088378529471718957445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5832117838039295625276593 4374088378529471718957445)
                  ·
                    refine ⟨820141570974275947304521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4374088378529471718957445 820141570974275947304521)
                    ·
                      rfl

theorem cell23_4791660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 2, 4].length) (baseStart_4791660 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4791660 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4791660 prefixEnd_4791660 := by exact prefixLift 4791660
  have htrace : WordTrace (prefixWord ++ tailWord_4791660) baseStart_4791660 baseEnd_4791660 := by
    simpa [prefixWord, tailWord_4791660, baseEnd_4791660] using wordTrace_append hprefix tailTrace_4791660
  have hstable : (prefixWord ++ tailWord_4791660).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4791660).length < 2 ^ (prefixWord ++ tailWord_4791660).sum := by decide
  have hdescent : baseEnd_4791660 < baseStart_4791660 := by decide
  rcases family_descends (prefixWord ++ tailWord_4791660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4791683 : List Nat := [1, 1, 1, 3, 5, 2, 1, 2, 1, 3, 3]
def baseStart_4791683 : Nat := 118140960795 + 4791683 * 2 ^ 59
def prefixEnd_4791683 : Nat := 4983230072969 + 3 ^ 40 * 4791683 * 2
def baseEnd_4791683 : Nat := 2460436522977881251925957

theorem tailTrace_4791683 : CollatzResearch.WordTrace tailWord_4791683 prefixEnd_4791683 2460436522977881251925957 := by
  unfold tailWord_4791683
  simp only [CollatzResearch.WordTrace]
  refine ⟨174767036699558320148995703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116511357799705546765997135 174767036699558320148995703)
  ·
    refine ⟨262150555049337480223493555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 174767036699558320148995703 262150555049337480223493555)
    ·
      refine ⟨393225832574006220335240333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 262150555049337480223493555 393225832574006220335240333)
      ·
        refine ⟨147459687215252332625715125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 393225832574006220335240333 147459687215252332625715125)
        ·
          refine ⟨13824345676429906183660793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 147459687215252332625715125 13824345676429906183660793)
          ·
            refine ⟨10368259257322429637745595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13824345676429906183660793 10368259257322429637745595)
            ·
              refine ⟨15552388885983644456618393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10368259257322429637745595 15552388885983644456618393)
              ·
                refine ⟨11664291664487733342463795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15552388885983644456618393 11664291664487733342463795)
                ·
                  refine ⟨17496437496731600013695693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11664291664487733342463795 17496437496731600013695693)
                  ·
                    refine ⟨6561164061274350005135885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17496437496731600013695693 6561164061274350005135885)
                    ·
                      refine ⟨2460436522977881251925957, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6561164061274350005135885 2460436522977881251925957)
                      ·
                        rfl

theorem cell23_4791683_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 2, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 2, 1, 2, 1, 3, 3].length) (baseStart_4791683 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4791683 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4791683 prefixEnd_4791683 := by exact prefixLift 4791683
  have htrace : WordTrace (prefixWord ++ tailWord_4791683) baseStart_4791683 baseEnd_4791683 := by
    simpa [prefixWord, tailWord_4791683, baseEnd_4791683] using wordTrace_append hprefix tailTrace_4791683
  have hstable : (prefixWord ++ tailWord_4791683).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4791683).length < 2 ^ (prefixWord ++ tailWord_4791683).sum := by decide
  have hdescent : baseEnd_4791683 < baseStart_4791683 := by decide
  rcases family_descends (prefixWord ++ tailWord_4791683) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4791699 : List Nat := [1, 1, 1, 2, 1, 2, 1, 1, 5, 8]
def baseStart_4791699 : Nat := 118140960795 + 4791699 * 2 ^ 59
def prefixEnd_4791699 : Nat := 4983230072969 + 3 ^ 40 * 4791699 * 2
def baseEnd_4791699 : Nat := 820148246222784396441961

theorem tailTrace_4791699 : CollatzResearch.WordTrace tailWord_4791699 prefixEnd_4791699 820148246222784396441961 := by
  unfold tailWord_4791699
  simp only [CollatzResearch.WordTrace]
  refine ⟨174767620267500354881578151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116511746845000236587718767 174767620267500354881578151)
  ·
    refine ⟨262151430401250532322367227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 174767620267500354881578151 262151430401250532322367227)
    ·
      refine ⟨393227145601875798483550841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 262151430401250532322367227 393227145601875798483550841)
      ·
        refine ⟨294920359201406848862663131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 393227145601875798483550841 294920359201406848862663131)
        ·
          refine ⟨442380538802110273293994697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 294920359201406848862663131 442380538802110273293994697)
          ·
            refine ⟨331785404101582704970496023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 442380538802110273293994697 331785404101582704970496023)
            ·
              refine ⟨497678106152374057455744035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 331785404101582704970496023 497678106152374057455744035)
              ·
                refine ⟨746517159228561086183616053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 497678106152374057455744035 746517159228561086183616053)
                ·
                  refine ⟨69985983677677601829714005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 746517159228561086183616053 69985983677677601829714005)
                  ·
                    refine ⟨820148246222784396441961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 69985983677677601829714005 820148246222784396441961)
                    ·
                      rfl

theorem cell23_4791699_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 1, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 1, 5, 8].length) (baseStart_4791699 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4791699 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4791699 prefixEnd_4791699 := by exact prefixLift 4791699
  have htrace : WordTrace (prefixWord ++ tailWord_4791699) baseStart_4791699 baseEnd_4791699 := by
    simpa [prefixWord, tailWord_4791699, baseEnd_4791699] using wordTrace_append hprefix tailTrace_4791699
  have hstable : (prefixWord ++ tailWord_4791699).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4791699).length < 2 ^ (prefixWord ++ tailWord_4791699).sum := by decide
  have hdescent : baseEnd_4791699 < baseStart_4791699 := by decide
  rcases family_descends (prefixWord ++ tailWord_4791699) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4791706 : List Nat := [3, 1, 1, 4, 1, 1, 1, 1, 1, 5, 4]
def baseStart_4791706 : Nat := 118140960795 + 4791706 * 2 ^ 59
def prefixEnd_4791706 : Nat := 4983230072969 + 3 ^ 40 * 4791706 * 2
def baseEnd_4791706 : Nat := 2460448333032934661938351

theorem tailTrace_4791706 : CollatzResearch.WordTrace tailWord_4791706 prefixEnd_4791706 2460448333032934661938351 := by
  unfold tailWord_4791706
  simp only [CollatzResearch.WordTrace]
  refine ⟨43691968894618748769270743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 116511917052316663384721981 43691968894618748769270743)
  ·
    refine ⟨65537953341928123153906115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43691968894618748769270743 65537953341928123153906115)
    ·
      refine ⟨98306930012892184730859173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65537953341928123153906115 98306930012892184730859173)
      ·
        refine ⟨18432549377417284637036095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 98306930012892184730859173 18432549377417284637036095)
        ·
          refine ⟨27648824066125926955554143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18432549377417284637036095 27648824066125926955554143)
          ·
            refine ⟨41473236099188890433331215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27648824066125926955554143 41473236099188890433331215)
            ·
              refine ⟨62209854148783335649996823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41473236099188890433331215 62209854148783335649996823)
              ·
                refine ⟨93314781223175003474995235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 62209854148783335649996823 93314781223175003474995235)
                ·
                  refine ⟨139972171834762505212492853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 93314781223175003474995235 139972171834762505212492853)
                  ·
                    refine ⟨13122391109508984863671205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 139972171834762505212492853 13122391109508984863671205)
                    ·
                      refine ⟨2460448333032934661938351, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13122391109508984863671205 2460448333032934661938351)
                      ·
                        rfl

theorem cell23_4791706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 1, 1, 1, 5, 4].length) (baseStart_4791706 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4791706 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4791706 prefixEnd_4791706 := by exact prefixLift 4791706
  have htrace : WordTrace (prefixWord ++ tailWord_4791706) baseStart_4791706 baseEnd_4791706 := by
    simpa [prefixWord, tailWord_4791706, baseEnd_4791706] using wordTrace_append hprefix tailTrace_4791706
  have hstable : (prefixWord ++ tailWord_4791706).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4791706).length < 2 ^ (prefixWord ++ tailWord_4791706).sum := by decide
  have hdescent : baseEnd_4791706 < baseStart_4791706 := by decide
  rcases family_descends (prefixWord ++ tailWord_4791706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4791776 : List Nat := [2, 1, 1, 3, 1, 1, 2, 1, 6, 5]
def baseStart_4791776 : Nat := 118140960795 + 4791776 * 2 ^ 59
def prefixEnd_4791776 : Nat := 4983230072969 + 3 ^ 40 * 4791776 * 2
def baseEnd_4791776 : Nat := 820161425559583129354343

theorem tailTrace_4791776 : CollatzResearch.WordTrace tailWord_4791776 prefixEnd_4791776 820161425559583129354343 := by
  unfold tailWord_4791776
  simp only [CollatzResearch.WordTrace]
  refine ⟨87385214344110698516065591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116513619125480931354754121 87385214344110698516065591)
  ·
    refine ⟨131077821516166047774098387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87385214344110698516065591 131077821516166047774098387)
    ·
      refine ⟨196616732274249071661147581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 131077821516166047774098387 196616732274249071661147581)
      ·
        refine ⟨73731274602843401872930343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 196616732274249071661147581 73731274602843401872930343)
        ·
          refine ⟨110596911904265102809395515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 73731274602843401872930343 110596911904265102809395515)
          ·
            refine ⟨165895367856397654214093273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 110596911904265102809395515 165895367856397654214093273)
            ·
              refine ⟨124421525892298240660569955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 165895367856397654214093273 124421525892298240660569955)
              ·
                refine ⟨186632288838447360990854933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 124421525892298240660569955 186632288838447360990854933)
                ·
                  refine ⟨8748388539302220046446325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 186632288838447360990854933 8748388539302220046446325)
                  ·
                    refine ⟨820161425559583129354343, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8748388539302220046446325 820161425559583129354343)
                    ·
                      rfl

theorem cell23_4791776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 2, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 2, 1, 6, 5].length) (baseStart_4791776 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4791776 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4791776 prefixEnd_4791776 := by exact prefixLift 4791776
  have htrace : WordTrace (prefixWord ++ tailWord_4791776) baseStart_4791776 baseEnd_4791776 := by
    simpa [prefixWord, tailWord_4791776, baseEnd_4791776] using wordTrace_append hprefix tailTrace_4791776
  have hstable : (prefixWord ++ tailWord_4791776).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4791776).length < 2 ^ (prefixWord ++ tailWord_4791776).sum := by decide
  have hdescent : baseEnd_4791776 < baseStart_4791776 := by decide
  rcases family_descends (prefixWord ++ tailWord_4791776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4791797 : List Nat := [1, 3, 5, 1, 1, 1, 3, 3, 5]
def baseStart_4791797 : Nat := 118140960795 + 4791797 * 2 ^ 59
def prefixEnd_4791797 : Nat := 4983230072969 + 3 ^ 40 * 4791797 * 2
def baseEnd_4791797 : Nat := 273388339974721533988937

theorem tailTrace_4791797 : CollatzResearch.WordTrace tailWord_4791797 prefixEnd_4791797 273388339974721533988937 := by
  unfold tailWord_4791797
  simp only [CollatzResearch.WordTrace]
  refine ⟨174771194621145317618645645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116514129747430211745763763 174771194621145317618645645)
  ·
    refine ⟨65539197982929494106992117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 174771194621145317618645645 65539197982929494106992117)
    ·
      refine ⟨6144299810899640072530511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 65539197982929494106992117 6144299810899640072530511)
      ·
        refine ⟨9216449716349460108795767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6144299810899640072530511 9216449716349460108795767)
        ·
          refine ⟨13824674574524190163193651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9216449716349460108795767 13824674574524190163193651)
          ·
            refine ⟨20737011861786285244790477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13824674574524190163193651 20737011861786285244790477)
            ·
              refine ⟨7776379448169856966796429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20737011861786285244790477 7776379448169856966796429)
              ·
                refine ⟨2916142293063696362548661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7776379448169856966796429 2916142293063696362548661)
                ·
                  refine ⟨273388339974721533988937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2916142293063696362548661 273388339974721533988937)
                  ·
                    rfl

theorem cell23_4791797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 3, 3, 5].length) (baseStart_4791797 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4791797 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4791797 prefixEnd_4791797 := by exact prefixLift 4791797
  have htrace : WordTrace (prefixWord ++ tailWord_4791797) baseStart_4791797 baseEnd_4791797 := by
    simpa [prefixWord, tailWord_4791797, baseEnd_4791797] using wordTrace_append hprefix tailTrace_4791797
  have hstable : (prefixWord ++ tailWord_4791797).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4791797).length < 2 ^ (prefixWord ++ tailWord_4791797).sum := by decide
  have hdescent : baseEnd_4791797 < baseStart_4791797 := by decide
  rcases family_descends (prefixWord ++ tailWord_4791797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4791810 : List Nat := [3, 4, 1, 2, 1, 1, 1, 1, 4, 5]
def baseStart_4791810 : Nat := 118140960795 + 4791810 * 2 ^ 59
def prefixEnd_4791810 : Nat := 4983230072969 + 3 ^ 40 * 4791810 * 2
def baseEnd_4791810 : Nat := 820167245007000751679291

theorem tailTrace_4791810 : CollatzResearch.WordTrace tailWord_4791810 prefixEnd_4791810 820167245007000751679291 := by
  unfold tailWord_4791810
  simp only [CollatzResearch.WordTrace]
  refine ⟨43692917192524555209717221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 116514445846732147225912589 43692917192524555209717221)
  ·
    refine ⟨8192421973598354101821979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 43692917192524555209717221 8192421973598354101821979)
    ·
      refine ⟨12288632960397531152732969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8192421973598354101821979 12288632960397531152732969)
      ·
        refine ⟨9216474720298148364549727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12288632960397531152732969 9216474720298148364549727)
        ·
          refine ⟨13824712080447222546824591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9216474720298148364549727 13824712080447222546824591)
          ·
            refine ⟨20737068120670833820236887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13824712080447222546824591 20737068120670833820236887)
            ·
              refine ⟨31105602181006250730355331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20737068120670833820236887 31105602181006250730355331)
              ·
                refine ⟨46658403271509376095532997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31105602181006250730355331 46658403271509376095532997)
                ·
                  refine ⟨8748450613408008017912437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 46658403271509376095532997 8748450613408008017912437)
                  ·
                    refine ⟨820167245007000751679291, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8748450613408008017912437 820167245007000751679291)
                    ·
                      rfl

theorem cell23_4791810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 1, 1, 4, 5].length) (baseStart_4791810 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4791810 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4791810 prefixEnd_4791810 := by exact prefixLift 4791810
  have htrace : WordTrace (prefixWord ++ tailWord_4791810) baseStart_4791810 baseEnd_4791810 := by
    simpa [prefixWord, tailWord_4791810, baseEnd_4791810] using wordTrace_append hprefix tailTrace_4791810
  have hstable : (prefixWord ++ tailWord_4791810).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4791810).length < 2 ^ (prefixWord ++ tailWord_4791810).sum := by decide
  have hdescent : baseEnd_4791810 < baseStart_4791810 := by decide
  rcases family_descends (prefixWord ++ tailWord_4791810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4791856 : List Nat := [2, 1, 1, 1, 2, 3, 1, 2, 1, 1, 8]
def baseStart_4791856 : Nat := 118140960795 + 4791856 * 2 ^ 59
def prefixEnd_4791856 : Nat := 4983230072969 + 3 ^ 40 * 4791856 * 2
def baseEnd_4791856 : Nat := 2460525355131109075062661

theorem tailTrace_4791856 : CollatzResearch.WordTrace tailWord_4791856 prefixEnd_4791856 2460525355131109075062661 := by
  unfold tailWord_4791856
  simp only [CollatzResearch.WordTrace]
  refine ⟨87386673263965785347521711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116515564351954380463362281 87386673263965785347521711)
  ·
    refine ⟨131080009895948678021282567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87386673263965785347521711 131080009895948678021282567)
    ·
      refine ⟨196620014843923017031923851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 131080009895948678021282567 196620014843923017031923851)
      ·
        refine ⟨294930022265884525547885777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 196620014843923017031923851 294930022265884525547885777)
        ·
          refine ⟨221197516699413394160914333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 294930022265884525547885777 221197516699413394160914333)
          ·
            refine ⟨82949068762280022810342875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 221197516699413394160914333 82949068762280022810342875)
            ·
              refine ⟨124423603143420034215514313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 82949068762280022810342875 124423603143420034215514313)
              ·
                refine ⟨93317702357565025661635735, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 124423603143420034215514313 93317702357565025661635735)
                ·
                  refine ⟨139976553536347538492453603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 93317702357565025661635735 139976553536347538492453603)
                  ·
                    refine ⟨209964830304521307738680405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 139976553536347538492453603 209964830304521307738680405)
                    ·
                      refine ⟨2460525355131109075062661, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 209964830304521307738680405 2460525355131109075062661)
                      ·
                        rfl

theorem cell23_4791856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 1, 2, 1, 1, 8].length) (baseStart_4791856 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4791856 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4791856 prefixEnd_4791856 := by exact prefixLift 4791856
  have htrace : WordTrace (prefixWord ++ tailWord_4791856) baseStart_4791856 baseEnd_4791856 := by
    simpa [prefixWord, tailWord_4791856, baseEnd_4791856] using wordTrace_append hprefix tailTrace_4791856
  have hstable : (prefixWord ++ tailWord_4791856).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4791856).length < 2 ^ (prefixWord ++ tailWord_4791856).sum := by decide
  have hdescent : baseEnd_4791856 < baseStart_4791856 := by decide
  rcases family_descends (prefixWord ++ tailWord_4791856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4791873 : List Nat := [1, 2, 5, 1, 1, 1, 2, 1, 1, 2, 6]
def baseStart_4791873 : Nat := 118140960795 + 4791873 * 2 ^ 59
def prefixEnd_4791873 : Nat := 4983230072969 + 3 ^ 40 * 4791873 * 2
def baseEnd_4791873 : Nat := 2460534084302235508550083

theorem tailTrace_4791873 : CollatzResearch.WordTrace tailWord_4791873 prefixEnd_4791873 2460534084302235508550083 := by
  unfold tailWord_4791873
  simp only [CollatzResearch.WordTrace]
  refine ⟨174773966568869982598412273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116515977712579988398941515 174773966568869982598412273)
  ·
    refine ⟨131080474926652486948809205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 174773966568869982598412273 131080474926652486948809205)
    ·
      refine ⟨12288794524373670651450863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 131080474926652486948809205 12288794524373670651450863)
      ·
        refine ⟨18433191786560505977176295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12288794524373670651450863 18433191786560505977176295)
        ·
          refine ⟨27649787679840758965764443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18433191786560505977176295 27649787679840758965764443)
          ·
            refine ⟨41474681519761138448646665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27649787679840758965764443 41474681519761138448646665)
            ·
              refine ⟨31106011139820853836484999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 41474681519761138448646665 31106011139820853836484999)
              ·
                refine ⟨46659016709731280754727499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31106011139820853836484999 46659016709731280754727499)
                ·
                  refine ⟨69988525064596921132091249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 46659016709731280754727499 69988525064596921132091249)
                  ·
                    refine ⟨52491393798447690849068437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 69988525064596921132091249 52491393798447690849068437)
                    ·
                      refine ⟨2460534084302235508550083, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 52491393798447690849068437 2460534084302235508550083)
                      ·
                        rfl

theorem cell23_4791873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 2, 1, 1, 2, 6].length) (baseStart_4791873 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4791873 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4791873 prefixEnd_4791873 := by exact prefixLift 4791873
  have htrace : WordTrace (prefixWord ++ tailWord_4791873) baseStart_4791873 baseEnd_4791873 := by
    simpa [prefixWord, tailWord_4791873, baseEnd_4791873] using wordTrace_append hprefix tailTrace_4791873
  have hstable : (prefixWord ++ tailWord_4791873).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4791873).length < 2 ^ (prefixWord ++ tailWord_4791873).sum := by decide
  have hdescent : baseEnd_4791873 < baseStart_4791873 := by decide
  rcases family_descends (prefixWord ++ tailWord_4791873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4791900 : List Nat := [2, 2, 4, 1, 2, 1, 2, 1, 3, 5]
def baseStart_4791900 : Nat := 118140960795 + 4791900 * 2 ^ 59
def prefixEnd_4791900 : Nat := 4983230072969 + 3 ^ 40 * 4791900 * 2
def baseEnd_4791900 : Nat := 820182649426635634304153

theorem tailTrace_4791900 : CollatzResearch.WordTrace tailWord_4791900 prefixEnd_4791900 820182649426635634304153 := by
  unfold tailWord_4791900
  simp only [CollatzResearch.WordTrace]
  refine ⟨87387475669886083104822577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116516634226514777473096769 87387475669886083104822577)
  ·
    refine ⟨65540606752414562328616933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 87387475669886083104822577 65540606752414562328616933)
    ·
      refine ⟨12288863766077730436615675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 65540606752414562328616933 12288863766077730436615675)
      ·
        refine ⟨18433295649116595654923513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12288863766077730436615675 18433295649116595654923513)
        ·
          refine ⟨13824971736837446741192635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18433295649116595654923513 13824971736837446741192635)
          ·
            refine ⟨20737457605256170111788953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13824971736837446741192635 20737457605256170111788953)
            ·
              refine ⟨15553093203942127583841715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20737457605256170111788953 15553093203942127583841715)
              ·
                refine ⟨23329639805913191375762573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15553093203942127583841715 23329639805913191375762573)
                ·
                  refine ⟨8748614927217446765910965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23329639805913191375762573 8748614927217446765910965)
                  ·
                    refine ⟨820182649426635634304153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8748614927217446765910965 820182649426635634304153)
                    ·
                      rfl

theorem cell23_4791900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 2, 1, 3, 5].length) (baseStart_4791900 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4791900 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4791900 prefixEnd_4791900 := by exact prefixLift 4791900
  have htrace : WordTrace (prefixWord ++ tailWord_4791900) baseStart_4791900 baseEnd_4791900 := by
    simpa [prefixWord, tailWord_4791900, baseEnd_4791900] using wordTrace_append hprefix tailTrace_4791900
  have hstable : (prefixWord ++ tailWord_4791900).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4791900).length < 2 ^ (prefixWord ++ tailWord_4791900).sum := by decide
  have hdescent : baseEnd_4791900 < baseStart_4791900 := by decide
  rcases family_descends (prefixWord ++ tailWord_4791900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4791901 : List Nat := [1, 4, 4, 2, 1, 2, 1, 1, 2, 2, 3]
def baseStart_4791901 : Nat := 118140960795 + 4791901 * 2 ^ 59
def prefixEnd_4791901 : Nat := 4983230072969 + 3 ^ 40 * 4791901 * 2
def baseEnd_4791901 : Nat := 2460548461760561398999955

theorem tailTrace_4791901 : CollatzResearch.WordTrace tailWord_4791901 prefixEnd_4791901 2460548461760561398999955 := by
  unfold tailWord_4791901
  simp only [CollatzResearch.WordTrace]
  refine ⟨174774987812768543380431557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116516658541845695586954371 174774987812768543380431557)
  ·
    refine ⟨32770310214894101883830917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 174774987812768543380431557 32770310214894101883830917)
    ·
      refine ⟨6144433165292644103218297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 32770310214894101883830917 6144433165292644103218297)
      ·
        refine ⟨4608324873969483077413723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6144433165292644103218297 4608324873969483077413723)
        ·
          refine ⟨6912487310954224616120585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4608324873969483077413723 6912487310954224616120585)
          ·
            refine ⟨5184365483215668462090439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6912487310954224616120585 5184365483215668462090439)
            ·
              refine ⟨7776548224823502693135659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5184365483215668462090439 7776548224823502693135659)
              ·
                refine ⟨11664822337235254039703489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7776548224823502693135659 11664822337235254039703489)
                ·
                  refine ⟨8748616752926440529777617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11664822337235254039703489 8748616752926440529777617)
                  ·
                    refine ⟨6561462564694830397333213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8748616752926440529777617 6561462564694830397333213)
                    ·
                      refine ⟨2460548461760561398999955, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6561462564694830397333213 2460548461760561398999955)
                      ·
                        rfl

theorem cell23_4791901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 1, 2, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 1, 2, 1, 1, 2, 2, 3].length) (baseStart_4791901 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4791901 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4791901 prefixEnd_4791901 := by exact prefixLift 4791901
  have htrace : WordTrace (prefixWord ++ tailWord_4791901) baseStart_4791901 baseEnd_4791901 := by
    simpa [prefixWord, tailWord_4791901, baseEnd_4791901] using wordTrace_append hprefix tailTrace_4791901
  have hstable : (prefixWord ++ tailWord_4791901).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4791901).length < 2 ^ (prefixWord ++ tailWord_4791901).sum := by decide
  have hdescent : baseEnd_4791901 < baseStart_4791901 := by decide
  rcases family_descends (prefixWord ++ tailWord_4791901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4791907 : List Nat := [1, 1, 1, 5, 1, 3, 3, 1, 2, 3, 2]
def baseStart_4791907 : Nat := 118140960795 + 4791907 * 2 ^ 59
def prefixEnd_4791907 : Nat := 4983230072969 + 3 ^ 40 * 4791907 * 2
def baseEnd_4791907 : Nat := 2460551542644488375524927

theorem tailTrace_4791907 : CollatzResearch.WordTrace tailWord_4791907 prefixEnd_4791907 2460551542644488375524927 := by
  unfold tailWord_4791907
  simp only [CollatzResearch.WordTrace]
  refine ⟨174775206650746806405149975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116516804433831204270099983 174775206650746806405149975)
  ·
    refine ⟨262162809976120209607724963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 174775206650746806405149975 262162809976120209607724963)
    ·
      refine ⟨393244214964180314411587445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 262162809976120209607724963 393244214964180314411587445)
      ·
        refine ⟨36866645152891904476086323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 393244214964180314411587445 36866645152891904476086323)
        ·
          refine ⟨55299967729337856714129485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36866645152891904476086323 55299967729337856714129485)
          ·
            refine ⟨20737487898501696267798557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 55299967729337856714129485 20737487898501696267798557)
            ·
              refine ⟨7776557961938136100424459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20737487898501696267798557 7776557961938136100424459)
              ·
                refine ⟨11664836942907204150636689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7776557961938136100424459 11664836942907204150636689)
                ·
                  refine ⟨8748627707180403112977517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11664836942907204150636689 8748627707180403112977517)
                  ·
                    refine ⟨3280735390192651167366569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8748627707180403112977517 3280735390192651167366569)
                    ·
                      refine ⟨2460551542644488375524927, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3280735390192651167366569 2460551542644488375524927)
                      ·
                        rfl

theorem cell23_4791907_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 3, 1, 2, 3, 2].length) (baseStart_4791907 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4791907 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4791907 prefixEnd_4791907 := by exact prefixLift 4791907
  have htrace : WordTrace (prefixWord ++ tailWord_4791907) baseStart_4791907 baseEnd_4791907 := by
    simpa [prefixWord, tailWord_4791907, baseEnd_4791907] using wordTrace_append hprefix tailTrace_4791907
  have hstable : (prefixWord ++ tailWord_4791907).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4791907).length < 2 ^ (prefixWord ++ tailWord_4791907).sum := by decide
  have hdescent : baseEnd_4791907 < baseStart_4791907 := by decide
  rcases family_descends (prefixWord ++ tailWord_4791907) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4791913 : List Nat := [1, 2, 1, 1, 1, 4, 4, 2, 1, 6]
def baseStart_4791913 : Nat := 118140960795 + 4791913 * 2 ^ 59
def prefixEnd_4791913 : Nat := 4983230072969 + 3 ^ 40 * 4791913 * 2
def baseEnd_4791913 : Nat := 820184874509471784016633

theorem tailTrace_4791913 : CollatzResearch.WordTrace tailWord_4791913 prefixEnd_4791913 820184874509471784016633 := by
  unfold tailWord_4791913
  simp only [CollatzResearch.WordTrace]
  refine ⟨174775425488725069429868393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116516950325816712953245595 174775425488725069429868393)
  ·
    refine ⟨131081569116543802072401295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 174775425488725069429868393 131081569116543802072401295)
    ·
      refine ⟨196622353674815703108601943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 131081569116543802072401295 196622353674815703108601943)
      ·
        refine ⟨294933530512223554662902915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 196622353674815703108601943 294933530512223554662902915)
        ·
          refine ⟨442400295768335331994354373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 294933530512223554662902915 442400295768335331994354373)
          ·
            refine ⟨82950055456562874748941445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 442400295768335331994354373 82950055456562874748941445)
            ·
              refine ⟨15553135398105539015426521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 82950055456562874748941445 15553135398105539015426521)
              ·
                refine ⟨11664851548579154261569891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15553135398105539015426521 11664851548579154261569891)
                ·
                  refine ⟨17497277322868731392354837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11664851548579154261569891 17497277322868731392354837)
                  ·
                    refine ⟨820184874509471784016633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17497277322868731392354837 820184874509471784016633)
                    ·
                      rfl

theorem cell23_4791913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 4, 2, 1, 6].length) (baseStart_4791913 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4791913 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4791913 prefixEnd_4791913 := by exact prefixLift 4791913
  have htrace : WordTrace (prefixWord ++ tailWord_4791913) baseStart_4791913 baseEnd_4791913 := by
    simpa [prefixWord, tailWord_4791913, baseEnd_4791913] using wordTrace_append hprefix tailTrace_4791913
  have hstable : (prefixWord ++ tailWord_4791913).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4791913).length < 2 ^ (prefixWord ++ tailWord_4791913).sum := by decide
  have hdescent : baseEnd_4791913 < baseStart_4791913 := by decide
  rcases family_descends (prefixWord ++ tailWord_4791913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4791914 : List Nat := [3, 1, 3, 2, 1, 2, 1, 5, 1, 1, 3]
def baseStart_4791914 : Nat := 118140960795 + 4791914 * 2 ^ 59
def prefixEnd_4791914 : Nat := 4983230072969 + 3 ^ 40 * 4791914 * 2
def baseEnd_4791914 : Nat := 2460555137009069848137395

theorem tailTrace_4791914 : CollatzResearch.WordTrace tailWord_4791914 prefixEnd_4791914 2460555137009069848137395 := by
  unfold tailWord_4791914
  simp only [CollatzResearch.WordTrace]
  refine ⟨43693865490430361650163699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 116516974641147631067103197 43693865490430361650163699)
  ·
    refine ⟨65540798235645542475245549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43693865490430361650163699 65540798235645542475245549)
    ·
      refine ⟨24577799338367078428217081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 65540798235645542475245549 24577799338367078428217081)
      ·
        refine ⟨18433349503775308821162811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24577799338367078428217081 18433349503775308821162811)
        ·
          refine ⟨27650024255662963231744217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18433349503775308821162811 27650024255662963231744217)
          ·
            refine ⟨20737518191747222423808163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27650024255662963231744217 20737518191747222423808163)
            ·
              refine ⟨31106277287620833635712245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20737518191747222423808163 31106277287620833635712245)
              ·
                refine ⟨2916213495714453153348023, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 31106277287620833635712245 2916213495714453153348023)
                ·
                  refine ⟨4374320243571679730022035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2916213495714453153348023 4374320243571679730022035)
                  ·
                    refine ⟨6561480365357519595033053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4374320243571679730022035 6561480365357519595033053)
                    ·
                      refine ⟨2460555137009069848137395, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6561480365357519595033053 2460555137009069848137395)
                      ·
                        rfl

theorem cell23_4791914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 1, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 1, 5, 1, 1, 3].length) (baseStart_4791914 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4791914 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4791914 prefixEnd_4791914 := by exact prefixLift 4791914
  have htrace : WordTrace (prefixWord ++ tailWord_4791914) baseStart_4791914 baseEnd_4791914 := by
    simpa [prefixWord, tailWord_4791914, baseEnd_4791914] using wordTrace_append hprefix tailTrace_4791914
  have hstable : (prefixWord ++ tailWord_4791914).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4791914).length < 2 ^ (prefixWord ++ tailWord_4791914).sum := by decide
  have hdescent : baseEnd_4791914 < baseStart_4791914 := by decide
  rcases family_descends (prefixWord ++ tailWord_4791914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4791917 : List Nat := [1, 5, 1, 1, 4, 1, 1, 3, 1, 5]
def baseStart_4791917 : Nat := 118140960795 + 4791917 * 2 ^ 59
def prefixEnd_4791917 : Nat := 4983230072969 + 3 ^ 40 * 4791917 * 2
def baseEnd_4791917 : Nat := 820185559150344445466627

theorem tailTrace_4791917 : CollatzResearch.WordTrace tailWord_4791917 prefixEnd_4791917 820185559150344445466627 := by
  unfold tailWord_4791917
  simp only [CollatzResearch.WordTrace]
  refine ⟨174775571380710578113014005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116517047587140385408676003 174775571380710578113014005)
  ·
    refine ⟨16385209816941616698095063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 174775571380710578113014005 16385209816941616698095063)
    ·
      refine ⟨24577814725412425047142595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16385209816941616698095063 24577814725412425047142595)
      ·
        refine ⟨36866722088118637570713893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24577814725412425047142595 36866722088118637570713893)
        ·
          refine ⟨6912510391522244544508855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 36866722088118637570713893 6912510391522244544508855)
          ·
            refine ⟨10368765587283366816763283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6912510391522244544508855 10368765587283366816763283)
            ·
              refine ⟨15553148380925050225144925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10368765587283366816763283 15553148380925050225144925)
              ·
                refine ⟨5832430642846893834429347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15553148380925050225144925 5832430642846893834429347)
                ·
                  refine ⟨8748645964270340751644021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5832430642846893834429347 8748645964270340751644021)
                  ·
                    refine ⟨820185559150344445466627, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8748645964270340751644021 820185559150344445466627)
                    ·
                      rfl

theorem cell23_4791917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 4, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 4, 1, 1, 3, 1, 5].length) (baseStart_4791917 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4791917 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4791917 prefixEnd_4791917 := by exact prefixLift 4791917
  have htrace : WordTrace (prefixWord ++ tailWord_4791917) baseStart_4791917 baseEnd_4791917 := by
    simpa [prefixWord, tailWord_4791917, baseEnd_4791917] using wordTrace_append hprefix tailTrace_4791917
  have hstable : (prefixWord ++ tailWord_4791917).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4791917).length < 2 ^ (prefixWord ++ tailWord_4791917).sum := by decide
  have hdescent : baseEnd_4791917 < baseStart_4791917 := by decide
  rcases family_descends (prefixWord ++ tailWord_4791917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4791930 : List Nat := [3, 1, 1, 1, 1, 1, 1, 8, 2, 4]
def baseStart_4791930 : Nat := 118140960795 + 4791930 * 2 ^ 59
def prefixEnd_4791930 : Nat := 4983230072969 + 3 ^ 40 * 4791930 * 2
def baseEnd_4791930 : Nat := 820187784233180595179107

theorem tailTrace_4791930 : CollatzResearch.WordTrace tailWord_4791930 prefixEnd_4791930 820187784233180595179107 := by
  unfold tailWord_4791930
  simp only [CollatzResearch.WordTrace]
  refine ⟨43694011382415870333309311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 116517363686442320888824829 43694011382415870333309311)
  ·
    refine ⟨65541017073623805499963967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43694011382415870333309311 65541017073623805499963967)
    ·
      refine ⟨98311525610435708249945951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65541017073623805499963967 98311525610435708249945951)
      ·
        refine ⟨147467288415653562374918927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 98311525610435708249945951 147467288415653562374918927)
        ·
          refine ⟨221200932623480343562378391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 147467288415653562374918927 221200932623480343562378391)
          ·
            refine ⟨331801398935220515343567587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 221200932623480343562378391 331801398935220515343567587)
            ·
              refine ⟨497702098402830773015351381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 331801398935220515343567587 497702098402830773015351381)
              ·
                refine ⟨5832446465658173121273649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 497702098402830773015351381 5832446465658173121273649)
                ·
                  refine ⟨4374334849243629840955237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5832446465658173121273649 4374334849243629840955237)
                  ·
                    refine ⟨820187784233180595179107, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4374334849243629840955237 820187784233180595179107)
                    ·
                      rfl

theorem cell23_4791930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 8, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 8, 2, 4].length) (baseStart_4791930 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4791930 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4791930 prefixEnd_4791930 := by exact prefixLift 4791930
  have htrace : WordTrace (prefixWord ++ tailWord_4791930) baseStart_4791930 baseEnd_4791930 := by
    simpa [prefixWord, tailWord_4791930, baseEnd_4791930] using wordTrace_append hprefix tailTrace_4791930
  have hstable : (prefixWord ++ tailWord_4791930).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4791930).length < 2 ^ (prefixWord ++ tailWord_4791930).sum := by decide
  have hdescent : baseEnd_4791930 < baseStart_4791930 := by decide
  rcases family_descends (prefixWord ++ tailWord_4791930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4791947 : List Nat := [1, 1, 1, 1, 4, 1, 7, 1, 2, 4]
def baseStart_4791947 : Nat := 118140960795 + 4791947 * 2 ^ 59
def prefixEnd_4791947 : Nat := 4983230072969 + 3 ^ 40 * 4791947 * 2
def baseEnd_4791947 : Nat := 820190693956889406341581

theorem tailTrace_4791947 : CollatzResearch.WordTrace tailWord_4791947 prefixEnd_4791947 820190693956889406341581 := by
  unfold tailWord_4791947
  simp only [CollatzResearch.WordTrace]
  refine ⟨174776665570601893236606095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116517777047067928824404063 174776665570601893236606095)
  ·
    refine ⟨262164998355902839854909143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 174776665570601893236606095 262164998355902839854909143)
    ·
      refine ⟨393247497533854259782363715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 262164998355902839854909143 393247497533854259782363715)
      ·
        refine ⟨589871246300781389673545573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 393247497533854259782363715 589871246300781389673545573)
        ·
          refine ⟨110600858681396510563789795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 589871246300781389673545573 110600858681396510563789795)
          ·
            refine ⟨165901288022094765845684693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 110600858681396510563789795 165901288022094765845684693)
            ·
              refine ⟨3888311438017846074508235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 165901288022094765845684693 3888311438017846074508235)
              ·
                refine ⟨5832467157026769111762353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3888311438017846074508235 5832467157026769111762353)
                ·
                  refine ⟨4374350367770076833821765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5832467157026769111762353 4374350367770076833821765)
                  ·
                    refine ⟨820190693956889406341581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4374350367770076833821765 820190693956889406341581)
                    ·
                      rfl

theorem cell23_4791947_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 7, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 7, 1, 2, 4].length) (baseStart_4791947 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4791947 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4791947 prefixEnd_4791947 := by exact prefixLift 4791947
  have htrace : WordTrace (prefixWord ++ tailWord_4791947) baseStart_4791947 baseEnd_4791947 := by
    simpa [prefixWord, tailWord_4791947, baseEnd_4791947] using wordTrace_append hprefix tailTrace_4791947
  have hstable : (prefixWord ++ tailWord_4791947).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4791947).length < 2 ^ (prefixWord ++ tailWord_4791947).sum := by decide
  have hdescent : baseEnd_4791947 < baseStart_4791947 := by decide
  rcases family_descends (prefixWord ++ tailWord_4791947) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4791950 : List Nat := [4, 1, 1, 3, 1, 3, 1, 1, 1, 1, 6]
def baseStart_4791950 : Nat := 118140960795 + 4791950 * 2 ^ 59
def prefixEnd_4791950 : Nat := 4983230072969 + 3 ^ 40 * 4791950 * 2
def baseEnd_4791950 : Nat := 2460573622312631707287229

theorem tailTrace_4791950 : CollatzResearch.WordTrace tailWord_4791950 prefixEnd_4791950 2460573622312631707287229 := by
  unfold tailWord_4791950
  simp only [CollatzResearch.WordTrace]
  refine ⟨21847096873698878093620663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 116517849993060683165976869 21847096873698878093620663)
  ·
    refine ⟨32770645310548317140430995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21847096873698878093620663 32770645310548317140430995)
    ·
      refine ⟨49155967965822475710646493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32770645310548317140430995 49155967965822475710646493)
      ·
        refine ⟨18433487987183428391492435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 49155967965822475710646493 18433487987183428391492435)
        ·
          refine ⟨27650231980775142587238653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18433487987183428391492435 27650231980775142587238653)
          ·
            refine ⟨10368836992790678470214495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27650231980775142587238653 10368836992790678470214495)
            ·
              refine ⟨15553255489186017705321743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10368836992790678470214495 15553255489186017705321743)
              ·
                refine ⟨23329883233779026557982615, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15553255489186017705321743 23329883233779026557982615)
                ·
                  refine ⟨34994824850668539836973923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23329883233779026557982615 34994824850668539836973923)
                  ·
                    refine ⟨52492237276002809755460885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 34994824850668539836973923 52492237276002809755460885)
                    ·
                      refine ⟨2460573622312631707287229, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 52492237276002809755460885 2460573622312631707287229)
                      ·
                        rfl

theorem cell23_4791950_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 3, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 3, 1, 1, 1, 1, 6].length) (baseStart_4791950 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4791950 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4791950 prefixEnd_4791950 := by exact prefixLift 4791950
  have htrace : WordTrace (prefixWord ++ tailWord_4791950) baseStart_4791950 baseEnd_4791950 := by
    simpa [prefixWord, tailWord_4791950, baseEnd_4791950] using wordTrace_append hprefix tailTrace_4791950
  have hstable : (prefixWord ++ tailWord_4791950).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4791950).length < 2 ^ (prefixWord ++ tailWord_4791950).sum := by decide
  have hdescent : baseEnd_4791950 < baseStart_4791950 := by decide
  rcases family_descends (prefixWord ++ tailWord_4791950) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4791954 : List Nat := [3, 2, 3, 1, 3, 1, 2, 2, 1, 1, 4]
def baseStart_4791954 : Nat := 118140960795 + 4791954 * 2 ^ 59
def prefixEnd_4791954 : Nat := 4983230072969 + 3 ^ 40 * 4791954 * 2
def baseEnd_4791954 : Nat := 2460575676235249691637211

theorem tailTrace_4791954 : CollatzResearch.WordTrace tailWord_4791954 prefixEnd_4791954 2460575676235249691637211 := by
  unfold tailWord_4791954
  simp only [CollatzResearch.WordTrace]
  refine ⟨43694230220394133358027729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 116517947254384355621407277 43694230220394133358027729)
  ·
    refine ⟨32770672665295600018520797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43694230220394133358027729 32770672665295600018520797)
    ·
      refine ⟨12289002249485850006945299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32770672665295600018520797 12289002249485850006945299)
      ·
        refine ⟨18433503374228775010417949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12289002249485850006945299 18433503374228775010417949)
        ·
          refine ⟨6912563765335790628906731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18433503374228775010417949 6912563765335790628906731)
          ·
            refine ⟨10368845648003685943360097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6912563765335790628906731 10368845648003685943360097)
            ·
              refine ⟨7776634236002764457520073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10368845648003685943360097 7776634236002764457520073)
              ·
                refine ⟨5832475677002073343140055, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7776634236002764457520073 5832475677002073343140055)
                ·
                  refine ⟨8748713515503110014710083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5832475677002073343140055 8748713515503110014710083)
                  ·
                    refine ⟨13123070273254665022065125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8748713515503110014710083 13123070273254665022065125)
                    ·
                      refine ⟨2460575676235249691637211, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13123070273254665022065125 2460575676235249691637211)
                      ·
                        rfl

theorem cell23_4791954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 3, 1, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 3, 1, 2, 2, 1, 1, 4].length) (baseStart_4791954 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4791954 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4791954 prefixEnd_4791954 := by exact prefixLift 4791954
  have htrace : WordTrace (prefixWord ++ tailWord_4791954) baseStart_4791954 baseEnd_4791954 := by
    simpa [prefixWord, tailWord_4791954, baseEnd_4791954] using wordTrace_append hprefix tailTrace_4791954
  have hstable : (prefixWord ++ tailWord_4791954).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4791954).length < 2 ^ (prefixWord ++ tailWord_4791954).sum := by decide
  have hdescent : baseEnd_4791954 < baseStart_4791954 := by decide
  rcases family_descends (prefixWord ++ tailWord_4791954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4791960 : List Nat := [2, 1, 2, 4, 1, 2, 4, 7]
def baseStart_4791960 : Nat := 118140960795 + 4791960 * 2 ^ 59
def prefixEnd_4791960 : Nat := 4983230072969 + 3 ^ 40 * 4791960 * 2
def baseEnd_4791960 : Nat := 91132546559969506228229

theorem tailTrace_4791960 : CollatzResearch.WordTrace tailWord_4791960 prefixEnd_4791960 91132546559969506228229 := by
  unfold tailWord_4791960
  simp only [CollatzResearch.WordTrace]
  refine ⟨87388569859777398228414667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116518093146369864304552889 87388569859777398228414667)
  ·
    refine ⟨131082854789666097342622001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87388569859777398228414667 131082854789666097342622001)
    ·
      refine ⟨98312141092249573006966501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 131082854789666097342622001 98312141092249573006966501)
      ·
        refine ⟨18433526454796794938806219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 98312141092249573006966501 18433526454796794938806219)
        ·
          refine ⟨27650289682195192408209329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18433526454796794938806219 27650289682195192408209329)
          ·
            refine ⟨20737717261646394306156997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27650289682195192408209329 20737717261646394306156997)
            ·
              refine ⟨3888321986558698932404437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 20737717261646394306156997 3888321986558698932404437)
              ·
                refine ⟨91132546559969506228229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3888321986558698932404437 91132546559969506228229)
                ·
                  rfl

theorem cell23_4791960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 4, 7].length) (baseStart_4791960 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4791960 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4791960 prefixEnd_4791960 := by exact prefixLift 4791960
  have htrace : WordTrace (prefixWord ++ tailWord_4791960) baseStart_4791960 baseEnd_4791960 := by
    simpa [prefixWord, tailWord_4791960, baseEnd_4791960] using wordTrace_append hprefix tailTrace_4791960
  have hstable : (prefixWord ++ tailWord_4791960).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4791960).length < 2 ^ (prefixWord ++ tailWord_4791960).sum := by decide
  have hdescent : baseEnd_4791960 < baseStart_4791960 := by decide
  rcases family_descends (prefixWord ++ tailWord_4791960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4791983 : List Nat := [1, 1, 2, 1, 2, 4, 1, 2, 2, 2, 5]
def baseStart_4791983 : Nat := 118140960795 + 4791983 * 2 ^ 59
def prefixEnd_4791983 : Nat := 4983230072969 + 3 ^ 40 * 4791983 * 2
def baseEnd_4791983 : Nat := 2460590567174230078174577

theorem tailTrace_4791983 : CollatzResearch.WordTrace tailWord_4791983 prefixEnd_4791983 2460590567174230078174577 := by
  unfold tailWord_4791983
  simp only [CollatzResearch.WordTrace]
  refine ⟨174777978598471471384916603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116518652398980980923277735 174777978598471471384916603)
  ·
    refine ⟨262166967897707207077374905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 174777978598471471384916603 262166967897707207077374905)
    ·
      refine ⟨196625225923280405308031179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 262166967897707207077374905 196625225923280405308031179)
      ·
        refine ⟨294937838884920607962046769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 196625225923280405308031179 294937838884920607962046769)
        ·
          refine ⟨221203379163690455971535077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 294937838884920607962046769 221203379163690455971535077)
          ·
            refine ⟨41475633593191960494662827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 221203379163690455971535077 41475633593191960494662827)
            ·
              refine ⟨62213450389787940741994241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41475633593191960494662827 62213450389787940741994241)
              ·
                refine ⟨46660087792340955556495681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 62213450389787940741994241 46660087792340955556495681)
                ·
                  refine ⟨34995065844255716667371761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 46660087792340955556495681 34995065844255716667371761)
                  ·
                    refine ⟨26246299383191787500528821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 34995065844255716667371761 26246299383191787500528821)
                    ·
                      refine ⟨2460590567174230078174577, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26246299383191787500528821 2460590567174230078174577)
                      ·
                        rfl

theorem cell23_4791983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 1, 2, 2, 2, 5].length) (baseStart_4791983 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4791983 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4791983 prefixEnd_4791983 := by exact prefixLift 4791983
  have htrace : WordTrace (prefixWord ++ tailWord_4791983) baseStart_4791983 baseEnd_4791983 := by
    simpa [prefixWord, tailWord_4791983, baseEnd_4791983] using wordTrace_append hprefix tailTrace_4791983
  have hstable : (prefixWord ++ tailWord_4791983).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4791983).length < 2 ^ (prefixWord ++ tailWord_4791983).sum := by decide
  have hdescent : baseEnd_4791983 < baseStart_4791983 := by decide
  rcases family_descends (prefixWord ++ tailWord_4791983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4791987 : List Nat := [1, 1, 1, 2, 3, 3, 2, 4, 2, 1, 3]
def baseStart_4791987 : Nat := 118140960795 + 4791987 * 2 ^ 59
def prefixEnd_4791987 : Nat := 4983230072969 + 3 ^ 40 * 4791987 * 2
def baseEnd_4791987 : Nat := 2460592621096848062524559

theorem tailTrace_4791987 : CollatzResearch.WordTrace tailWord_4791987 prefixEnd_4791987 2460592621096848062524559 := by
  unfold tailWord_4791987
  simp only [CollatzResearch.WordTrace]
  refine ⟨174778124490456980068062215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116518749660304653378708143 174778124490456980068062215)
  ·
    refine ⟨262167186735685470102093323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 174778124490456980068062215 262167186735685470102093323)
    ·
      refine ⟨393250780103528205153139985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 262167186735685470102093323 393250780103528205153139985)
      ·
        refine ⟨294938085077646153864854989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 393250780103528205153139985 294938085077646153864854989)
        ·
          refine ⟨110601781904117307699320621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 294938085077646153864854989 110601781904117307699320621)
          ·
            refine ⟨41475668214043990387245233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 110601781904117307699320621 41475668214043990387245233)
            ·
              refine ⟨31106751160532992790433925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 41475668214043990387245233 31106751160532992790433925)
              ·
                refine ⟨5832515842599936148206361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 31106751160532992790433925 5832515842599936148206361)
                ·
                  refine ⟨4374386881949952111154771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5832515842599936148206361 4374386881949952111154771)
                  ·
                    refine ⟨6561580322924928166732157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4374386881949952111154771 6561580322924928166732157)
                    ·
                      refine ⟨2460592621096848062524559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6561580322924928166732157 2460592621096848062524559)
                      ·
                        rfl

theorem cell23_4791987_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 2, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 2, 4, 2, 1, 3].length) (baseStart_4791987 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4791987 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4791987 prefixEnd_4791987 := by exact prefixLift 4791987
  have htrace : WordTrace (prefixWord ++ tailWord_4791987) baseStart_4791987 baseEnd_4791987 := by
    simpa [prefixWord, tailWord_4791987, baseEnd_4791987] using wordTrace_append hprefix tailTrace_4791987
  have hstable : (prefixWord ++ tailWord_4791987).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4791987).length < 2 ^ (prefixWord ++ tailWord_4791987).sum := by decide
  have hdescent : baseEnd_4791987 < baseStart_4791987 := by decide
  rcases family_descends (prefixWord ++ tailWord_4791987) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4791997 : List Nat := [1, 4, 1, 2, 1, 2, 2, 2, 3, 3, 2]
def baseStart_4791997 : Nat := 118140960795 + 4791997 * 2 ^ 59
def prefixEnd_4791997 : Nat := 4983230072969 + 3 ^ 40 * 4791997 * 2
def baseEnd_4791997 : Nat := 2460597755903393023399513

theorem tailTrace_4791997 : CollatzResearch.WordTrace tailWord_4791997 prefixEnd_4791997 2460597755903393023399513 := by
  unfold tailWord_4791997
  simp only [CollatzResearch.WordTrace]
  refine ⟨174778489220420751775926245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116518992813613834517284163 174778489220420751775926245)
  ·
    refine ⟨32770966728828890957986171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 174778489220420751775926245 32770966728828890957986171)
    ·
      refine ⟨49156450093243336436979257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32770966728828890957986171 49156450093243336436979257)
      ·
        refine ⟨36867337569932502327734443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49156450093243336436979257 36867337569932502327734443)
        ·
          refine ⟨55301006354898753491601665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36867337569932502327734443 55301006354898753491601665)
          ·
            refine ⟨41475754766174065118701249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 55301006354898753491601665 41475754766174065118701249)
            ·
              refine ⟨31106816074630548839025937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 41475754766174065118701249 31106816074630548839025937)
              ·
                refine ⟨23330112055972911629269453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31106816074630548839025937 23330112055972911629269453)
                ·
                  refine ⟨8748792020989841860976045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23330112055972911629269453 8748792020989841860976045)
                  ·
                    refine ⟨3280797007871190697866017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8748792020989841860976045 3280797007871190697866017)
                    ·
                      refine ⟨2460597755903393023399513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3280797007871190697866017 2460597755903393023399513)
                      ·
                        rfl

theorem cell23_4791997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 2, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 2, 2, 3, 3, 2].length) (baseStart_4791997 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4791997 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4791997 prefixEnd_4791997 := by exact prefixLift 4791997
  have htrace : WordTrace (prefixWord ++ tailWord_4791997) baseStart_4791997 baseEnd_4791997 := by
    simpa [prefixWord, tailWord_4791997, baseEnd_4791997] using wordTrace_append hprefix tailTrace_4791997
  have hstable : (prefixWord ++ tailWord_4791997).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4791997).length < 2 ^ (prefixWord ++ tailWord_4791997).sum := by decide
  have hdescent : baseEnd_4791997 < baseStart_4791997 := by decide
  rcases family_descends (prefixWord ++ tailWord_4791997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4792004 : List Nat := [2, 3, 3, 1, 1, 1, 3, 3, 2, 1, 3]
def baseStart_4792004 : Nat := 118140960795 + 4792004 * 2 ^ 59
def prefixEnd_4792004 : Nat := 4983230072969 + 3 ^ 40 * 4792004 * 2
def baseEnd_4792004 : Nat := 2460601350267974496011981

theorem tailTrace_4792004 : CollatzResearch.WordTrace tailWord_4792004 prefixEnd_4792004 2460601350267974496011981 := by
  unfold tailWord_4792004
  simp only [CollatzResearch.WordTrace]
  refine ⟨87389372265697695985715533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116519163020930261314287377 87389372265697695985715533)
  ·
    refine ⟨32771014599636635994643325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 87389372265697695985715533 32771014599636635994643325)
    ·
      refine ⟨12289130474863738497991247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32771014599636635994643325 12289130474863738497991247)
      ·
        refine ⟨18433695712295607746986871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12289130474863738497991247 18433695712295607746986871)
        ·
          refine ⟨27650543568443411620480307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18433695712295607746986871 27650543568443411620480307)
          ·
            refine ⟨41475815352665117430720461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27650543568443411620480307 41475815352665117430720461)
            ·
              refine ⟨15553430757249419036520173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 41475815352665117430720461 15553430757249419036520173)
              ·
                refine ⟨5832536533968532138695065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15553430757249419036520173 5832536533968532138695065)
                ·
                  refine ⟨4374402400476399104021299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5832536533968532138695065 4374402400476399104021299)
                  ·
                    refine ⟨6561603600714598656031949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4374402400476399104021299 6561603600714598656031949)
                    ·
                      refine ⟨2460601350267974496011981, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6561603600714598656031949 2460601350267974496011981)
                      ·
                        rfl

theorem cell23_4792004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 3, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 3, 3, 2, 1, 3].length) (baseStart_4792004 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4792004 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4792004 prefixEnd_4792004 := by exact prefixLift 4792004
  have htrace : WordTrace (prefixWord ++ tailWord_4792004) baseStart_4792004 baseEnd_4792004 := by
    simpa [prefixWord, tailWord_4792004, baseEnd_4792004] using wordTrace_append hprefix tailTrace_4792004
  have hstable : (prefixWord ++ tailWord_4792004).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4792004).length < 2 ^ (prefixWord ++ tailWord_4792004).sum := by decide
  have hdescent : baseEnd_4792004 < baseStart_4792004 := by decide
  rcases family_descends (prefixWord ++ tailWord_4792004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4792043 : List Nat := [1, 1, 1, 1, 2, 4, 2, 1, 1, 2, 7]
def baseStart_4792043 : Nat := 118140960795 + 4792043 * 2 ^ 59
def prefixEnd_4792043 : Nat := 4983230072969 + 3 ^ 40 * 4792043 * 2
def baseEnd_4792043 : Nat := 2460621376013499843424301

theorem tailTrace_4792043 : CollatzResearch.WordTrace tailWord_4792043 prefixEnd_4792043 2460621376013499843424301 := by
  unfold tailWord_4792043
  simp only [CollatzResearch.WordTrace]
  refine ⟨174780166978254101632100783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116520111318836067754733855 174780166978254101632100783)
  ·
    refine ⟨262170250467381152448151175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 174780166978254101632100783 262170250467381152448151175)
    ·
      refine ⟨393255375701071728672226763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 262170250467381152448151175 393255375701071728672226763)
      ·
        refine ⟨589883063551607593008340145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 393255375701071728672226763 589883063551607593008340145)
        ·
          refine ⟨442412297663705694756255109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 589883063551607593008340145 442412297663705694756255109)
          ·
            refine ⟨82952305811944817766797833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 442412297663705694756255109 82952305811944817766797833)
            ·
              refine ⟨62214229358958613325098375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 82952305811944817766797833 62214229358958613325098375)
              ·
                refine ⟨93321344038437919987647563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 62214229358958613325098375 93321344038437919987647563)
                ·
                  refine ⟨139982016057656879981471345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 93321344038437919987647563 139982016057656879981471345)
                  ·
                    refine ⟨104986512043242659986103509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 139982016057656879981471345 104986512043242659986103509)
                    ·
                      refine ⟨2460621376013499843424301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 104986512043242659986103509 2460621376013499843424301)
                      ·
                        rfl

theorem cell23_4792043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 2, 1, 1, 2, 7].length) (baseStart_4792043 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4792043 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4792043 prefixEnd_4792043 := by exact prefixLift 4792043
  have htrace : WordTrace (prefixWord ++ tailWord_4792043) baseStart_4792043 baseEnd_4792043 := by
    simpa [prefixWord, tailWord_4792043, baseEnd_4792043] using wordTrace_append hprefix tailTrace_4792043
  have hstable : (prefixWord ++ tailWord_4792043).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4792043).length < 2 ^ (prefixWord ++ tailWord_4792043).sum := by decide
  have hdescent : baseEnd_4792043 < baseStart_4792043 := by decide
  rcases family_descends (prefixWord ++ tailWord_4792043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4792044 : List Nat := [2, 2, 1, 1, 2, 2, 3, 4, 2, 2, 2]
def baseStart_4792044 : Nat := 118140960795 + 4792044 * 2 ^ 59
def prefixEnd_4792044 : Nat := 4983230072969 + 3 ^ 40 * 4792044 * 2
def baseEnd_4792044 : Nat := 2460621889494154339511797

theorem tailTrace_4792044 : CollatzResearch.WordTrace tailWord_4792044 prefixEnd_4792044 2460621889494154339511797 := by
  unfold tailWord_4792044
  simp only [CollatzResearch.WordTrace]
  refine ⟨87390101725625239401443593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116520135634166985868591457 87390101725625239401443593)
  ·
    refine ⟨65542576294218929551082695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 87390101725625239401443593 65542576294218929551082695)
    ·
      refine ⟨98313864441328394326624043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65542576294218929551082695 98313864441328394326624043)
      ·
        refine ⟨147470796661992591489936065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 98313864441328394326624043 147470796661992591489936065)
        ·
          refine ⟨110603097496494443617452049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 147470796661992591489936065 110603097496494443617452049)
          ·
            refine ⟨82952323122370832713089037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 110603097496494443617452049 82952323122370832713089037)
            ·
              refine ⟨31107121170889062267408389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 82952323122370832713089037 31107121170889062267408389)
              ·
                refine ⟨5832585219541699175139073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 31107121170889062267408389 5832585219541699175139073)
                ·
                  refine ⟨4374438914656274381354305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5832585219541699175139073 4374438914656274381354305)
                  ·
                    refine ⟨3280829185992205786015729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4374438914656274381354305 3280829185992205786015729)
                    ·
                      refine ⟨2460621889494154339511797, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3280829185992205786015729 2460621889494154339511797)
                      ·
                        rfl

theorem cell23_4792044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 2, 2, 2].length) (baseStart_4792044 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4792044 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4792044 prefixEnd_4792044 := by exact prefixLift 4792044
  have htrace : WordTrace (prefixWord ++ tailWord_4792044) baseStart_4792044 baseEnd_4792044 := by
    simpa [prefixWord, tailWord_4792044, baseEnd_4792044] using wordTrace_append hprefix tailTrace_4792044
  have hstable : (prefixWord ++ tailWord_4792044).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4792044).length < 2 ^ (prefixWord ++ tailWord_4792044).sum := by decide
  have hdescent : baseEnd_4792044 < baseStart_4792044 := by decide
  rcases family_descends (prefixWord ++ tailWord_4792044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4792050 : List Nat := [3, 2, 1, 3, 1, 1, 2, 3, 7]
def baseStart_4792050 : Nat := 118140960795 + 4792050 * 2 ^ 59
def prefixEnd_4792050 : Nat := 4983230072969 + 3 ^ 40 * 4792050 * 2
def baseEnd_4792050 : Nat := 273402774486453479559641

theorem tailTrace_4792050 : CollatzResearch.WordTrace tailWord_4792050 prefixEnd_4792050 273402774486453479559641 := by
  unfold tailWord_4792050
  simp only [CollatzResearch.WordTrace]
  refine ⟨43695105572307185456901401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 116520281526152494551737069 43695105572307185456901401)
  ·
    refine ⟨32771329179230389092676051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43695105572307185456901401 32771329179230389092676051)
    ·
      refine ⟨49156993768845583639014077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32771329179230389092676051 49156993768845583639014077)
      ·
        refine ⟨18433872663317093864630279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 49156993768845583639014077 18433872663317093864630279)
        ·
          refine ⟨27650808994975640796945419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18433872663317093864630279 27650808994975640796945419)
          ·
            refine ⟨41476213492463461195418129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27650808994975640796945419 41476213492463461195418129)
            ·
              refine ⟨31107160119347595896563597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 41476213492463461195418129 31107160119347595896563597)
              ·
                refine ⟨11665185044755348461211349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 31107160119347595896563597 11665185044755348461211349)
                ·
                  refine ⟨273402774486453479559641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11665185044755348461211349 273402774486453479559641)
                  ·
                    rfl

theorem cell23_4792050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 2, 3, 7].length) (baseStart_4792050 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4792050 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4792050 prefixEnd_4792050 := by exact prefixLift 4792050
  have htrace : WordTrace (prefixWord ++ tailWord_4792050) baseStart_4792050 baseEnd_4792050 := by
    simpa [prefixWord, tailWord_4792050, baseEnd_4792050] using wordTrace_append hprefix tailTrace_4792050
  have hstable : (prefixWord ++ tailWord_4792050).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4792050).length < 2 ^ (prefixWord ++ tailWord_4792050).sum := by decide
  have hdescent : baseEnd_4792050 < baseStart_4792050 := by decide
  rcases family_descends (prefixWord ++ tailWord_4792050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4792137 : List Nat := [1, 2, 1, 1, 2, 4, 2, 3, 2, 2, 3]
def baseStart_4792137 : Nat := 118140960795 + 4792137 * 2 ^ 59
def prefixEnd_4792137 : Nat := 4983230072969 + 3 ^ 40 * 4792137 * 2
def baseEnd_4792137 : Nat := 2460669643195022475648869

theorem tailTrace_4792137 : CollatzResearch.WordTrace tailWord_4792137 prefixEnd_4792137 2460669643195022475648869 := by
  unfold tailWord_4792137
  simp only [CollatzResearch.WordTrace]
  refine ⟨174783595439913555686022665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116522396959942370457348443 174783595439913555686022665)
  ·
    refine ⟨131087696579935166764516999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 174783595439913555686022665 131087696579935166764516999)
    ·
      refine ⟨196631544869902750146775499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 131087696579935166764516999 196631544869902750146775499)
      ·
        refine ⟨294947317304854125220163249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 196631544869902750146775499 294947317304854125220163249)
        ·
          refine ⟨221210487978640593915122437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 294947317304854125220163249 221210487978640593915122437)
          ·
            refine ⟨41476966495995111359085457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 221210487978640593915122437 41476966495995111359085457)
            ·
              refine ⟨31107724871996333519314093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 41476966495995111359085457 31107724871996333519314093)
              ·
                refine ⟨11665396826998625069742785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 31107724871996333519314093 11665396826998625069742785)
                ·
                  refine ⟨8749047620248968802307089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11665396826998625069742785 8749047620248968802307089)
                  ·
                    refine ⟨6561785715186726601730317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8749047620248968802307089 6561785715186726601730317)
                    ·
                      refine ⟨2460669643195022475648869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6561785715186726601730317 2460669643195022475648869)
                      ·
                        rfl

theorem cell23_4792137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 2, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 2, 3, 2, 2, 3].length) (baseStart_4792137 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4792137 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4792137 prefixEnd_4792137 := by exact prefixLift 4792137
  have htrace : WordTrace (prefixWord ++ tailWord_4792137) baseStart_4792137 baseEnd_4792137 := by
    simpa [prefixWord, tailWord_4792137, baseEnd_4792137] using wordTrace_append hprefix tailTrace_4792137
  have hstable : (prefixWord ++ tailWord_4792137).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4792137).length < 2 ^ (prefixWord ++ tailWord_4792137).sum := by decide
  have hdescent : baseEnd_4792137 < baseStart_4792137 := by decide
  rcases family_descends (prefixWord ++ tailWord_4792137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4792161 : List Nat := [1, 2, 3, 1, 1, 1, 7, 2, 1, 4]
def baseStart_4792161 : Nat := 118140960795 + 4792161 * 2 ^ 59
def prefixEnd_4792161 : Nat := 4983230072969 + 3 ^ 40 * 4792161 * 2
def baseEnd_4792161 : Nat := 820227322243576793916253

theorem tailTrace_4792161 : CollatzResearch.WordTrace tailWord_4792161 prefixEnd_4792161 820227322243576793916253 := by
  unfold tailWord_4792161
  simp only [CollatzResearch.WordTrace]
  refine ⟨174784470791826607784896337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116522980527884405189930891 174784470791826607784896337)
  ·
    refine ⟨131088353093869955838672253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 174784470791826607784896337 131088353093869955838672253)
    ·
      refine ⟨49158132410201233439502095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 131088353093869955838672253 49158132410201233439502095)
      ·
        refine ⟨73737198615301850159253143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49158132410201233439502095 73737198615301850159253143)
        ·
          refine ⟨110605797922952775238879715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 73737198615301850159253143 110605797922952775238879715)
          ·
            refine ⟨165908696884429162858319573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 110605797922952775238879715 165908696884429162858319573)
            ·
              refine ⟨3888485083228808504491865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 165908696884429162858319573 3888485083228808504491865)
              ·
                refine ⟨2916363812421606378368899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3888485083228808504491865 2916363812421606378368899)
                ·
                  refine ⟨4374545718632409567553349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2916363812421606378368899 4374545718632409567553349)
                  ·
                    refine ⟨820227322243576793916253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4374545718632409567553349 820227322243576793916253)
                    ·
                      rfl

theorem cell23_4792161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 7, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 7, 2, 1, 4].length) (baseStart_4792161 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4792161 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4792161 prefixEnd_4792161 := by exact prefixLift 4792161
  have htrace : WordTrace (prefixWord ++ tailWord_4792161) baseStart_4792161 baseEnd_4792161 := by
    simpa [prefixWord, tailWord_4792161, baseEnd_4792161] using wordTrace_append hprefix tailTrace_4792161
  have hstable : (prefixWord ++ tailWord_4792161).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4792161).length < 2 ^ (prefixWord ++ tailWord_4792161).sum := by decide
  have hdescent : baseEnd_4792161 < baseStart_4792161 := by decide
  rcases family_descends (prefixWord ++ tailWord_4792161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4792174 : List Nat := [4, 1, 2, 3, 1, 2, 1, 3, 6]
def baseStart_4792174 : Nat := 118140960795 + 4792174 * 2 ^ 59
def prefixEnd_4792174 : Nat := 4983230072969 + 3 ^ 40 * 4792174 * 2
def baseEnd_4792174 : Nat := 273409849108804314542911

theorem tailTrace_4792174 : CollatzResearch.WordTrace tailWord_4792174 prefixEnd_4792174 273409849108804314542911 := by
  unfold tailWord_4792174
  simp only [CollatzResearch.WordTrace]
  refine ⟨21848118117597438875639947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 116523296627186340670079717 21848118117597438875639947)
  ·
    refine ⟨32772177176396158313459921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21848118117597438875639947 32772177176396158313459921)
    ·
      refine ⟨24579132882297118735094941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32772177176396158313459921 24579132882297118735094941)
      ·
        refine ⟨9217174830861419525660603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24579132882297118735094941 9217174830861419525660603)
        ·
          refine ⟨13825762246292129288490905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9217174830861419525660603 13825762246292129288490905)
          ·
            refine ⟨10369321684719096966368179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13825762246292129288490905 10369321684719096966368179)
            ·
              refine ⟨15553982527078645449552269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10369321684719096966368179 15553982527078645449552269)
              ·
                refine ⟨5832743447654492043582101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15553982527078645449552269 5832743447654492043582101)
                ·
                  refine ⟨273409849108804314542911, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5832743447654492043582101 273409849108804314542911)
                  ·
                    rfl

theorem cell23_4792174_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 2, 1, 3, 6].length) (baseStart_4792174 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4792174 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4792174 prefixEnd_4792174 := by exact prefixLift 4792174
  have htrace : WordTrace (prefixWord ++ tailWord_4792174) baseStart_4792174 baseEnd_4792174 := by
    simpa [prefixWord, tailWord_4792174, baseEnd_4792174] using wordTrace_append hprefix tailTrace_4792174
  have hstable : (prefixWord ++ tailWord_4792174).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4792174).length < 2 ^ (prefixWord ++ tailWord_4792174).sum := by decide
  have hdescent : baseEnd_4792174 < baseStart_4792174 := by decide
  rcases family_descends (prefixWord ++ tailWord_4792174) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4792201 : List Nat := [1, 2, 1, 1, 5, 1, 2, 5, 1, 1, 3]
def baseStart_4792201 : Nat := 118140960795 + 4792201 * 2 ^ 59
def prefixEnd_4792201 : Nat := 4983230072969 + 3 ^ 40 * 4792201 * 2
def baseEnd_4792201 : Nat := 2460702505956910225248575

theorem tailTrace_4792201 : CollatzResearch.WordTrace tailWord_4792201 prefixEnd_4792201 2460702505956910225248575 := by
  unfold tailWord_4792201
  simp only [CollatzResearch.WordTrace]
  refine ⟨174785929711681694616352457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116523953141121129744234971 174785929711681694616352457)
  ·
    refine ⟨131089447283761270962264343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 174785929711681694616352457 131089447283761270962264343)
    ·
      refine ⟨196634170925641906443396515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 131089447283761270962264343 196634170925641906443396515)
      ·
        refine ⟨294951256388462859665094773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 196634170925641906443396515 294951256388462859665094773)
        ·
          refine ⟨27651680286418393093602635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 294951256388462859665094773 27651680286418393093602635)
          ·
            refine ⟨41477520429627589640403953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27651680286418393093602635 41477520429627589640403953)
            ·
              refine ⟨31108140322220692230302965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 41477520429627589640403953 31108140322220692230302965)
              ·
                refine ⟨2916388155208189896590903, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 31108140322220692230302965 2916388155208189896590903)
                ·
                  refine ⟨4374582232812284844886355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2916388155208189896590903 4374582232812284844886355)
                  ·
                    refine ⟨6561873349218427267329533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4374582232812284844886355 6561873349218427267329533)
                    ·
                      refine ⟨2460702505956910225248575, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6561873349218427267329533 2460702505956910225248575)
                      ·
                        rfl

theorem cell23_4792201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 2, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 2, 5, 1, 1, 3].length) (baseStart_4792201 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4792201 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4792201 prefixEnd_4792201 := by exact prefixLift 4792201
  have htrace : WordTrace (prefixWord ++ tailWord_4792201) baseStart_4792201 baseEnd_4792201 := by
    simpa [prefixWord, tailWord_4792201, baseEnd_4792201] using wordTrace_append hprefix tailTrace_4792201
  have hstable : (prefixWord ++ tailWord_4792201).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4792201).length < 2 ^ (prefixWord ++ tailWord_4792201).sum := by decide
  have hdescent : baseEnd_4792201 < baseStart_4792201 := by decide
  rcases family_descends (prefixWord ++ tailWord_4792201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4792207 : List Nat := [1, 1, 2, 1, 1, 1, 1, 1, 6, 6, 2]
def baseStart_4792207 : Nat := 118140960795 + 4792207 * 2 ^ 59
def prefixEnd_4792207 : Nat := 4983230072969 + 3 ^ 40 * 4792207 * 2
def baseEnd_4792207 : Nat := 2460705586840837201773547

theorem tailTrace_4792207 : CollatzResearch.WordTrace tailWord_4792207 prefixEnd_4792207 2460705586840837201773547 := by
  unfold tailWord_4792207
  simp only [CollatzResearch.WordTrace]
  refine ⟨174786148549659957641070875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116524099033106638427380583 174786148549659957641070875)
  ·
    refine ⟨262179222824489936461606313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 174786148549659957641070875 262179222824489936461606313)
    ·
      refine ⟨196634417118367452346204735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 262179222824489936461606313 196634417118367452346204735)
      ·
        refine ⟨294951625677551178519307103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 196634417118367452346204735 294951625677551178519307103)
        ·
          refine ⟨442427438516326767778960655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 294951625677551178519307103 442427438516326767778960655)
          ·
            refine ⟨663641157774490151668440983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 442427438516326767778960655 663641157774490151668440983)
            ·
              refine ⟨995461736661735227502661475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 663641157774490151668440983 995461736661735227502661475)
              ·
                refine ⟨1493192604992602841253992213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 995461736661735227502661475 1493192604992602841253992213)
                ·
                  refine ⟨69993403359028258183780885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1493192604992602841253992213 69993403359028258183780885)
                  ·
                    refine ⟨3280940782454449602364729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 69993403359028258183780885 3280940782454449602364729)
                    ·
                      refine ⟨2460705586840837201773547, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3280940782454449602364729 2460705586840837201773547)
                      ·
                        rfl

theorem cell23_4792207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 6, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 6, 6, 2].length) (baseStart_4792207 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4792207 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4792207 prefixEnd_4792207 := by exact prefixLift 4792207
  have htrace : WordTrace (prefixWord ++ tailWord_4792207) baseStart_4792207 baseEnd_4792207 := by
    simpa [prefixWord, tailWord_4792207, baseEnd_4792207] using wordTrace_append hprefix tailTrace_4792207
  have hstable : (prefixWord ++ tailWord_4792207).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4792207).length < 2 ^ (prefixWord ++ tailWord_4792207).sum := by decide
  have hdescent : baseEnd_4792207 < baseStart_4792207 := by decide
  rcases family_descends (prefixWord ++ tailWord_4792207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4792217 : List Nat := [1, 2, 1, 2, 1, 3, 2, 3, 4, 4]
def baseStart_4792217 : Nat := 118140960795 + 4792217 * 2 ^ 59
def prefixEnd_4792217 : Nat := 4983230072969 + 3 ^ 40 * 4792217 * 2
def baseEnd_4792217 : Nat := 820236907215794054216167

theorem tailTrace_4792217 : CollatzResearch.WordTrace tailWord_4792217 prefixEnd_4792217 820236907215794054216167 := by
  unfold tailWord_4792217
  simp only [CollatzResearch.WordTrace]
  refine ⟨174786513279623729348934905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116524342186415819565956603 174786513279623729348934905)
  ·
    refine ⟨131089884959717797011701179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 174786513279623729348934905 131089884959717797011701179)
    ·
      refine ⟨196634827439576695517551769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 131089884959717797011701179 196634827439576695517551769)
      ·
        refine ⟨147476120579682521638163827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 196634827439576695517551769 147476120579682521638163827)
        ·
          refine ⟨221214180869523782457245741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 147476120579682521638163827 221214180869523782457245741)
          ·
            refine ⟨82955317826071418421467153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 221214180869523782457245741 82955317826071418421467153)
            ·
              refine ⟨62216488369553563816100365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 82955317826071418421467153 62216488369553563816100365)
              ·
                refine ⟨23331183138582586431037637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 62216488369553563816100365 23331183138582586431037637)
                ·
                  refine ⟨4374596838484234955819557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 23331183138582586431037637 4374596838484234955819557)
                  ·
                    refine ⟨820236907215794054216167, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4374596838484234955819557 820236907215794054216167)
                    ·
                      rfl

theorem cell23_4792217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 2, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 2, 3, 4, 4].length) (baseStart_4792217 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4792217 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4792217 prefixEnd_4792217 := by exact prefixLift 4792217
  have htrace : WordTrace (prefixWord ++ tailWord_4792217) baseStart_4792217 baseEnd_4792217 := by
    simpa [prefixWord, tailWord_4792217, baseEnd_4792217] using wordTrace_append hprefix tailTrace_4792217
  have hstable : (prefixWord ++ tailWord_4792217).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4792217).length < 2 ^ (prefixWord ++ tailWord_4792217).sum := by decide
  have hdescent : baseEnd_4792217 < baseStart_4792217 := by decide
  rcases family_descends (prefixWord ++ tailWord_4792217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4792218 : List Nat := [3, 1, 1, 4, 2, 2, 1, 4, 1, 1, 3]
def baseStart_4792218 : Nat := 118140960795 + 4792218 * 2 ^ 59
def prefixEnd_4792218 : Nat := 4983230072969 + 3 ^ 40 * 4792218 * 2
def baseEnd_4792218 : Nat := 2460711235128036658735997

theorem tailTrace_4792218 : CollatzResearch.WordTrace tailWord_4792218 prefixEnd_4792218 2460711235128036658735997 := by
  unfold tailWord_4792218
  simp only [CollatzResearch.WordTrace]
  refine ⟨43696637438155026629930327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 116524366501746737679814205 43696637438155026629930327)
  ·
    refine ⟨65544956157232539944895491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43696637438155026629930327 65544956157232539944895491)
    ·
      refine ⟨98317434235848809917343237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65544956157232539944895491 98317434235848809917343237)
      ·
        refine ⟨18434518919221651859501857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 98317434235848809917343237 18434518919221651859501857)
        ·
          refine ⟨13825889189416238894626393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18434518919221651859501857 13825889189416238894626393)
          ·
            refine ⟨10369416892062179170969795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13825889189416238894626393 10369416892062179170969795)
            ·
              refine ⟨15554125338093268756454693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10369416892062179170969795 15554125338093268756454693)
              ·
                refine ⟨2916398500892487891835255, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15554125338093268756454693 2916398500892487891835255)
                ·
                  refine ⟨4374597751338731837752883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2916398500892487891835255 4374597751338731837752883)
                  ·
                    refine ⟨6561896627008097756629325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4374597751338731837752883 6561896627008097756629325)
                    ·
                      refine ⟨2460711235128036658735997, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6561896627008097756629325 2460711235128036658735997)
                      ·
                        rfl

theorem cell23_4792218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 2, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 2, 1, 4, 1, 1, 3].length) (baseStart_4792218 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4792218 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4792218 prefixEnd_4792218 := by exact prefixLift 4792218
  have htrace : WordTrace (prefixWord ++ tailWord_4792218) baseStart_4792218 baseEnd_4792218 := by
    simpa [prefixWord, tailWord_4792218, baseEnd_4792218] using wordTrace_append hprefix tailTrace_4792218
  have hstable : (prefixWord ++ tailWord_4792218).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4792218).length < 2 ^ (prefixWord ++ tailWord_4792218).sum := by decide
  have hdescent : baseEnd_4792218 < baseStart_4792218 := by decide
  rcases family_descends (prefixWord ++ tailWord_4792218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4792240 : List Nat := [2, 1, 1, 1, 2, 1, 1, 1, 4, 2, 7]
def baseStart_4792240 : Nat := 118140960795 + 4792240 * 2 ^ 59
def prefixEnd_4792240 : Nat := 4983230072969 + 3 ^ 40 * 4792240 * 2
def baseEnd_4792240 : Nat := 2460722531702435572660895

theorem tailTrace_4792240 : CollatzResearch.WordTrace tailWord_4792240 prefixEnd_4792240 2460722531702435572660895 := by
  unfold tailWord_4792240
  simp only [CollatzResearch.WordTrace]
  refine ⟨87393676079270202138511087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116524901439026936184681449 87393676079270202138511087)
  ·
    refine ⟨131090514118905303207766631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87393676079270202138511087 131090514118905303207766631)
    ·
      refine ⟨196635771178357954811649947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 131090514118905303207766631 196635771178357954811649947)
      ·
        refine ⟨294953656767536932217474921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 196635771178357954811649947 294953656767536932217474921)
        ·
          refine ⟨221215242575652699163106191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 294953656767536932217474921 221215242575652699163106191)
          ·
            refine ⟨331822863863479048744659287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 221215242575652699163106191 331822863863479048744659287)
            ·
              refine ⟨497734295795218573116988931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 331822863863479048744659287 497734295795218573116988931)
              ·
                refine ⟨746601443692827859675483397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 497734295795218573116988931 746601443692827859675483397)
                ·
                  refine ⟨139987770692405223689153137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 746601443692827859675483397 139987770692405223689153137)
                  ·
                    refine ⟨104990828019303917766864853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 139987770692405223689153137 104990828019303917766864853)
                    ·
                      refine ⟨2460722531702435572660895, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 104990828019303917766864853 2460722531702435572660895)
                      ·
                        rfl

theorem cell23_4792240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 1, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 1, 4, 2, 7].length) (baseStart_4792240 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4792240 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4792240 prefixEnd_4792240 := by exact prefixLift 4792240
  have htrace : WordTrace (prefixWord ++ tailWord_4792240) baseStart_4792240 baseEnd_4792240 := by
    simpa [prefixWord, tailWord_4792240, baseEnd_4792240] using wordTrace_append hprefix tailTrace_4792240
  have hstable : (prefixWord ++ tailWord_4792240).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4792240).length < 2 ^ (prefixWord ++ tailWord_4792240).sum := by decide
  have hdescent : baseEnd_4792240 < baseStart_4792240 := by decide
  rcases family_descends (prefixWord ++ tailWord_4792240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4792241 : List Nat := [1, 2, 2, 4, 2, 1, 1, 1, 5, 2, 2]
def baseStart_4792241 : Nat := 118140960795 + 4792241 * 2 ^ 59
def prefixEnd_4792241 : Nat := 4983230072969 + 3 ^ 40 * 4792241 * 2
def baseEnd_4792241 : Nat := 2460723045183090068748391

theorem tailTrace_4792241 : CollatzResearch.WordTrace tailWord_4792241 prefixEnd_4792241 2460723045183090068748391 := by
  unfold tailWord_4792241
  simp only [CollatzResearch.WordTrace]
  refine ⟨174787388631536781447808577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116524925754357854298539051 174787388631536781447808577)
  ·
    refine ⟨131090541473652586085856433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 174787388631536781447808577 131090541473652586085856433)
    ·
      refine ⟨98317906105239439564392325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 131090541473652586085856433 98317906105239439564392325)
      ·
        refine ⟨18434607394732394918323561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 98317906105239439564392325 18434607394732394918323561)
        ·
          refine ⟨13825955546049296188742671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18434607394732394918323561 13825955546049296188742671)
          ·
            refine ⟨20738933319073944283114007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13825955546049296188742671 20738933319073944283114007)
            ·
              refine ⟨31108399978610916424671011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20738933319073944283114007 31108399978610916424671011)
              ·
                refine ⟨46662599967916374637006517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31108399978610916424671011 46662599967916374637006517)
                ·
                  refine ⟨4374618746992160122219361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 46662599967916374637006517 4374618746992160122219361)
                  ·
                    refine ⟨3280964060244120091664521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4374618746992160122219361 3280964060244120091664521)
                    ·
                      refine ⟨2460723045183090068748391, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3280964060244120091664521 2460723045183090068748391)
                      ·
                        rfl

theorem cell23_4792241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 1, 1, 5, 2, 2].length) (baseStart_4792241 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4792241 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4792241 prefixEnd_4792241 := by exact prefixLift 4792241
  have htrace : WordTrace (prefixWord ++ tailWord_4792241) baseStart_4792241 baseEnd_4792241 := by
    simpa [prefixWord, tailWord_4792241, baseEnd_4792241] using wordTrace_append hprefix tailTrace_4792241
  have hstable : (prefixWord ++ tailWord_4792241).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4792241).length < 2 ^ (prefixWord ++ tailWord_4792241).sum := by decide
  have hdescent : baseEnd_4792241 < baseStart_4792241 := by decide
  rcases family_descends (prefixWord ++ tailWord_4792241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4792254 : List Nat := [4, 2, 1, 1, 1, 3, 2, 2, 1, 2, 4]
def baseStart_4792254 : Nat := 118140960795 + 4792254 * 2 ^ 59
def prefixEnd_4792254 : Nat := 4983230072969 + 3 ^ 40 * 4792254 * 2
def baseEnd_4792254 : Nat := 2460729720431598517885831

theorem tailTrace_4792254 : CollatzResearch.WordTrace tailWord_4792254 prefixEnd_4792254 2460729720431598517885831 := by
  unfold tailWord_4792254
  simp only [CollatzResearch.WordTrace]
  refine ⟨21848482847561210583503977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 116525241853659789778687877 21848482847561210583503977)
  ·
    refine ⟨16386362135670907937627983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21848482847561210583503977 16386362135670907937627983)
    ·
      refine ⟨24579543203506361906441975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16386362135670907937627983 24579543203506361906441975)
      ·
        refine ⟨36869314805259542859662963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24579543203506361906441975 36869314805259542859662963)
        ·
          refine ⟨55303972207889314289494445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36869314805259542859662963 55303972207889314289494445)
          ·
            refine ⟨20738989577958492858560417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 55303972207889314289494445 20738989577958492858560417)
            ·
              refine ⟨15554242183468869643920313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20738989577958492858560417 15554242183468869643920313)
              ·
                refine ⟨11665681637601652232940235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15554242183468869643920313 11665681637601652232940235)
                ·
                  refine ⟨17498522456402478349410353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11665681637601652232940235 17498522456402478349410353)
                  ·
                    refine ⟨13123891842301858762057765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17498522456402478349410353 13123891842301858762057765)
                    ·
                      refine ⟨2460729720431598517885831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13123891842301858762057765 2460729720431598517885831)
                      ·
                        rfl

theorem cell23_4792254_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 2, 2, 1, 2, 4].length) (baseStart_4792254 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4792254 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4792254 prefixEnd_4792254 := by exact prefixLift 4792254
  have htrace : WordTrace (prefixWord ++ tailWord_4792254) baseStart_4792254 baseEnd_4792254 := by
    simpa [prefixWord, tailWord_4792254, baseEnd_4792254] using wordTrace_append hprefix tailTrace_4792254
  have hstable : (prefixWord ++ tailWord_4792254).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4792254).length < 2 ^ (prefixWord ++ tailWord_4792254).sum := by decide
  have hdescent : baseEnd_4792254 < baseStart_4792254 := by decide
  rcases family_descends (prefixWord ++ tailWord_4792254) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4792291 : List Nat := [1, 1, 1, 6, 1, 4, 1, 1, 1, 3, 3]
def baseStart_4792291 : Nat := 118140960795 + 4792291 * 2 ^ 59
def prefixEnd_4792291 : Nat := 4983230072969 + 3 ^ 40 * 4792291 * 2
def baseEnd_4792291 : Nat := 2460748719215814873123161

theorem tailTrace_4792291 : CollatzResearch.WordTrace tailWord_4792291 prefixEnd_4792291 2460748719215814873123161 := by
  unfold tailWord_4792291
  simp only [CollatzResearch.WordTrace]
  refine ⟨174789212281355639987128727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116526141520903759991419151 174789212281355639987128727)
  ·
    refine ⟨262183818422033459980693091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 174789212281355639987128727 262183818422033459980693091)
    ·
      refine ⟨393275727633050189971039637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 262183818422033459980693091 393275727633050189971039637)
      ·
        refine ⟨18434799732799227654892483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 393275727633050189971039637 18434799732799227654892483)
        ·
          refine ⟨27652199599198841482338725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18434799732799227654892483 27652199599198841482338725)
          ·
            refine ⟨5184787424849782777938511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 27652199599198841482338725 5184787424849782777938511)
            ·
              refine ⟨7777181137274674166907767, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5184787424849782777938511 7777181137274674166907767)
              ·
                refine ⟨11665771705912011250361651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7777181137274674166907767 11665771705912011250361651)
                ·
                  refine ⟨17498657558868016875542477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11665771705912011250361651 17498657558868016875542477)
                  ·
                    refine ⟨6561996584575506328328429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17498657558868016875542477 6561996584575506328328429)
                    ·
                      refine ⟨2460748719215814873123161, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6561996584575506328328429 2460748719215814873123161)
                      ·
                        rfl

theorem cell23_4792291_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 4, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 4, 1, 1, 1, 3, 3].length) (baseStart_4792291 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4792291 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4792291 prefixEnd_4792291 := by exact prefixLift 4792291
  have htrace : WordTrace (prefixWord ++ tailWord_4792291) baseStart_4792291 baseEnd_4792291 := by
    simpa [prefixWord, tailWord_4792291, baseEnd_4792291] using wordTrace_append hprefix tailTrace_4792291
  have hstable : (prefixWord ++ tailWord_4792291).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4792291).length < 2 ^ (prefixWord ++ tailWord_4792291).sum := by decide
  have hdescent : baseEnd_4792291 < baseStart_4792291 := by decide
  rcases family_descends (prefixWord ++ tailWord_4792291) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4792317 : List Nat := [1, 4, 1, 1, 1, 2, 3, 1, 1, 3, 5]
def baseStart_4792317 : Nat := 118140960795 + 4792317 * 2 ^ 59
def prefixEnd_4792317 : Nat := 4983230072969 + 3 ^ 40 * 4792317 * 2
def baseEnd_4792317 : Nat := 2460762069712831771398041

theorem tailTrace_4792317 : CollatzResearch.WordTrace tailWord_4792317 prefixEnd_4792317 2460762069712831771398041 := by
  unfold tailWord_4792317
  simp only [CollatzResearch.WordTrace]
  refine ⟨174790160579261446427575205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116526773719507630951716803 174790160579261446427575205)
  ·
    refine ⟨32773155108611521205170351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 174790160579261446427575205 32773155108611521205170351)
    ·
      refine ⟨49159732662917281807755527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32773155108611521205170351 49159732662917281807755527)
      ·
        refine ⟨73739598994375922711633291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49159732662917281807755527 73739598994375922711633291)
        ·
          refine ⟨110609398491563884067449937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 73739598994375922711633291 110609398491563884067449937)
          ·
            refine ⟨82957048868672913050587453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 110609398491563884067449937 82957048868672913050587453)
            ·
              refine ⟨31108893325752342393970295, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 82957048868672913050587453 31108893325752342393970295)
              ·
                refine ⟨46663339988628513590955443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31108893325752342393970295 46663339988628513590955443)
                ·
                  refine ⟨69995009982942770386433165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 46663339988628513590955443 69995009982942770386433165)
                  ·
                    refine ⟨26248128743603538894912437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 69995009982942770386433165 26248128743603538894912437)
                    ·
                      refine ⟨2460762069712831771398041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26248128743603538894912437 2460762069712831771398041)
                      ·
                        rfl

theorem cell23_4792317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 3, 1, 1, 3, 5].length) (baseStart_4792317 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4792317 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4792317 prefixEnd_4792317 := by exact prefixLift 4792317
  have htrace : WordTrace (prefixWord ++ tailWord_4792317) baseStart_4792317 baseEnd_4792317 := by
    simpa [prefixWord, tailWord_4792317, baseEnd_4792317] using wordTrace_append hprefix tailTrace_4792317
  have hstable : (prefixWord ++ tailWord_4792317).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4792317).length < 2 ^ (prefixWord ++ tailWord_4792317).sum := by decide
  have hdescent : baseEnd_4792317 < baseStart_4792317 := by decide
  rcases family_descends (prefixWord ++ tailWord_4792317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4792326 : List Nat := [6, 2, 1, 2, 1, 2, 1, 1, 3, 2, 2]
def baseStart_4792326 : Nat := 118140960795 + 4792326 * 2 ^ 59
def prefixEnd_4792326 : Nat := 4983230072969 + 3 ^ 40 * 4792326 * 2
def baseEnd_4792326 : Nat := 2460766691038722236185501

theorem tailTrace_4792326 : CollatzResearch.WordTrace tailWord_4792326 prefixEnd_4792326 2460766691038722236185501 := by
  unfold tailWord_4792326
  simp only [CollatzResearch.WordTrace]
  refine ⟨5462202776132151280145401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 116526992557485893976435221 5462202776132151280145401)
  ·
    refine ⟨4096652082099113460109051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5462202776132151280145401 4096652082099113460109051)
    ·
      refine ⟨6144978123148670190163577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4096652082099113460109051 6144978123148670190163577)
      ·
        refine ⟨4608733592361502642622683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6144978123148670190163577 4608733592361502642622683)
        ·
          refine ⟨6913100388542253963934025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4608733592361502642622683 6913100388542253963934025)
          ·
            refine ⟨5184825291406690472950519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6913100388542253963934025 5184825291406690472950519)
            ·
              refine ⟨7777237937110035709425779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5184825291406690472950519 7777237937110035709425779)
              ·
                refine ⟨11665856905665053564138669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7777237937110035709425779 11665856905665053564138669)
                ·
                  refine ⟨4374696339624395086552001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11665856905665053564138669 4374696339624395086552001)
                  ·
                    refine ⟨3281022254718296314914001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4374696339624395086552001 3281022254718296314914001)
                    ·
                      refine ⟨2460766691038722236185501, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3281022254718296314914001 2460766691038722236185501)
                      ·
                        rfl

theorem cell23_4792326_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 1, 2, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 1, 2, 1, 1, 3, 2, 2].length) (baseStart_4792326 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4792326 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4792326 prefixEnd_4792326 := by exact prefixLift 4792326
  have htrace : WordTrace (prefixWord ++ tailWord_4792326) baseStart_4792326 baseEnd_4792326 := by
    simpa [prefixWord, tailWord_4792326, baseEnd_4792326] using wordTrace_append hprefix tailTrace_4792326
  have hstable : (prefixWord ++ tailWord_4792326).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4792326).length < 2 ^ (prefixWord ++ tailWord_4792326).sum := by decide
  have hdescent : baseEnd_4792326 < baseStart_4792326 := by decide
  rcases family_descends (prefixWord ++ tailWord_4792326) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4792331 : List Nat := [1, 1, 1, 1, 6, 1, 1, 3, 4, 2, 2]
def baseStart_4792331 : Nat := 118140960795 + 4792331 * 2 ^ 59
def prefixEnd_4792331 : Nat := 4983230072969 + 3 ^ 40 * 4792331 * 2
def baseEnd_4792331 : Nat := 2460769258441994716622977

theorem tailTrace_4792331 : CollatzResearch.WordTrace tailWord_4792331 prefixEnd_4792331 2460769258441994716622977 := by
  unfold tailWord_4792331
  simp only [CollatzResearch.WordTrace]
  refine ⟨174790671201210726818584847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116527114134140484545723231 174790671201210726818584847)
  ·
    refine ⟨262186006801816090227877271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 174790671201210726818584847 262186006801816090227877271)
    ·
      refine ⟨393279010202724135341815907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 262186006801816090227877271 393279010202724135341815907)
      ·
        refine ⟨589918515304086203012723861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 393279010202724135341815907 589918515304086203012723861)
        ·
          refine ⟨27652430404879040766221431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 589918515304086203012723861 27652430404879040766221431)
          ·
            refine ⟨41478645607318561149332147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27652430404879040766221431 41478645607318561149332147)
            ·
              refine ⟨62217968410977841723998221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41478645607318561149332147 62217968410977841723998221)
              ·
                refine ⟨23331738154116690646499333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 62217968410977841723998221 23331738154116690646499333)
                ·
                  refine ⟨4374700903896879496218625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 23331738154116690646499333 4374700903896879496218625)
                  ·
                    refine ⟨3281025677922659622163969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4374700903896879496218625 3281025677922659622163969)
                    ·
                      refine ⟨2460769258441994716622977, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3281025677922659622163969 2460769258441994716622977)
                      ·
                        rfl

theorem cell23_4792331_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 1, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 1, 3, 4, 2, 2].length) (baseStart_4792331 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4792331 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4792331 prefixEnd_4792331 := by exact prefixLift 4792331
  have htrace : WordTrace (prefixWord ++ tailWord_4792331) baseStart_4792331 baseEnd_4792331 := by
    simpa [prefixWord, tailWord_4792331, baseEnd_4792331] using wordTrace_append hprefix tailTrace_4792331
  have hstable : (prefixWord ++ tailWord_4792331).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4792331).length < 2 ^ (prefixWord ++ tailWord_4792331).sum := by decide
  have hdescent : baseEnd_4792331 < baseStart_4792331 := by decide
  rcases family_descends (prefixWord ++ tailWord_4792331) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4792334 : List Nat := [4, 1, 1, 2, 2, 1, 2, 1, 2, 4, 3]
def baseStart_4792334 : Nat := 118140960795 + 4792334 * 2 ^ 59
def prefixEnd_4792334 : Nat := 4983230072969 + 3 ^ 40 * 4792334 * 2
def baseEnd_4792334 : Nat := 2460770798883958204885463

theorem tailTrace_4792334 : CollatzResearch.WordTrace tailWord_4792334 prefixEnd_4792334 2460770798883958204885463 := by
  unfold tailWord_4792334
  simp only [CollatzResearch.WordTrace]
  refine ⟨21848847577524982291368007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 116527187080133238887296037 21848847577524982291368007)
  ·
    refine ⟨32773271366287473437052011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21848847577524982291368007 32773271366287473437052011)
    ·
      refine ⟨49159907049431210155578017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32773271366287473437052011 49159907049431210155578017)
      ·
        refine ⟨36869930287073407616683513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49159907049431210155578017 36869930287073407616683513)
        ·
          refine ⟨27652447715305055712512635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36869930287073407616683513 27652447715305055712512635)
          ·
            refine ⟨41478671572957583568768953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27652447715305055712512635 41478671572957583568768953)
            ·
              refine ⟨31109003679718187676576715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 41478671572957583568768953 31109003679718187676576715)
              ·
                refine ⟨46663505519577281514865073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31109003679718187676576715 46663505519577281514865073)
                ·
                  refine ⟨34997629139682961136148805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 46663505519577281514865073 34997629139682961136148805)
                  ·
                    refine ⟨6562055463690555213027901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 34997629139682961136148805 6562055463690555213027901)
                    ·
                      refine ⟨2460770798883958204885463, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6562055463690555213027901 2460770798883958204885463)
                      ·
                        rfl

theorem cell23_4792334_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 2, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 2, 1, 2, 4, 3].length) (baseStart_4792334 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4792334 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4792334 prefixEnd_4792334 := by exact prefixLift 4792334
  have htrace : WordTrace (prefixWord ++ tailWord_4792334) baseStart_4792334 baseEnd_4792334 := by
    simpa [prefixWord, tailWord_4792334, baseEnd_4792334] using wordTrace_append hprefix tailTrace_4792334
  have hstable : (prefixWord ++ tailWord_4792334).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4792334).length < 2 ^ (prefixWord ++ tailWord_4792334).sum := by decide
  have hdescent : baseEnd_4792334 < baseStart_4792334 := by decide
  rcases family_descends (prefixWord ++ tailWord_4792334) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4792382 : List Nat := [4, 2, 1, 3, 2, 1, 2, 2, 2, 2, 2]
def baseStart_4792382 : Nat := 118140960795 + 4792382 * 2 ^ 59
def prefixEnd_4792382 : Nat := 4983230072969 + 3 ^ 40 * 4792382 * 2
def baseEnd_4792382 : Nat := 2460795445955374017085243

theorem tailTrace_4792382 : CollatzResearch.WordTrace tailWord_4792382 prefixEnd_4792382 2460795445955374017085243 := by
  unfold tailWord_4792382
  simp only [CollatzResearch.WordTrace]
  refine ⟨21849066415503245316086425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 116528354216017308352460933 21849066415503245316086425)
  ·
    refine ⟨16386799811627433987064819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21849066415503245316086425 16386799811627433987064819)
    ·
      refine ⟨24580199717441150980597229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16386799811627433987064819 24580199717441150980597229)
      ·
        refine ⟨9217574894040431617723961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24580199717441150980597229 9217574894040431617723961)
        ·
          refine ⟨6913181170530323713292971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9217574894040431617723961 6913181170530323713292971)
          ·
            refine ⟨10369771755795485569939457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6913181170530323713292971 10369771755795485569939457)
            ·
              refine ⟨7777328816846614177454593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10369771755795485569939457 7777328816846614177454593)
              ·
                refine ⟨5832996612634960633090945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7777328816846614177454593 5832996612634960633090945)
                ·
                  refine ⟨4374747459476220474818209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5832996612634960633090945 4374747459476220474818209)
                  ·
                    refine ⟨3281060594607165356113657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4374747459476220474818209 3281060594607165356113657)
                    ·
                      refine ⟨2460795445955374017085243, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3281060594607165356113657 2460795445955374017085243)
                      ·
                        rfl

theorem cell23_4792382_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 2, 1, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 2, 1, 2, 2, 2, 2, 2].length) (baseStart_4792382 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4792382 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4792382 prefixEnd_4792382 := by exact prefixLift 4792382
  have htrace : WordTrace (prefixWord ++ tailWord_4792382) baseStart_4792382 baseEnd_4792382 := by
    simpa [prefixWord, tailWord_4792382, baseEnd_4792382] using wordTrace_append hprefix tailTrace_4792382
  have hstable : (prefixWord ++ tailWord_4792382).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4792382).length < 2 ^ (prefixWord ++ tailWord_4792382).sum := by decide
  have hdescent : baseEnd_4792382 < baseStart_4792382 := by decide
  rcases family_descends (prefixWord ++ tailWord_4792382) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4792384 : List Nat := [2, 1, 1, 2, 2, 4, 2, 2, 2, 5]
def baseStart_4792384 : Nat := 118140960795 + 4792384 * 2 ^ 59
def prefixEnd_4792384 : Nat := 4983230072969 + 3 ^ 40 * 4792384 * 2
def baseEnd_4792384 : Nat := 820265490972227669753411

theorem tailTrace_4792384 : CollatzResearch.WordTrace tailWord_4792384 prefixEnd_4792384 820265490972227669753411 := by
  unfold tailWord_4792384
  simp only [CollatzResearch.WordTrace]
  refine ⟨87396302135009358435132103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116528402846679144580176137 87396302135009358435132103)
  ·
    refine ⟨131094453202514037652698155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87396302135009358435132103 131094453202514037652698155)
    ·
      refine ⟨196641679803771056479047233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 131094453202514037652698155 196641679803771056479047233)
      ·
        refine ⟨147481259852828292359285425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 196641679803771056479047233 147481259852828292359285425)
        ·
          refine ⟨110610944889621219269464069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 147481259852828292359285425 110610944889621219269464069)
          ·
            refine ⟨20739552166803978613024513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 110610944889621219269464069 20739552166803978613024513)
            ·
              refine ⟨15554664125102983959768385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20739552166803978613024513 15554664125102983959768385)
              ·
                refine ⟨11665998093827237969826289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15554664125102983959768385 11665998093827237969826289)
                ·
                  refine ⟨8749498570370428477369717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11665998093827237969826289 8749498570370428477369717)
                  ·
                    refine ⟨820265490972227669753411, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8749498570370428477369717 820265490972227669753411)
                    ·
                      rfl

theorem cell23_4792384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 2, 2, 2, 5].length) (baseStart_4792384 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4792384 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4792384 prefixEnd_4792384 := by exact prefixLift 4792384
  have htrace : WordTrace (prefixWord ++ tailWord_4792384) baseStart_4792384 baseEnd_4792384 := by
    simpa [prefixWord, tailWord_4792384, baseEnd_4792384] using wordTrace_append hprefix tailTrace_4792384
  have hstable : (prefixWord ++ tailWord_4792384).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4792384).length < 2 ^ (prefixWord ++ tailWord_4792384).sum := by decide
  have hdescent : baseEnd_4792384 < baseStart_4792384 := by decide
  rcases family_descends (prefixWord ++ tailWord_4792384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4792404 : List Nat := [2, 4, 1, 1, 1, 1, 1, 4, 1, 3, 4]
def baseStart_4792404 : Nat := 118140960795 + 4792404 * 2 ^ 59
def prefixEnd_4792404 : Nat := 4983230072969 + 3 ^ 40 * 4792404 * 2
def baseEnd_4792404 : Nat := 2460806742529772931010141

theorem tailTrace_4792404 : CollatzResearch.WordTrace tailWord_4792404 prefixEnd_4792404 2460806742529772931010141 := by
  unfold tailWord_4792404
  simp only [CollatzResearch.WordTrace]
  refine ⟨87396666864973130142996133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116528889153297506857328177 87396666864973130142996133)
  ·
    refine ⟨16386875037182461901811775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 87396666864973130142996133 16386875037182461901811775)
    ·
      refine ⟨24580312555773692852717663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16386875037182461901811775 24580312555773692852717663)
      ·
        refine ⟨36870468833660539279076495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24580312555773692852717663 36870468833660539279076495)
        ·
          refine ⟨55305703250490808918614743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36870468833660539279076495 55305703250490808918614743)
          ·
            refine ⟨82958554875736213377922115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55305703250490808918614743 82958554875736213377922115)
            ·
              refine ⟨124437832313604320066883173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 82958554875736213377922115 124437832313604320066883173)
              ·
                refine ⟨23332093558800810012540595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 124437832313604320066883173 23332093558800810012540595)
                ·
                  refine ⟨34998140338201215018810893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23332093558800810012540595 34998140338201215018810893)
                  ·
                    refine ⟨13124302626825455632054085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 34998140338201215018810893 13124302626825455632054085)
                    ·
                      refine ⟨2460806742529772931010141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13124302626825455632054085 2460806742529772931010141)
                      ·
                        rfl

theorem cell23_4792404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 1, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 1, 4, 1, 3, 4].length) (baseStart_4792404 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4792404 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4792404 prefixEnd_4792404 := by exact prefixLift 4792404
  have htrace : WordTrace (prefixWord ++ tailWord_4792404) baseStart_4792404 baseEnd_4792404 := by
    simpa [prefixWord, tailWord_4792404, baseEnd_4792404] using wordTrace_append hprefix tailTrace_4792404
  have hstable : (prefixWord ++ tailWord_4792404).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4792404).length < 2 ^ (prefixWord ++ tailWord_4792404).sum := by decide
  have hdescent : baseEnd_4792404 < baseStart_4792404 := by decide
  rcases family_descends (prefixWord ++ tailWord_4792404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4792421 : List Nat := [1, 3, 1, 3, 2, 2, 3, 1, 2, 1, 4]
def baseStart_4792421 : Nat := 118140960795 + 4792421 * 2 ^ 59
def prefixEnd_4792421 : Nat := 4983230072969 + 3 ^ 40 * 4792421 * 2
def baseEnd_4792421 : Nat := 2460815471700899364497563

theorem tailTrace_4792421 : CollatzResearch.WordTrace tailWord_4792421 prefixEnd_4792421 2460815471700899364497563 := by
  unfold tailWord_4792421
  simp only [CollatzResearch.WordTrace]
  refine ⟨174793953770884672189361117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116529302513923114792907411 174793953770884672189361117)
  ·
    refine ⟨65547732664081752071010419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 174793953770884672189361117 65547732664081752071010419)
    ·
      refine ⟨98321598996122628106515629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65547732664081752071010419 98321598996122628106515629)
      ·
        refine ⟨36870599623545985539943361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 98321598996122628106515629 36870599623545985539943361)
        ·
          refine ⟨27652949717659489154957521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36870599623545985539943361 27652949717659489154957521)
          ·
            refine ⟨20739712288244616866218141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27652949717659489154957521 20739712288244616866218141)
            ·
              refine ⟨7777392108091731324831803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20739712288244616866218141 7777392108091731324831803)
              ·
                refine ⟨11666088162137596987247705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7777392108091731324831803 11666088162137596987247705)
                ·
                  refine ⟨8749566121603197740435779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11666088162137596987247705 8749566121603197740435779)
                  ·
                    refine ⟨13124349182404796610653669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8749566121603197740435779 13124349182404796610653669)
                    ·
                      refine ⟨2460815471700899364497563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13124349182404796610653669 2460815471700899364497563)
                      ·
                        rfl

theorem cell23_4792421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 3, 1, 2, 1, 4].length) (baseStart_4792421 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4792421 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4792421 prefixEnd_4792421 := by exact prefixLift 4792421
  have htrace : WordTrace (prefixWord ++ tailWord_4792421) baseStart_4792421 baseEnd_4792421 := by
    simpa [prefixWord, tailWord_4792421, baseEnd_4792421] using wordTrace_append hprefix tailTrace_4792421
  have hstable : (prefixWord ++ tailWord_4792421).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4792421).length < 2 ^ (prefixWord ++ tailWord_4792421).sum := by decide
  have hdescent : baseEnd_4792421 < baseStart_4792421 := by decide
  rcases family_descends (prefixWord ++ tailWord_4792421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4792434 : List Nat := [3, 2, 1, 2, 2, 2, 1, 1, 2, 1, 6]
def baseStart_4792434 : Nat := 118140960795 + 4792434 * 2 ^ 59
def prefixEnd_4792434 : Nat := 4983230072969 + 3 ^ 40 * 4792434 * 2
def baseEnd_4792434 : Nat := 2460822146949407813635003

theorem tailTrace_4792434 : CollatzResearch.WordTrace tailWord_4792434 prefixEnd_4792434 2460822146949407813635003 := by
  unfold tailWord_4792434
  simp only [CollatzResearch.WordTrace]
  refine ⟨43698606979959393852396089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 116529618613225050273056237 43698606979959393852396089)
  ·
    refine ⟨32773955234969545389297067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43698606979959393852396089 32773955234969545389297067)
    ·
      refine ⟨49160932852454318083945601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32773955234969545389297067 49160932852454318083945601)
      ·
        refine ⟨36870699639340738562959201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49160932852454318083945601 36870699639340738562959201)
        ·
          refine ⟨27653024729505553922219401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36870699639340738562959201 27653024729505553922219401)
          ·
            refine ⟨20739768547129165441664551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27653024729505553922219401 20739768547129165441664551)
            ·
              refine ⟨31109652820693748162496827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20739768547129165441664551 31109652820693748162496827)
              ·
                refine ⟨46664479231040622243745241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31109652820693748162496827 46664479231040622243745241)
                ·
                  refine ⟨34998359423280466682808931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 46664479231040622243745241 34998359423280466682808931)
                  ·
                    refine ⟨52497539134920700024213397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 34998359423280466682808931 52497539134920700024213397)
                    ·
                      refine ⟨2460822146949407813635003, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 52497539134920700024213397 2460822146949407813635003)
                      ·
                        rfl

theorem cell23_4792434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 1, 1, 2, 1, 6].length) (baseStart_4792434 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4792434 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4792434 prefixEnd_4792434 := by exact prefixLift 4792434
  have htrace : WordTrace (prefixWord ++ tailWord_4792434) baseStart_4792434 baseEnd_4792434 := by
    simpa [prefixWord, tailWord_4792434, baseEnd_4792434] using wordTrace_append hprefix tailTrace_4792434
  have hstable : (prefixWord ++ tailWord_4792434).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4792434).length < 2 ^ (prefixWord ++ tailWord_4792434).sum := by decide
  have hdescent : baseEnd_4792434 < baseStart_4792434 := by decide
  rcases family_descends (prefixWord ++ tailWord_4792434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4792438 : List Nat := [5, 1, 1, 2, 1, 2, 1, 2, 2, 4, 2]
def baseStart_4792438 : Nat := 118140960795 + 4792438 * 2 ^ 59
def prefixEnd_4792438 : Nat := 4983230072969 + 3 ^ 40 * 4792438 * 2
def baseEnd_4792438 : Nat := 2460824200872025797984985

theorem tailTrace_4792438 : CollatzResearch.WordTrace tailWord_4792438 prefixEnd_4792438 2460824200872025797984985 := by
  unfold tailWord_4792438
  simp only [CollatzResearch.WordTrace]
  refine ⟨10924660863238942755795623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 116529715874548722728486645 10924660863238942755795623)
  ·
    refine ⟨16386991294858414133693435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10924660863238942755795623 16386991294858414133693435)
    ·
      refine ⟨24580486942287621200540153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16386991294858414133693435 24580486942287621200540153)
      ·
        refine ⟨18435365206715715900405115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24580486942287621200540153 18435365206715715900405115)
        ·
          refine ⟨27653047810073573850607673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18435365206715715900405115 27653047810073573850607673)
          ·
            refine ⟨20739785857555180387955755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27653047810073573850607673 20739785857555180387955755)
            ·
              refine ⟨31109678786332770581933633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20739785857555180387955755 31109678786332770581933633)
              ·
                refine ⟨23332259089749577936450225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31109678786332770581933633 23332259089749577936450225)
                ·
                  refine ⟨17499194317312183452337669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23332259089749577936450225 17499194317312183452337669)
                  ·
                    refine ⟨3281098934496034397313313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17499194317312183452337669 3281098934496034397313313)
                    ·
                      refine ⟨2460824200872025797984985, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3281098934496034397313313 2460824200872025797984985)
                      ·
                        rfl

theorem cell23_4792438_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 1, 2, 2, 4, 2].length) (baseStart_4792438 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4792438 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4792438 prefixEnd_4792438 := by exact prefixLift 4792438
  have htrace : WordTrace (prefixWord ++ tailWord_4792438) baseStart_4792438 baseEnd_4792438 := by
    simpa [prefixWord, tailWord_4792438, baseEnd_4792438] using wordTrace_append hprefix tailTrace_4792438
  have hstable : (prefixWord ++ tailWord_4792438).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4792438).length < 2 ^ (prefixWord ++ tailWord_4792438).sum := by decide
  have hdescent : baseEnd_4792438 < baseStart_4792438 := by decide
  rcases family_descends (prefixWord ++ tailWord_4792438) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4792444 : List Nat := [2, 2, 2, 1, 1, 5, 1, 1, 8]
def baseStart_4792444 : Nat := 118140960795 + 4792444 * 2 ^ 59
def prefixEnd_4792444 : Nat := 4983230072969 + 3 ^ 40 * 4792444 * 2
def baseEnd_4792444 : Nat := 273425253528439197167773

theorem tailTrace_4792444 : CollatzResearch.WordTrace tailWord_4792444 prefixEnd_4792444 273425253528439197167773 := by
  unfold tailWord_4792444
  simp only [CollatzResearch.WordTrace]
  refine ⟨87397396324900673558724193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116529861766534231411632257 87397396324900673558724193)
  ·
    refine ⟨65548047243675505169043145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 87397396324900673558724193 65548047243675505169043145)
    ·
      refine ⟨49161035432756628876782359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 65548047243675505169043145 49161035432756628876782359)
      ·
        refine ⟨73741553149134943315173539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49161035432756628876782359 73741553149134943315173539)
        ·
          refine ⟨110612329723702414972760309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 73741553149134943315173539 110612329723702414972760309)
          ·
            refine ⟨10369905911597101403696279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 110612329723702414972760309 10369905911597101403696279)
            ·
              refine ⟨15554858867395652105544419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10369905911597101403696279 15554858867395652105544419)
              ·
                refine ⟨23332288301093478158316629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15554858867395652105544419 23332288301093478158316629)
                ·
                  refine ⟨273425253528439197167773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 23332288301093478158316629 273425253528439197167773)
                  ·
                    rfl

theorem cell23_4792444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 5, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 5, 1, 1, 8].length) (baseStart_4792444 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4792444 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4792444 prefixEnd_4792444 := by exact prefixLift 4792444
  have htrace : WordTrace (prefixWord ++ tailWord_4792444) baseStart_4792444 baseEnd_4792444 := by
    simpa [prefixWord, tailWord_4792444, baseEnd_4792444] using wordTrace_append hprefix tailTrace_4792444
  have hstable : (prefixWord ++ tailWord_4792444).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4792444).length < 2 ^ (prefixWord ++ tailWord_4792444).sum := by decide
  have hdescent : baseEnd_4792444 < baseStart_4792444 := by decide
  rcases family_descends (prefixWord ++ tailWord_4792444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4792482 : List Nat := [3, 3, 1, 3, 1, 3, 1, 3, 1, 4]
def baseStart_4792482 : Nat := 118140960795 + 4792482 * 2 ^ 59
def prefixEnd_4792482 : Nat := 4983230072969 + 3 ^ 40 * 4792482 * 2
def baseEnd_4792482 : Nat := 820282264673607875278261

theorem tailTrace_4792482 : CollatzResearch.WordTrace tailWord_4792482 prefixEnd_4792482 820282264673607875278261 := by
  unfold tailWord_4792482
  simp only [CollatzResearch.WordTrace]
  refine ⟨43699044655915919901832925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 116530785749109119738221133 43699044655915919901832925)
  ·
    refine ⟨16387141745968469963187347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 43699044655915919901832925 16387141745968469963187347)
    ·
      refine ⟨24580712618952704944781021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16387141745968469963187347 24580712618952704944781021)
      ·
        refine ⟨9217767232107264354292883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24580712618952704944781021 9217767232107264354292883)
        ·
          refine ⟨13826650848160896531439325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9217767232107264354292883 13826650848160896531439325)
          ·
            refine ⟨5184994068060336199289747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13826650848160896531439325 5184994068060336199289747)
            ·
              refine ⟨7777491102090504298934621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5184994068060336199289747 7777491102090504298934621)
              ·
                refine ⟨2916559163283939112100483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7777491102090504298934621 2916559163283939112100483)
                ·
                  refine ⟨4374838744925908668150725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2916559163283939112100483 4374838744925908668150725)
                  ·
                    refine ⟨820282264673607875278261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4374838744925908668150725 820282264673607875278261)
                    ·
                      rfl

theorem cell23_4792482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 3, 1, 3, 1, 4].length) (baseStart_4792482 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4792482 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4792482 prefixEnd_4792482 := by exact prefixLift 4792482
  have htrace : WordTrace (prefixWord ++ tailWord_4792482) baseStart_4792482 baseEnd_4792482 := by
    simpa [prefixWord, tailWord_4792482, baseEnd_4792482] using wordTrace_append hprefix tailTrace_4792482
  have hstable : (prefixWord ++ tailWord_4792482).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4792482).length < 2 ^ (prefixWord ++ tailWord_4792482).sum := by decide
  have hdescent : baseEnd_4792482 < baseStart_4792482 := by decide
  rcases family_descends (prefixWord ++ tailWord_4792482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4792498 : List Nat := [3, 2, 1, 1, 1, 3, 3, 2, 2, 3, 2]
def baseStart_4792498 : Nat := 118140960795 + 4792498 * 2 ^ 59
def prefixEnd_4792498 : Nat := 4983230072969 + 3 ^ 40 * 4792498 * 2
def baseEnd_4792498 : Nat := 2460855009711295563234709

theorem tailTrace_4792498 : CollatzResearch.WordTrace tailWord_4792498 prefixEnd_4792498 2460855009711295563234709 := by
  unfold tailWord_4792498
  simp only [CollatzResearch.WordTrace]
  refine ⟨43699190547901428584978537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 116531174794403809559942765 43699190547901428584978537)
  ·
    refine ⟨32774392910926071438733903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43699190547901428584978537 32774392910926071438733903)
    ·
      refine ⟨49161589366389107158100855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32774392910926071438733903 49161589366389107158100855)
      ·
        refine ⟨73742384049583660737151283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49161589366389107158100855 73742384049583660737151283)
        ·
          refine ⟨110613576074375491105726925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 73742384049583660737151283 110613576074375491105726925)
          ·
            refine ⟨41480091027890809164647597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 110613576074375491105726925 41480091027890809164647597)
            ·
              refine ⟨15555034135459053436742849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 41480091027890809164647597 15555034135459053436742849)
              ·
                refine ⟨11666275601594290077557137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15555034135459053436742849 11666275601594290077557137)
                ·
                  refine ⟨8749706701195717558167853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11666275601594290077557137 8749706701195717558167853)
                  ·
                    refine ⟨3281140012948394084312945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8749706701195717558167853 3281140012948394084312945)
                    ·
                      refine ⟨2460855009711295563234709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3281140012948394084312945 2460855009711295563234709)
                      ·
                        rfl

theorem cell23_4792498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 3, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 3, 2, 2, 3, 2].length) (baseStart_4792498 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4792498 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4792498 prefixEnd_4792498 := by exact prefixLift 4792498
  have htrace : WordTrace (prefixWord ++ tailWord_4792498) baseStart_4792498 baseEnd_4792498 := by
    simpa [prefixWord, tailWord_4792498, baseEnd_4792498] using wordTrace_append hprefix tailTrace_4792498
  have hstable : (prefixWord ++ tailWord_4792498).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4792498).length < 2 ^ (prefixWord ++ tailWord_4792498).sum := by decide
  have hdescent : baseEnd_4792498 < baseStart_4792498 := by decide
  rcases family_descends (prefixWord ++ tailWord_4792498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4792588 : List Nat := [2, 2, 1, 2, 2, 2, 1, 3, 3, 3, 2]
def baseStart_4792588 : Nat := 118140960795 + 4792588 * 2 ^ 59
def prefixEnd_4792588 : Nat := 4983230072969 + 3 ^ 40 * 4792588 * 2
def baseEnd_4792588 : Nat := 2460901222970200211109295

theorem tailTrace_4792588 : CollatzResearch.WordTrace tailWord_4792588 prefixEnd_4792588 2460901222970200211109295 := by
  unfold tailWord_4792588
  simp only [CollatzResearch.WordTrace]
  refine ⟨87400022380639829855345209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116533363174186439807126945 87400022380639829855345209)
  ·
    refine ⟨65550016785479872391508907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 87400022380639829855345209 65550016785479872391508907)
    ·
      refine ⟨98325025178219808587263361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65550016785479872391508907 98325025178219808587263361)
      ·
        refine ⟨73743768883664856440447521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 98325025178219808587263361 73743768883664856440447521)
        ·
          refine ⟨55307826662748642330335641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 73743768883664856440447521 55307826662748642330335641)
          ·
            refine ⟨41480869997061481747751731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 55307826662748642330335641 41480869997061481747751731)
            ·
              refine ⟨62221304995592222621627597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41480869997061481747751731 62221304995592222621627597)
              ·
                refine ⟨23332989373347083483110349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 62221304995592222621627597 23332989373347083483110349)
                ·
                  refine ⟨8749871015005156306166381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23332989373347083483110349 8749871015005156306166381)
                  ·
                    refine ⟨3281201630626933614812393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8749871015005156306166381 3281201630626933614812393)
                    ·
                      refine ⟨2460901222970200211109295, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3281201630626933614812393 2460901222970200211109295)
                      ·
                        rfl

theorem cell23_4792588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 1, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 1, 3, 3, 3, 2].length) (baseStart_4792588 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4792588 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4792588 prefixEnd_4792588 := by exact prefixLift 4792588
  have htrace : WordTrace (prefixWord ++ tailWord_4792588) baseStart_4792588 baseEnd_4792588 := by
    simpa [prefixWord, tailWord_4792588, baseEnd_4792588] using wordTrace_append hprefix tailTrace_4792588
  have hstable : (prefixWord ++ tailWord_4792588).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4792588).length < 2 ^ (prefixWord ++ tailWord_4792588).sum := by decide
  have hdescent : baseEnd_4792588 < baseStart_4792588 := by decide
  rcases family_descends (prefixWord ++ tailWord_4792588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4792612 : List Nat := [2, 3, 1, 3, 1, 4, 1, 2, 2, 1, 3]
def baseStart_4792612 : Nat := 118140960795 + 4792612 * 2 ^ 59
def prefixEnd_4792612 : Nat := 4983230072969 + 3 ^ 40 * 4792612 * 2
def baseEnd_4792612 : Nat := 2460913546505908117209185

theorem tailTrace_4792612 : CollatzResearch.WordTrace tailWord_4792612 prefixEnd_4792612 2460913546505908117209185 := by
  unfold tailWord_4792612
  simp only [CollatzResearch.WordTrace]
  refine ⟨87400460056596355904782045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116533946742128474539709393 87400460056596355904782045)
  ·
    refine ⟨32775172521223633464293267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 87400460056596355904782045 32775172521223633464293267)
    ·
      refine ⟨49162758781835450196439901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32775172521223633464293267 49162758781835450196439901)
      ·
        refine ⟨18436034543188293823664963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 49162758781835450196439901 18436034543188293823664963)
        ·
          refine ⟨27654051814782440735497445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18436034543188293823664963 27654051814782440735497445)
          ·
            refine ⟨5185134715271707637905771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 27654051814782440735497445 5185134715271707637905771)
            ·
              refine ⟨7777702072907561456858657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5185134715271707637905771 7777702072907561456858657)
              ·
                refine ⟨5833276554680671092643993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7777702072907561456858657 5833276554680671092643993)
                ·
                  refine ⟨4374957416010503319482995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5833276554680671092643993 4374957416010503319482995)
                  ·
                    refine ⟨6562436124015754979224493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4374957416010503319482995 6562436124015754979224493)
                    ·
                      refine ⟨2460913546505908117209185, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6562436124015754979224493 2460913546505908117209185)
                      ·
                        rfl

theorem cell23_4792612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 4, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 4, 1, 2, 2, 1, 3].length) (baseStart_4792612 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4792612 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4792612 prefixEnd_4792612 := by exact prefixLift 4792612
  have htrace : WordTrace (prefixWord ++ tailWord_4792612) baseStart_4792612 baseEnd_4792612 := by
    simpa [prefixWord, tailWord_4792612, baseEnd_4792612] using wordTrace_append hprefix tailTrace_4792612
  have hstable : (prefixWord ++ tailWord_4792612).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4792612).length < 2 ^ (prefixWord ++ tailWord_4792612).sum := by decide
  have hdescent : baseEnd_4792612 < baseStart_4792612 := by decide
  rcases family_descends (prefixWord ++ tailWord_4792612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4792628 : List Nat := [2, 5, 1, 1, 1, 2, 2, 1, 2, 6]
def baseStart_4792628 : Nat := 118140960795 + 4792628 * 2 ^ 59
def prefixEnd_4792628 : Nat := 4983230072969 + 3 ^ 40 * 4792628 * 2
def baseEnd_4792628 : Nat := 820307254065460018203037

theorem tailTrace_4792628 : CollatzResearch.WordTrace tailWord_4792628 prefixEnd_4792628 820307254065460018203037 := by
  unfold tailWord_4792628
  simp only [CollatzResearch.WordTrace]
  refine ⟨87400751840567373271073269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116534335787423164361431025 87400751840567373271073269)
  ·
    refine ⟨8193820485053191244163119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 87400751840567373271073269 8193820485053191244163119)
    ·
      refine ⟨12290730727579786866244679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8193820485053191244163119 12290730727579786866244679)
      ·
        refine ⟨18436096091369680299367019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12290730727579786866244679 18436096091369680299367019)
        ·
          refine ⟨27654144137054520449050529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18436096091369680299367019 27654144137054520449050529)
          ·
            refine ⟨20740608102790890336787897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27654144137054520449050529 20740608102790890336787897)
            ·
              refine ⟨15555456077093167752590923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20740608102790890336787897 15555456077093167752590923)
              ·
                refine ⟨23333184115639751628886385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15555456077093167752590923 23333184115639751628886385)
                ·
                  refine ⟨17499888086729813721664789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23333184115639751628886385 17499888086729813721664789)
                  ·
                    refine ⟨820307254065460018203037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17499888086729813721664789 820307254065460018203037)
                    ·
                      rfl

theorem cell23_4792628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 2, 1, 2, 6].length) (baseStart_4792628 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4792628 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4792628 prefixEnd_4792628 := by exact prefixLift 4792628
  have htrace : WordTrace (prefixWord ++ tailWord_4792628) baseStart_4792628 baseEnd_4792628 := by
    simpa [prefixWord, tailWord_4792628, baseEnd_4792628] using wordTrace_append hprefix tailTrace_4792628
  have hstable : (prefixWord ++ tailWord_4792628).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4792628).length < 2 ^ (prefixWord ++ tailWord_4792628).sum := by decide
  have hdescent : baseEnd_4792628 < baseStart_4792628 := by decide
  rcases family_descends (prefixWord ++ tailWord_4792628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4792651 : List Nat := [1, 1, 1, 1, 3, 1, 1, 4, 4, 3, 3]
def baseStart_4792651 : Nat := 118140960795 + 4792651 * 2 ^ 59
def prefixEnd_4792651 : Nat := 4983230072969 + 3 ^ 40 * 4792651 * 2
def baseEnd_4792651 : Nat := 2460933572251433464621505

theorem tailTrace_4792651 : CollatzResearch.WordTrace tailWord_4792651 prefixEnd_4792651 2460933572251433464621505 := by
  unfold tailWord_4792651
  simp only [CollatzResearch.WordTrace]
  refine ⟨174802342560051421470233807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116534895040034280980155871 174802342560051421470233807)
  ·
    refine ⟨262203513840077132205350711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 174802342560051421470233807 262203513840077132205350711)
    ·
      refine ⟨393305270760115698308026067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 262203513840077132205350711 393305270760115698308026067)
      ·
        refine ⟨589957906140173547462039101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 393305270760115698308026067 589957906140173547462039101)
        ·
          refine ⟨221234214802565080298264663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 589957906140173547462039101 221234214802565080298264663)
          ·
            refine ⟨331851322203847620447396995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 221234214802565080298264663 331851322203847620447396995)
            ·
              refine ⟨497776983305771430671095493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 331851322203847620447396995 497776983305771430671095493)
              ·
                refine ⟨93333184369832143250830405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 497776983305771430671095493 93333184369832143250830405)
                ·
                  refine ⟨17499972069343526859530701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 93333184369832143250830405 17499972069343526859530701)
                  ·
                    refine ⟨6562489526003822572324013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17499972069343526859530701 6562489526003822572324013)
                    ·
                      refine ⟨2460933572251433464621505, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6562489526003822572324013 2460933572251433464621505)
                      ·
                        rfl

theorem cell23_4792651_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 4, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 4, 4, 3, 3].length) (baseStart_4792651 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4792651 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4792651 prefixEnd_4792651 := by exact prefixLift 4792651
  have htrace : WordTrace (prefixWord ++ tailWord_4792651) baseStart_4792651 baseEnd_4792651 := by
    simpa [prefixWord, tailWord_4792651, baseEnd_4792651] using wordTrace_append hprefix tailTrace_4792651
  have hstable : (prefixWord ++ tailWord_4792651).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4792651).length < 2 ^ (prefixWord ++ tailWord_4792651).sum := by decide
  have hdescent : baseEnd_4792651 < baseStart_4792651 := by decide
  rcases family_descends (prefixWord ++ tailWord_4792651) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4792671 : List Nat := [1, 1, 2, 3, 1, 2, 3, 1, 4, 5]
def baseStart_4792671 : Nat := 118140960795 + 4792671 * 2 ^ 59
def prefixEnd_4792671 : Nat := 4983230072969 + 3 ^ 40 * 4792671 * 2
def baseEnd_4792671 : Nat := 820314613954841128790471

theorem tailTrace_4792671 : CollatzResearch.WordTrace tailWord_4792671 prefixEnd_4792671 820314613954841128790471 := by
  unfold tailWord_4792671
  simp only [CollatzResearch.WordTrace]
  refine ⟨174803072019978964885961867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116535381346652643257307911 174803072019978964885961867)
  ·
    refine ⟨262204608029968447328942801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 174803072019978964885961867 262204608029968447328942801)
    ·
      refine ⟨196653456022476335496707101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 262204608029968447328942801 196653456022476335496707101)
      ·
        refine ⟨73745046008428625811265163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 196653456022476335496707101 73745046008428625811265163)
        ·
          refine ⟨110617569012642938716897745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 73745046008428625811265163 110617569012642938716897745)
          ·
            refine ⟨82963176759482204037673309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 110617569012642938716897745 82963176759482204037673309)
            ·
              refine ⟨31111191284805826514127491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 82963176759482204037673309 31111191284805826514127491)
              ·
                refine ⟨46666786927208739771191237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31111191284805826514127491 46666786927208739771191237)
                ·
                  refine ⟨8750022548851638707098357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 46666786927208739771191237 8750022548851638707098357)
                  ·
                    refine ⟨820314613954841128790471, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8750022548851638707098357 820314613954841128790471)
                    ·
                      rfl

theorem cell23_4792671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 3, 1, 4, 5].length) (baseStart_4792671 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4792671 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4792671 prefixEnd_4792671 := by exact prefixLift 4792671
  have htrace : WordTrace (prefixWord ++ tailWord_4792671) baseStart_4792671 baseEnd_4792671 := by
    simpa [prefixWord, tailWord_4792671, baseEnd_4792671] using wordTrace_append hprefix tailTrace_4792671
  have hstable : (prefixWord ++ tailWord_4792671).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4792671).length < 2 ^ (prefixWord ++ tailWord_4792671).sum := by decide
  have hdescent : baseEnd_4792671 < baseStart_4792671 := by decide
  rcases family_descends (prefixWord ++ tailWord_4792671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4792675 : List Nat := [1, 1, 1, 5, 2, 1, 5, 2, 5]
def baseStart_4792675 : Nat := 118140960795 + 4792675 * 2 ^ 59
def prefixEnd_4792675 : Nat := 4983230072969 + 3 ^ 40 * 4792675 * 2
def baseEnd_4792675 : Nat := 273438432865237930080155

theorem tailTrace_4792675 : CollatzResearch.WordTrace tailWord_4792675 prefixEnd_4792675 273438432865237930080155 := by
  unfold tailWord_4792675
  simp only [CollatzResearch.WordTrace]
  refine ⟨174803217911964473569107479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116535478607976315712738319 174803217911964473569107479)
  ·
    refine ⟨262204826867946710353661219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 174803217911964473569107479 262204826867946710353661219)
    ·
      refine ⟨393307240301920065530491829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 262204826867946710353661219 393307240301920065530491829)
      ·
        refine ⟨36872553778305006143483609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 393307240301920065530491829 36872553778305006143483609)
        ·
          refine ⟨27654415333728754607612707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36872553778305006143483609 27654415333728754607612707)
          ·
            refine ⟨41481623000593131911419061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27654415333728754607612707 41481623000593131911419061)
            ·
              refine ⟨3888902156305606116695537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 41481623000593131911419061 3888902156305606116695537)
              ·
                refine ⟨2916676617229204587521653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3888902156305606116695537 2916676617229204587521653)
                ·
                  refine ⟨273438432865237930080155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2916676617229204587521653 273438432865237930080155)
                  ·
                    rfl

theorem cell23_4792675_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 5, 2, 5].length) (baseStart_4792675 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4792675 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4792675 prefixEnd_4792675 := by exact prefixLift 4792675
  have htrace : WordTrace (prefixWord ++ tailWord_4792675) baseStart_4792675 baseEnd_4792675 := by
    simpa [prefixWord, tailWord_4792675, baseEnd_4792675] using wordTrace_append hprefix tailTrace_4792675
  have hstable : (prefixWord ++ tailWord_4792675).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4792675).length < 2 ^ (prefixWord ++ tailWord_4792675).sum := by decide
  have hdescent : baseEnd_4792675 < baseStart_4792675 := by decide
  rcases family_descends (prefixWord ++ tailWord_4792675) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4792681 : List Nat := [1, 2, 1, 1, 1, 3, 5, 1, 1, 2, 5]
def baseStart_4792681 : Nat := 118140960795 + 4792681 * 2 ^ 59
def prefixEnd_4792681 : Nat := 4983230072969 + 3 ^ 40 * 4792681 * 2
def baseEnd_4792681 : Nat := 2460948976671068347246367

theorem tailTrace_4792681 : CollatzResearch.WordTrace tailWord_4792681 prefixEnd_4792681 2460948976671068347246367 := by
  unfold tailWord_4792681
  simp only [CollatzResearch.WordTrace]
  refine ⟨174803436749942736593825897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116535624499961824395883931 174803436749942736593825897)
  ·
    refine ⟨131102577562457052445369423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 174803436749942736593825897 131102577562457052445369423)
    ·
      refine ⟨196653866343685578668054135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 131102577562457052445369423 196653866343685578668054135)
      ·
        refine ⟨294980799515528368002081203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 196653866343685578668054135 294980799515528368002081203)
        ·
          refine ⟨442471199273292552003121805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 294980799515528368002081203 442471199273292552003121805)
          ·
            refine ⟨165926699727484707001170677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 442471199273292552003121805 165926699727484707001170677)
            ·
              refine ⟨15555628099451691281359751, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 165926699727484707001170677 15555628099451691281359751)
              ·
                refine ⟨23333442149177536922039627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15555628099451691281359751 23333442149177536922039627)
                ·
                  refine ⟨35000163223766305383059441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23333442149177536922039627 35000163223766305383059441)
                  ·
                    refine ⟨26250122417824729037294581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 35000163223766305383059441 26250122417824729037294581)
                    ·
                      refine ⟨2460948976671068347246367, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26250122417824729037294581 2460948976671068347246367)
                      ·
                        rfl

theorem cell23_4792681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 5, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 5, 1, 1, 2, 5].length) (baseStart_4792681 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4792681 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4792681 prefixEnd_4792681 := by exact prefixLift 4792681
  have htrace : WordTrace (prefixWord ++ tailWord_4792681) baseStart_4792681 baseEnd_4792681 := by
    simpa [prefixWord, tailWord_4792681, baseEnd_4792681] using wordTrace_append hprefix tailTrace_4792681
  have hstable : (prefixWord ++ tailWord_4792681).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4792681).length < 2 ^ (prefixWord ++ tailWord_4792681).sum := by decide
  have hdescent : baseEnd_4792681 < baseStart_4792681 := by decide
  rcases family_descends (prefixWord ++ tailWord_4792681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4792705 : List Nat := [1, 2, 4, 3, 1, 2, 2, 1, 2, 5]
def baseStart_4792705 : Nat := 118140960795 + 4792705 * 2 ^ 59
def prefixEnd_4792705 : Nat := 4983230072969 + 3 ^ 40 * 4792705 * 2
def baseEnd_4792705 : Nat := 820320433402258751115419

theorem tailTrace_4792705 : CollatzResearch.WordTrace tailWord_4792705 prefixEnd_4792705 820320433402258751115419 := by
  unfold tailWord_4792705
  simp only [CollatzResearch.WordTrace]
  refine ⟨174804312101855788692699569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116536208067903859128466379 174804312101855788692699569)
  ·
    refine ⟨131103234076391841519524677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 174804312101855788692699569 131103234076391841519524677)
    ·
      refine ⟨24581856389323470284910877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 131103234076391841519524677 24581856389323470284910877)
      ·
        refine ⟨9218196145996301356841579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24581856389323470284910877 9218196145996301356841579)
        ·
          refine ⟨13827294218994452035262369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9218196145996301356841579 13827294218994452035262369)
          ·
            refine ⟨10370470664245839026446777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13827294218994452035262369 10370470664245839026446777)
            ·
              refine ⟨7777852998184379269835083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10370470664245839026446777 7777852998184379269835083)
              ·
                refine ⟨11666779497276568904752625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7777852998184379269835083 11666779497276568904752625)
                ·
                  refine ⟨8750084622957426678564469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11666779497276568904752625 8750084622957426678564469)
                  ·
                    refine ⟨820320433402258751115419, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8750084622957426678564469 820320433402258751115419)
                    ·
                      rfl

theorem cell23_4792705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 2, 2, 1, 2, 5].length) (baseStart_4792705 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4792705 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4792705 prefixEnd_4792705 := by exact prefixLift 4792705
  have htrace : WordTrace (prefixWord ++ tailWord_4792705) baseStart_4792705 baseEnd_4792705 := by
    simpa [prefixWord, tailWord_4792705, baseEnd_4792705] using wordTrace_append hprefix tailTrace_4792705
  have hstable : (prefixWord ++ tailWord_4792705).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4792705).length < 2 ^ (prefixWord ++ tailWord_4792705).sum := by decide
  have hdescent : baseEnd_4792705 < baseStart_4792705 := by decide
  rcases family_descends (prefixWord ++ tailWord_4792705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4792726 : List Nat := [5, 3, 1, 2, 1, 1, 1, 4, 5]
def baseStart_4792726 : Nat := 118140960795 + 4792726 * 2 ^ 59
def prefixEnd_4792726 : Nat := 4983230072969 + 3 ^ 40 * 4792726 * 2
def baseEnd_4792726 : Nat := 273441342588946741242629

theorem tailTrace_4792726 : CollatzResearch.WordTrace tailWord_4792726 prefixEnd_4792726 273441342588946741242629 := by
  unfold tailWord_4792726
  simp only [CollatzResearch.WordTrace]
  refine ⟨10925317377173731829950877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 116536718689853139519476021 10925317377173731829950877)
  ·
    refine ⟨4096994016440149436231579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10925317377173731829950877 4096994016440149436231579)
    ·
      refine ⟨6145491024660224154347369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4096994016440149436231579 6145491024660224154347369)
      ·
        refine ⟨4609118268495168115760527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6145491024660224154347369 4609118268495168115760527)
        ·
          refine ⟨6913677402742752173640791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4609118268495168115760527 6913677402742752173640791)
          ·
            refine ⟨10370516104114128260461187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6913677402742752173640791 10370516104114128260461187)
            ·
              refine ⟨15555774156171192390691781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10370516104114128260461187 15555774156171192390691781)
              ·
                refine ⟨2916707654282098573254709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15555774156171192390691781 2916707654282098573254709)
                ·
                  refine ⟨273441342588946741242629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2916707654282098573254709 273441342588946741242629)
                  ·
                    rfl

theorem cell23_4792726_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 1, 1, 1, 4, 5].length) (baseStart_4792726 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4792726 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4792726 prefixEnd_4792726 := by exact prefixLift 4792726
  have htrace : WordTrace (prefixWord ++ tailWord_4792726) baseStart_4792726 baseEnd_4792726 := by
    simpa [prefixWord, tailWord_4792726, baseEnd_4792726] using wordTrace_append hprefix tailTrace_4792726
  have hstable : (prefixWord ++ tailWord_4792726).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4792726).length < 2 ^ (prefixWord ++ tailWord_4792726).sum := by decide
  have hdescent : baseEnd_4792726 < baseStart_4792726 := by decide
  rcases family_descends (prefixWord ++ tailWord_4792726) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4792756 : List Nat := [2, 5, 2, 2, 2, 1, 1, 1, 2, 5]
def baseStart_4792756 : Nat := 118140960795 + 4792756 * 2 ^ 59
def prefixEnd_4792756 : Nat := 4983230072969 + 3 ^ 40 * 4792756 * 2
def baseEnd_4792756 : Nat := 820329162573385184602841

theorem tailTrace_4792756 : CollatzResearch.WordTrace tailWord_4792756 prefixEnd_4792756 820329162573385184602841 := by
  unfold tailWord_4792756
  simp only [CollatzResearch.WordTrace]
  refine ⟨87403086112335512201403061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116537448149780682935204081 87403086112335512201403061)
  ·
    refine ⟨8194039323031454268881537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 87403086112335512201403061 8194039323031454268881537)
    ·
      refine ⟨6145529492273590701661153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8194039323031454268881537 6145529492273590701661153)
      ·
        refine ⟨4609147119205193026245865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6145529492273590701661153 4609147119205193026245865)
        ·
          refine ⟨3456860339403894769684399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4609147119205193026245865 3456860339403894769684399)
          ·
            refine ⟨5185290509105842154526599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3456860339403894769684399 5185290509105842154526599)
            ·
              refine ⟨7777935763658763231789899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5185290509105842154526599 7777935763658763231789899)
              ·
                refine ⟨11666903645488144847684849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7777935763658763231789899 11666903645488144847684849)
                ·
                  refine ⟨8750177734116108635763637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11666903645488144847684849 8750177734116108635763637)
                  ·
                    refine ⟨820329162573385184602841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8750177734116108635763637 820329162573385184602841)
                    ·
                      rfl

theorem cell23_4792756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 2, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 2, 1, 1, 1, 2, 5].length) (baseStart_4792756 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4792756 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4792756 prefixEnd_4792756 := by exact prefixLift 4792756
  have htrace : WordTrace (prefixWord ++ tailWord_4792756) baseStart_4792756 baseEnd_4792756 := by
    simpa [prefixWord, tailWord_4792756, baseEnd_4792756] using wordTrace_append hprefix tailTrace_4792756
  have hstable : (prefixWord ++ tailWord_4792756).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4792756).length < 2 ^ (prefixWord ++ tailWord_4792756).sum := by decide
  have hdescent : baseEnd_4792756 < baseStart_4792756 := by decide
  rcases family_descends (prefixWord ++ tailWord_4792756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4792771 : List Nat := [1, 1, 1, 3, 1, 1, 3, 1, 2, 4, 5]
def baseStart_4792771 : Nat := 118140960795 + 4792771 * 2 ^ 59
def prefixEnd_4792771 : Nat := 4983230072969 + 3 ^ 40 * 4792771 * 2
def baseEnd_4792771 : Nat := 2460995189929972995120953

theorem tailTrace_4792771 : CollatzResearch.WordTrace tailWord_4792771 prefixEnd_4792771 2460995189929972995120953 := by
  unfold tailWord_4792771
  simp only [CollatzResearch.WordTrace]
  refine ⟨174806719319616681964602167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116537812879744454643068111 174806719319616681964602167)
  ·
    refine ⟨262210078979425022946903251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 174806719319616681964602167 262210078979425022946903251)
    ·
      refine ⟨393315118469137534420354877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 262210078979425022946903251 393315118469137534420354877)
      ·
        refine ⟨147493169425926575407633079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 393315118469137534420354877 147493169425926575407633079)
        ·
          refine ⟨221239754138889863111449619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 147493169425926575407633079 221239754138889863111449619)
          ·
            refine ⟨331859631208334794667174429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 221239754138889863111449619 331859631208334794667174429)
            ·
              refine ⟨124447361703125548000190411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 331859631208334794667174429 124447361703125548000190411)
              ·
                refine ⟨186671042554688322000285617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 124447361703125548000190411 186671042554688322000285617)
                ·
                  refine ⟨140003281916016241500214213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 186671042554688322000285617 140003281916016241500214213)
                  ·
                    refine ⟨26250615359253045281290165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 140003281916016241500214213 26250615359253045281290165)
                    ·
                      refine ⟨2460995189929972995120953, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26250615359253045281290165 2460995189929972995120953)
                      ·
                        rfl

theorem cell23_4792771_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 3, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 3, 1, 2, 4, 5].length) (baseStart_4792771 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4792771 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4792771 prefixEnd_4792771 := by exact prefixLift 4792771
  have htrace : WordTrace (prefixWord ++ tailWord_4792771) baseStart_4792771 baseEnd_4792771 := by
    simpa [prefixWord, tailWord_4792771, baseEnd_4792771] using wordTrace_append hprefix tailTrace_4792771
  have hstable : (prefixWord ++ tailWord_4792771).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4792771).length < 2 ^ (prefixWord ++ tailWord_4792771).sum := by decide
  have hdescent : baseEnd_4792771 < baseStart_4792771 := by decide
  rcases family_descends (prefixWord ++ tailWord_4792771) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4792785 : List Nat := [1, 2, 2, 1, 2, 1, 1, 6, 2, 3, 2]
def baseStart_4792785 : Nat := 118140960795 + 4792785 * 2 ^ 59
def prefixEnd_4792785 : Nat := 4983230072969 + 3 ^ 40 * 4792785 * 2
def baseEnd_4792785 : Nat := 2461002378659135940345889

theorem tailTrace_4792785 : CollatzResearch.WordTrace tailWord_4792785 prefixEnd_4792785 2461002378659135940345889 := by
  unfold tailWord_4792785
  simp only [CollatzResearch.WordTrace]
  refine ⟨174807229941565962355611809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116538153294377308237074539 174807229941565962355611809)
  ·
    refine ⟨131105422456174471766708857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 174807229941565962355611809 131105422456174471766708857)
    ·
      refine ⟨98329066842130853825031643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 131105422456174471766708857 98329066842130853825031643)
      ·
        refine ⟨147493600263196280737547465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 98329066842130853825031643 147493600263196280737547465)
        ·
          refine ⟨110620200197397210553160599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 147493600263196280737547465 110620200197397210553160599)
          ·
            refine ⟨165930300296095815829740899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 110620200197397210553160599 165930300296095815829740899)
            ·
              refine ⟨248895450444143723744611349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 165930300296095815829740899 248895450444143723744611349)
              ·
                refine ⟨11666974239569237050528657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 248895450444143723744611349 11666974239569237050528657)
                ·
                  refine ⟨8750230679676927787896493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11666974239569237050528657 8750230679676927787896493)
                  ·
                    refine ⟨3281336504878847920461185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8750230679676927787896493 3281336504878847920461185)
                    ·
                      refine ⟨2461002378659135940345889, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3281336504878847920461185 2461002378659135940345889)
                      ·
                        rfl

theorem cell23_4792785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 6, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 6, 2, 3, 2].length) (baseStart_4792785 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4792785 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4792785 prefixEnd_4792785 := by exact prefixLift 4792785
  have htrace : WordTrace (prefixWord ++ tailWord_4792785) baseStart_4792785 baseEnd_4792785 := by
    simpa [prefixWord, tailWord_4792785, baseEnd_4792785] using wordTrace_append hprefix tailTrace_4792785
  have hstable : (prefixWord ++ tailWord_4792785).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4792785).length < 2 ^ (prefixWord ++ tailWord_4792785).sum := by decide
  have hdescent : baseEnd_4792785 < baseStart_4792785 := by decide
  rcases family_descends (prefixWord ++ tailWord_4792785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4792791 : List Nat := [1, 1, 3, 2, 1, 1, 1, 1, 2, 10]
def baseStart_4792791 : Nat := 118140960795 + 4792791 * 2 ^ 59
def prefixEnd_4792791 : Nat := 4983230072969 + 3 ^ 40 * 4792791 * 2
def baseEnd_4792791 : Nat := 820335153181020972290287

theorem tailTrace_4792791 : CollatzResearch.WordTrace tailWord_4792791 prefixEnd_4792791 820335153181020972290287 := by
  unfold tailWord_4792791
  simp only [CollatzResearch.WordTrace]
  refine ⟨174807448779544225380330227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116538299186362816920220151 174807448779544225380330227)
  ·
    refine ⟨262211173169316338070495341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 174807448779544225380330227 262211173169316338070495341)
    ·
      refine ⟨98329189938493626776435753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 262211173169316338070495341 98329189938493626776435753)
      ·
        refine ⟨73746892453870220082326815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 98329189938493626776435753 73746892453870220082326815)
        ·
          refine ⟨110620338680805330123490223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 73746892453870220082326815 110620338680805330123490223)
          ·
            refine ⟨165930508021207995185235335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 110620338680805330123490223 165930508021207995185235335)
            ·
              refine ⟨248895762031811992777853003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 165930508021207995185235335 248895762031811992777853003)
              ·
                refine ⟨373343643047717989166779505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 248895762031811992777853003 373343643047717989166779505)
                ·
                  refine ⟨280007732285788491875084629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 373343643047717989166779505 280007732285788491875084629)
                  ·
                    refine ⟨820335153181020972290287, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 280007732285788491875084629 820335153181020972290287)
                    ·
                      rfl

theorem cell23_4792791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 1, 2, 10].length) (baseStart_4792791 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4792791 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4792791 prefixEnd_4792791 := by exact prefixLift 4792791
  have htrace : WordTrace (prefixWord ++ tailWord_4792791) baseStart_4792791 baseEnd_4792791 := by
    simpa [prefixWord, tailWord_4792791, baseEnd_4792791] using wordTrace_append hprefix tailTrace_4792791
  have hstable : (prefixWord ++ tailWord_4792791).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4792791).length < 2 ^ (prefixWord ++ tailWord_4792791).sum := by decide
  have hdescent : baseEnd_4792791 < baseStart_4792791 := by decide
  rcases family_descends (prefixWord ++ tailWord_4792791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4792828 : List Nat := [2, 2, 2, 1, 2, 1, 1, 3, 3, 2, 4]
def baseStart_4792828 : Nat := 118140960795 + 4792828 * 2 ^ 59
def prefixEnd_4792828 : Nat := 4983230072969 + 3 ^ 40 * 4792828 * 2
def baseEnd_4792828 : Nat := 2461024458327279272108191

theorem tailTrace_4792828 : CollatzResearch.WordTrace tailWord_4792828 prefixEnd_4792828 2461024458327279272108191 := by
  unfold tailWord_4792828
  simp only [CollatzResearch.WordTrace]
  refine ⟨87404399140205090349713569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116539198853606787132951425 87404399140205090349713569)
  ·
    refine ⟨65553299355153817762285177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 87404399140205090349713569 65553299355153817762285177)
    ·
      refine ⟨49164974516365363321713883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 65553299355153817762285177 49164974516365363321713883)
      ·
        refine ⟨73747461774548044982570825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49164974516365363321713883 73747461774548044982570825)
        ·
          refine ⟨55310596330911033736928119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 73747461774548044982570825 55310596330911033736928119)
          ·
            refine ⟨82965894496366550605392179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55310596330911033736928119 82965894496366550605392179)
            ·
              refine ⟨124448841744549825908088269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 82965894496366550605392179 124448841744549825908088269)
              ·
                refine ⟨46668315654206184715533101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 124448841744549825908088269 46668315654206184715533101)
                ·
                  refine ⟨17500618370327319268324913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 46668315654206184715533101 17500618370327319268324913)
                  ·
                    refine ⟨13125463777745489451243685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17500618370327319268324913 13125463777745489451243685)
                    ·
                      refine ⟨2461024458327279272108191, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13125463777745489451243685 2461024458327279272108191)
                      ·
                        rfl

theorem cell23_4792828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 1, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 1, 3, 3, 2, 4].length) (baseStart_4792828 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4792828 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4792828 prefixEnd_4792828 := by exact prefixLift 4792828
  have htrace : WordTrace (prefixWord ++ tailWord_4792828) baseStart_4792828 baseEnd_4792828 := by
    simpa [prefixWord, tailWord_4792828, baseEnd_4792828] using wordTrace_append hprefix tailTrace_4792828
  have hstable : (prefixWord ++ tailWord_4792828).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4792828).length < 2 ^ (prefixWord ++ tailWord_4792828).sum := by decide
  have hdescent : baseEnd_4792828 < baseStart_4792828 := by decide
  rcases family_descends (prefixWord ++ tailWord_4792828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4792835 : List Nat := [1, 1, 1, 3, 2, 1, 3, 5, 1, 2, 3]
def baseStart_4792835 : Nat := 118140960795 + 4792835 * 2 ^ 59
def prefixEnd_4792835 : Nat := 4983230072969 + 3 ^ 40 * 4792835 * 2
def baseEnd_4792835 : Nat := 2461028052691860744720659

theorem tailTrace_4792835 : CollatzResearch.WordTrace tailWord_4792835 prefixEnd_4792835 2461028052691860744720659 := by
  unfold tailWord_4792835
  simp only [CollatzResearch.WordTrace]
  refine ⟨174809053591384820894931959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116539369060923213929954639 174809053591384820894931959)
  ·
    refine ⟨262213580387077231342397939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 174809053591384820894931959 262213580387077231342397939)
    ·
      refine ⟨393320370580615847013596909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 262213580387077231342397939 393320370580615847013596909)
      ·
        refine ⟨147495138967730942630098841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 393320370580615847013596909 147495138967730942630098841)
        ·
          refine ⟨110621354225798206972574131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 147495138967730942630098841 110621354225798206972574131)
          ·
            refine ⟨165932031338697310458861197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 110621354225798206972574131 165932031338697310458861197)
            ·
              refine ⟨62224511752011491422072949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 165932031338697310458861197 62224511752011491422072949)
              ·
                refine ⟨5833547976751077320819339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 62224511752011491422072949 5833547976751077320819339)
                ·
                  refine ⟨8750321965126615981229009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5833547976751077320819339 8750321965126615981229009)
                  ·
                    refine ⟨6562741473844961985921757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8750321965126615981229009 6562741473844961985921757)
                    ·
                      refine ⟨2461028052691860744720659, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6562741473844961985921757 2461028052691860744720659)
                      ·
                        rfl

theorem cell23_4792835_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 3, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 3, 5, 1, 2, 3].length) (baseStart_4792835 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4792835 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4792835 prefixEnd_4792835 := by exact prefixLift 4792835
  have htrace : WordTrace (prefixWord ++ tailWord_4792835) baseStart_4792835 baseEnd_4792835 := by
    simpa [prefixWord, tailWord_4792835, baseEnd_4792835] using wordTrace_append hprefix tailTrace_4792835
  have hstable : (prefixWord ++ tailWord_4792835).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4792835).length < 2 ^ (prefixWord ++ tailWord_4792835).sum := by decide
  have hdescent : baseEnd_4792835 < baseStart_4792835 := by decide
  rcases family_descends (prefixWord ++ tailWord_4792835) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4792852 : List Nat := [2, 4, 3, 1, 1, 1, 2, 2, 1, 1, 5]
def baseStart_4792852 : Nat := 118140960795 + 4792852 * 2 ^ 59
def prefixEnd_4792852 : Nat := 4983230072969 + 3 ^ 40 * 4792852 * 2
def baseEnd_4792852 : Nat := 2461036781862987178208081

theorem tailTrace_4792852 : CollatzResearch.WordTrace tailWord_4792852 prefixEnd_4792852 2461036781862987178208081 := by
  unfold tailWord_4792852
  simp only [CollatzResearch.WordTrace]
  refine ⟨87404836816161616399150405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116539782421548821865533873 87404836816161616399150405)
  ·
    refine ⟨16388406903030303074840701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 87404836816161616399150405 16388406903030303074840701)
    ·
      refine ⟨6145652588636363653065263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16388406903030303074840701 6145652588636363653065263)
      ·
        refine ⟨9218478882954545479597895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6145652588636363653065263 9218478882954545479597895)
        ·
          refine ⟨13827718324431818219396843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9218478882954545479597895 13827718324431818219396843)
          ·
            refine ⟨20741577486647727329095265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13827718324431818219396843 20741577486647727329095265)
            ·
              refine ⟨15556183114985795496821449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20741577486647727329095265 15556183114985795496821449)
              ·
                refine ⟨11667137336239346622616087, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15556183114985795496821449 11667137336239346622616087)
                ·
                  refine ⟨17500706004359019933924131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11667137336239346622616087 17500706004359019933924131)
                  ·
                    refine ⟨26251059006538529900886197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17500706004359019933924131 26251059006538529900886197)
                    ·
                      refine ⟨2461036781862987178208081, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26251059006538529900886197 2461036781862987178208081)
                      ·
                        rfl

theorem cell23_4792852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 2, 2, 1, 1, 5].length) (baseStart_4792852 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4792852 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4792852 prefixEnd_4792852 := by exact prefixLift 4792852
  have htrace : WordTrace (prefixWord ++ tailWord_4792852) baseStart_4792852 baseEnd_4792852 := by
    simpa [prefixWord, tailWord_4792852, baseEnd_4792852] using wordTrace_append hprefix tailTrace_4792852
  have hstable : (prefixWord ++ tailWord_4792852).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4792852).length < 2 ^ (prefixWord ++ tailWord_4792852).sum := by decide
  have hdescent : baseEnd_4792852 < baseStart_4792852 := by decide
  rcases family_descends (prefixWord ++ tailWord_4792852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4792865 : List Nat := [1, 2, 3, 2, 2, 1, 2, 3, 1, 3, 3]
def baseStart_4792865 : Nat := 118140960795 + 4792865 * 2 ^ 59
def prefixEnd_4792865 : Nat := 4983230072969 + 3 ^ 40 * 4792865 * 2
def baseEnd_4792865 : Nat := 2461043457111495627345521

theorem tailTrace_4792865 : CollatzResearch.WordTrace tailWord_4792865 prefixEnd_4792865 2461043457111495627345521 := by
  unfold tailWord_4792865
  simp only [CollatzResearch.WordTrace]
  refine ⟨174810147781276136018524049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116540098520850757345682699 174810147781276136018524049)
  ·
    refine ⟨131107610835957102013893037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 174810147781276136018524049 131107610835957102013893037)
    ·
      refine ⟨49165354063483913255209889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 131107610835957102013893037 49165354063483913255209889)
      ·
        refine ⟨36874015547612934941407417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49165354063483913255209889 36874015547612934941407417)
        ·
          refine ⟨27655511660709701206055563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36874015547612934941407417 27655511660709701206055563)
          ·
            refine ⟨41483267491064551809083345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27655511660709701206055563 41483267491064551809083345)
            ·
              refine ⟨31112450618298413856812509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 41483267491064551809083345 31112450618298413856812509)
              ·
                refine ⟨11667168981861905196304691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 31112450618298413856812509 11667168981861905196304691)
                ·
                  refine ⟨17500753472792857794457037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11667168981861905196304691 17500753472792857794457037)
                  ·
                    refine ⟨6562782552297321672921389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17500753472792857794457037 6562782552297321672921389)
                    ·
                      refine ⟨2461043457111495627345521, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6562782552297321672921389 2461043457111495627345521)
                      ·
                        rfl

theorem cell23_4792865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 2, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 2, 3, 1, 3, 3].length) (baseStart_4792865 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4792865 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4792865 prefixEnd_4792865 := by exact prefixLift 4792865
  have htrace : WordTrace (prefixWord ++ tailWord_4792865) baseStart_4792865 baseEnd_4792865 := by
    simpa [prefixWord, tailWord_4792865, baseEnd_4792865] using wordTrace_append hprefix tailTrace_4792865
  have hstable : (prefixWord ++ tailWord_4792865).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4792865).length < 2 ^ (prefixWord ++ tailWord_4792865).sum := by decide
  have hdescent : baseEnd_4792865 < baseStart_4792865 := by decide
  rcases family_descends (prefixWord ++ tailWord_4792865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4792886 : List Nat := [5, 1, 2, 1, 2, 2, 3, 1, 1, 2, 3]
def baseStart_4792886 : Nat := 118140960795 + 4792886 * 2 ^ 59
def prefixEnd_4792886 : Nat := 4983230072969 + 3 ^ 40 * 4792886 * 2
def baseEnd_4792886 : Nat := 2461054240205240045182925

theorem tailTrace_4792886 : CollatzResearch.WordTrace tailWord_4792886 prefixEnd_4792886 2461054240205240045182925 := by
  unfold tailWord_4792886
  simp only [CollatzResearch.WordTrace]
  refine ⟨10925682107137503537814907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 116540609142800037736692341 10925682107137503537814907)
  ·
    refine ⟨16388523160706255306722361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10925682107137503537814907 16388523160706255306722361)
    ·
      refine ⟨12291392370529691480041771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16388523160706255306722361 12291392370529691480041771)
      ·
        refine ⟨18437088555794537220062657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12291392370529691480041771 18437088555794537220062657)
        ·
          refine ⟨13827816416845902915046993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18437088555794537220062657 13827816416845902915046993)
          ·
            refine ⟨10370862312634427186285245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13827816416845902915046993 10370862312634427186285245)
            ·
              refine ⟨3889073367237910194856967, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10370862312634427186285245 3889073367237910194856967)
              ·
                refine ⟨5833610050856865292285451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3889073367237910194856967 5833610050856865292285451)
                ·
                  refine ⟨8750415076285297938428177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5833610050856865292285451 8750415076285297938428177)
                  ·
                    refine ⟨6562811307213973453821133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8750415076285297938428177 6562811307213973453821133)
                    ·
                      refine ⟨2461054240205240045182925, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6562811307213973453821133 2461054240205240045182925)
                      ·
                        rfl

theorem cell23_4792886_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 2, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 2, 3, 1, 1, 2, 3].length) (baseStart_4792886 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4792886 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4792886 prefixEnd_4792886 := by exact prefixLift 4792886
  have htrace : WordTrace (prefixWord ++ tailWord_4792886) baseStart_4792886 baseEnd_4792886 := by
    simpa [prefixWord, tailWord_4792886, baseEnd_4792886] using wordTrace_append hprefix tailTrace_4792886
  have hstable : (prefixWord ++ tailWord_4792886).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4792886).length < 2 ^ (prefixWord ++ tailWord_4792886).sum := by decide
  have hdescent : baseEnd_4792886 < baseStart_4792886 := by decide
  rcases family_descends (prefixWord ++ tailWord_4792886) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4792902 : List Nat := [6, 1, 1, 1, 2, 1, 1, 1, 2, 7]
def baseStart_4792902 : Nat := 118140960795 + 4792902 * 2 ^ 59
def prefixEnd_4792902 : Nat := 4983230072969 + 3 ^ 40 * 4792902 * 2
def baseEnd_4792902 : Nat := 820354151965237327527617

theorem tailTrace_4792902 : CollatzResearch.WordTrace tailWord_4792902 prefixEnd_4792902 820354151965237327527617 := by
  unfold tailWord_4792902
  simp only [CollatzResearch.WordTrace]
  refine ⟨5462859290066940354300655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 116540998188094727558413973 5462859290066940354300655)
  ·
    refine ⟨8194288935100410531450983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5462859290066940354300655 8194288935100410531450983)
    ·
      refine ⟨12291433402650615797176475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8194288935100410531450983 12291433402650615797176475)
      ·
        refine ⟨18437150103975923695764713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12291433402650615797176475 18437150103975923695764713)
        ·
          refine ⟨13827862577981942771823535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18437150103975923695764713 13827862577981942771823535)
          ·
            refine ⟨20741793866972914157735303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13827862577981942771823535 20741793866972914157735303)
            ·
              refine ⟨31112690800459371236602955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20741793866972914157735303 31112690800459371236602955)
              ·
                refine ⟨46669036200689056854904433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31112690800459371236602955 46669036200689056854904433)
                ·
                  refine ⟨35001777150516792641178325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 46669036200689056854904433 35001777150516792641178325)
                  ·
                    refine ⟨820354151965237327527617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 35001777150516792641178325 820354151965237327527617)
                    ·
                      rfl

theorem cell23_4792902_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 1, 1, 2, 7].length) (baseStart_4792902 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4792902 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4792902 prefixEnd_4792902 := by exact prefixLift 4792902
  have htrace : WordTrace (prefixWord ++ tailWord_4792902) baseStart_4792902 baseEnd_4792902 := by
    simpa [prefixWord, tailWord_4792902, baseEnd_4792902] using wordTrace_append hprefix tailTrace_4792902
  have hstable : (prefixWord ++ tailWord_4792902).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4792902).length < 2 ^ (prefixWord ++ tailWord_4792902).sum := by decide
  have hdescent : baseEnd_4792902 < baseStart_4792902 := by decide
  rcases family_descends (prefixWord ++ tailWord_4792902) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4792909 : List Nat := [1, 6, 1, 1, 2, 1, 1, 2, 3, 3, 2]
def baseStart_4792909 : Nat := 118140960795 + 4792909 * 2 ^ 59
def prefixEnd_4792909 : Nat := 4983230072969 + 3 ^ 40 * 4792909 * 2
def baseEnd_4792909 : Nat := 2461066050260293455195319

theorem tailTrace_4792909 : CollatzResearch.WordTrace tailWord_4792909 prefixEnd_4792909 2461066050260293455195319 := by
  unfold tailWord_4792909
  simp only [CollatzResearch.WordTrace]
  refine ⟨174811752593116731533125781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116541168395411154355417187 174811752593116731533125781)
  ·
    refine ⟨8194300902802346790615271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 174811752593116731533125781 8194300902802346790615271)
    ·
      refine ⟨12291451354203520185922907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8194300902802346790615271 12291451354203520185922907)
      ·
        refine ⟨18437177031305280278884361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12291451354203520185922907 18437177031305280278884361)
        ·
          refine ⟨13827882773478960209163271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18437177031305280278884361 13827882773478960209163271)
          ·
            refine ⟨20741824160218440313744907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13827882773478960209163271 20741824160218440313744907)
            ·
              refine ⟨31112736240327660470617361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20741824160218440313744907 31112736240327660470617361)
              ·
                refine ⟨23334552180245745352963021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31112736240327660470617361 23334552180245745352963021)
                ·
                  refine ⟨8750457067592154507361133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23334552180245745352963021 8750457067592154507361133)
                  ·
                    refine ⟨3281421400347057940260425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8750457067592154507361133 3281421400347057940260425)
                    ·
                      refine ⟨2461066050260293455195319, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3281421400347057940260425 2461066050260293455195319)
                      ·
                        rfl

theorem cell23_4792909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 1, 2, 3, 3, 2].length) (baseStart_4792909 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4792909 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4792909 prefixEnd_4792909 := by exact prefixLift 4792909
  have htrace : WordTrace (prefixWord ++ tailWord_4792909) baseStart_4792909 baseEnd_4792909 := by
    simpa [prefixWord, tailWord_4792909, baseEnd_4792909] using wordTrace_append hprefix tailTrace_4792909
  have hstable : (prefixWord ++ tailWord_4792909).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4792909).length < 2 ^ (prefixWord ++ tailWord_4792909).sum := by decide
  have hdescent : baseEnd_4792909 < baseStart_4792909 := by decide
  rcases family_descends (prefixWord ++ tailWord_4792909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4792922 : List Nat := [3, 1, 1, 2, 1, 1, 1, 1, 8, 2, 2]
def baseStart_4792922 : Nat := 118140960795 + 4792922 * 2 ^ 59
def prefixEnd_4792922 : Nat := 4983230072969 + 3 ^ 40 * 4792922 * 2
def baseEnd_4792922 : Nat := 2461072725508801904332759

theorem tailTrace_4792922 : CollatzResearch.WordTrace tailWord_4792922 prefixEnd_4792922 2461072725508801904332759 := by
  unfold tailWord_4792922
  simp only [CollatzResearch.WordTrace]
  refine ⟨43703056685517408688337255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 116541484494713089835566013 43703056685517408688337255)
  ·
    refine ⟨65554585028276113032505883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43703056685517408688337255 65554585028276113032505883)
    ·
      refine ⟨98331877542414169548758825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65554585028276113032505883 98331877542414169548758825)
      ·
        refine ⟨73748908156810627161569119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 98331877542414169548758825 73748908156810627161569119)
        ·
          refine ⟨110623362235215940742353679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 73748908156810627161569119 110623362235215940742353679)
          ·
            refine ⟨165935043352823911113530519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 110623362235215940742353679 165935043352823911113530519)
            ·
              refine ⟨248902565029235866670295779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 165935043352823911113530519 248902565029235866670295779)
              ·
                refine ⟨373353847543853800005443669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 248902565029235866670295779 373353847543853800005443669)
                ·
                  refine ⟨4375240400904536718813793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 373353847543853800005443669 4375240400904536718813793)
                  ·
                    refine ⟨3281430300678402539110345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4375240400904536718813793 3281430300678402539110345)
                    ·
                      refine ⟨2461072725508801904332759, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3281430300678402539110345 2461072725508801904332759)
                      ·
                        rfl

theorem cell23_4792922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 1, 8, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 1, 8, 2, 2].length) (baseStart_4792922 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4792922 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4792922 prefixEnd_4792922 := by exact prefixLift 4792922
  have htrace : WordTrace (prefixWord ++ tailWord_4792922) baseStart_4792922 baseEnd_4792922 := by
    simpa [prefixWord, tailWord_4792922, baseEnd_4792922] using wordTrace_append hprefix tailTrace_4792922
  have hstable : (prefixWord ++ tailWord_4792922).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4792922).length < 2 ^ (prefixWord ++ tailWord_4792922).sum := by decide
  have hdescent : baseEnd_4792922 < baseStart_4792922 := by decide
  rcases family_descends (prefixWord ++ tailWord_4792922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4792928 : List Nat := [2, 1, 1, 3, 2, 1, 3, 1, 9]
def baseStart_4792928 : Nat := 118140960795 + 4792928 * 2 ^ 59
def prefixEnd_4792928 : Nat := 4983230072969 + 3 ^ 40 * 4792928 * 2
def baseEnd_4792928 : Nat := 273452867376969875650859

theorem tailTrace_4792928 : CollatzResearch.WordTrace tailWord_4792928 prefixEnd_4792928 273452867376969875650859 := by
  unfold tailWord_4792928
  simp only [CollatzResearch.WordTrace]
  refine ⟨87406222790023948889033719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116541630386698598518711625 87406222790023948889033719)
  ·
    refine ⟨131109334185035923333550579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87406222790023948889033719 131109334185035923333550579)
    ·
      refine ⟨196664001277553885000325869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 131109334185035923333550579 196664001277553885000325869)
      ·
        refine ⟨73749000479082706875122201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 196664001277553885000325869 73749000479082706875122201)
        ·
          refine ⟨55311750359312030156341651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 73749000479082706875122201 55311750359312030156341651)
          ·
            refine ⟨82967625538968045234512477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55311750359312030156341651 82967625538968045234512477)
            ·
              refine ⟨31112859577113016962942179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 82967625538968045234512477 31112859577113016962942179)
              ·
                refine ⟨46669289365669525444413269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31112859577113016962942179 46669289365669525444413269)
                ·
                  refine ⟨273452867376969875650859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 46669289365669525444413269 273452867376969875650859)
                  ·
                    rfl

theorem cell23_4792928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 3, 1, 9].length) (baseStart_4792928 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4792928 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4792928 prefixEnd_4792928 := by exact prefixLift 4792928
  have htrace : WordTrace (prefixWord ++ tailWord_4792928) baseStart_4792928 baseEnd_4792928 := by
    simpa [prefixWord, tailWord_4792928, baseEnd_4792928] using wordTrace_append hprefix tailTrace_4792928
  have hstable : (prefixWord ++ tailWord_4792928).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4792928).length < 2 ^ (prefixWord ++ tailWord_4792928).sum := by decide
  have hdescent : baseEnd_4792928 < baseStart_4792928 := by decide
  rcases family_descends (prefixWord ++ tailWord_4792928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4793009 : List Nat := [1, 2, 2, 6, 1, 1, 1, 2, 2, 5]
def baseStart_4793009 : Nat := 118140960795 + 4793009 * 2 ^ 59
def prefixEnd_4793009 : Nat := 4983230072969 + 3 ^ 40 * 4793009 * 2
def baseEnd_4793009 : Nat := 820372466108581021314953

theorem tailTrace_4793009 : CollatzResearch.WordTrace tailWord_4793009 prefixEnd_4793009 820372466108581021314953 := by
  unfold tailWord_4793009
  simp only [CollatzResearch.WordTrace]
  refine ⟨174815399892754448611766081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116543599928502965741177387 174815399892754448611766081)
  ·
    refine ⟨131111549919565836458824561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 174815399892754448611766081 131111549919565836458824561)
    ·
      refine ⟨98333662439674377344118421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 131111549919565836458824561 98333662439674377344118421)
      ·
        refine ⟨4609390426859736438005551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 98333662439674377344118421 4609390426859736438005551)
        ·
          refine ⟨6914085640289604657008327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4609390426859736438005551 6914085640289604657008327)
          ·
            refine ⟨10371128460434406985512491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6914085640289604657008327 10371128460434406985512491)
            ·
              refine ⟨15556692690651610478268737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10371128460434406985512491 15556692690651610478268737)
              ·
                refine ⟨11667519517988707858701553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15556692690651610478268737 11667519517988707858701553)
                ·
                  refine ⟨8750639638491530894026165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11667519517988707858701553 8750639638491530894026165)
                  ·
                    refine ⟨820372466108581021314953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8750639638491530894026165 820372466108581021314953)
                    ·
                      rfl

theorem cell23_4793009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 1, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 1, 1, 1, 2, 2, 5].length) (baseStart_4793009 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4793009 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4793009 prefixEnd_4793009 := by exact prefixLift 4793009
  have htrace : WordTrace (prefixWord ++ tailWord_4793009) baseStart_4793009 baseEnd_4793009 := by
    simpa [prefixWord, tailWord_4793009, baseEnd_4793009] using wordTrace_append hprefix tailTrace_4793009
  have hstable : (prefixWord ++ tailWord_4793009).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4793009).length < 2 ^ (prefixWord ++ tailWord_4793009).sum := by decide
  have hdescent : baseEnd_4793009 < baseStart_4793009 := by decide
  rcases family_descends (prefixWord ++ tailWord_4793009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4793112 : List Nat := [2, 1, 2, 3, 1, 1, 1, 4, 4, 4]
def baseStart_4793112 : Nat := 118140960795 + 4793112 * 2 ^ 59
def prefixEnd_4793112 : Nat := 4983230072969 + 3 ^ 40 * 4793112 * 2
def baseEnd_4793112 : Nat := 820390095611052053652295

theorem tailTrace_4793112 : CollatzResearch.WordTrace tailWord_4793112 prefixEnd_4793112 820390095611052053652295 := by
  unfold tailWord_4793112
  simp only [CollatzResearch.WordTrace]
  refine ⟨87409578305690648601382795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116546104407587531468510393 87409578305690648601382795)
  ·
    refine ⟨131114367458535972902074193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87409578305690648601382795 131114367458535972902074193)
    ·
      refine ⟨98335775593901979676555645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 131114367458535972902074193 98335775593901979676555645)
      ·
        refine ⟨36875915847713242378708367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 98335775593901979676555645 36875915847713242378708367)
        ·
          refine ⟨55313873771569863568062551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36875915847713242378708367 55313873771569863568062551)
          ·
            refine ⟨82970810657354795352093827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55313873771569863568062551 82970810657354795352093827)
            ·
              refine ⟨124456215986032193028140741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 82970810657354795352093827 124456215986032193028140741)
              ·
                refine ⟨23335540497381036192776389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 124456215986032193028140741 23335540497381036192776389)
                ·
                  refine ⟨4375413843258944286145573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 23335540497381036192776389 4375413843258944286145573)
                  ·
                    refine ⟨820390095611052053652295, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4375413843258944286145573 820390095611052053652295)
                    ·
                      rfl

theorem cell23_4793112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 1, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 1, 4, 4, 4].length) (baseStart_4793112 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4793112 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4793112 prefixEnd_4793112 := by exact prefixLift 4793112
  have htrace : WordTrace (prefixWord ++ tailWord_4793112) baseStart_4793112 baseEnd_4793112 := by
    simpa [prefixWord, tailWord_4793112, baseEnd_4793112] using wordTrace_append hprefix tailTrace_4793112
  have hstable : (prefixWord ++ tailWord_4793112).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4793112).length < 2 ^ (prefixWord ++ tailWord_4793112).sum := by decide
  have hdescent : baseEnd_4793112 < baseStart_4793112 := by decide
  rcases family_descends (prefixWord ++ tailWord_4793112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4793116 : List Nat := [2, 2, 3, 1, 1, 5, 2, 1, 1, 5]
def baseStart_4793116 : Nat := 118140960795 + 4793116 * 2 ^ 59
def prefixEnd_4793116 : Nat := 4983230072969 + 3 ^ 40 * 4793116 * 2
def baseEnd_4793116 : Nat := 820390780251924715102289

theorem tailTrace_4793116 : CollatzResearch.WordTrace tailWord_4793116 prefixEnd_4793116 820390780251924715102289 := by
  unfold tailWord_4793116
  simp only [CollatzResearch.WordTrace]
  refine ⟨87409651251683402942955601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116546201668911203923940801 87409651251683402942955601)
  ·
    refine ⟨65557238438762552207216701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 87409651251683402942955601 65557238438762552207216701)
    ·
      refine ⟨24583964414535957077706263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 65557238438762552207216701 24583964414535957077706263)
      ·
        refine ⟨36875946621803935616559395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24583964414535957077706263 36875946621803935616559395)
        ·
          refine ⟨55313919932705903424839093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36875946621803935616559395 55313919932705903424839093)
          ·
            refine ⟨5185679993691178446078665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 55313919932705903424839093 5185679993691178446078665)
            ·
              refine ⟨3889259995268383834558999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5185679993691178446078665 3889259995268383834558999)
              ·
                refine ⟨5833889992902575751838499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3889259995268383834558999 5833889992902575751838499)
                ·
                  refine ⟨8750834989353863627757749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5833889992902575751838499 8750834989353863627757749)
                  ·
                    refine ⟨820390780251924715102289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8750834989353863627757749 820390780251924715102289)
                    ·
                      rfl

theorem cell23_4793116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 5, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 5, 2, 1, 1, 5].length) (baseStart_4793116 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4793116 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4793116 prefixEnd_4793116 := by exact prefixLift 4793116
  have htrace : WordTrace (prefixWord ++ tailWord_4793116) baseStart_4793116 baseEnd_4793116 := by
    simpa [prefixWord, tailWord_4793116, baseEnd_4793116] using wordTrace_append hprefix tailTrace_4793116
  have hstable : (prefixWord ++ tailWord_4793116).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4793116).length < 2 ^ (prefixWord ++ tailWord_4793116).sum := by decide
  have hdescent : baseEnd_4793116 < baseStart_4793116 := by decide
  rcases family_descends (prefixWord ++ tailWord_4793116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4793119 : List Nat := [1, 1, 2, 4, 2, 3, 1, 3, 1, 1, 4]
def baseStart_4793119 : Nat := 118140960795 + 4793119 * 2 ^ 59
def prefixEnd_4793119 : Nat := 4983230072969 + 3 ^ 40 * 4793119 * 2
def baseEnd_4793119 : Nat := 2461173881197737633569353

theorem tailTrace_4793119 : CollatzResearch.WordTrace tailWord_4793119 prefixEnd_4793119 2461173881197737633569353 := by
  unfold tailWord_4793119
  simp only [CollatzResearch.WordTrace]
  refine ⟨174819411922355937398270411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116546274614903958265513607 174819411922355937398270411)
  ·
    refine ⟨262229117883533906097405617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 174819411922355937398270411 262229117883533906097405617)
    ·
      refine ⟨196671838412650429573054213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 262229117883533906097405617 196671838412650429573054213)
      ·
        refine ⟨36875969702371955544947665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 196671838412650429573054213 36875969702371955544947665)
        ·
          refine ⟨27656977276778966658710749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36875969702371955544947665 27656977276778966658710749)
          ·
            refine ⟨10371366478792112497016531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27656977276778966658710749 10371366478792112497016531)
            ·
              refine ⟨15557049718188168745524797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10371366478792112497016531 15557049718188168745524797)
              ·
                refine ⟨5833893644320563279571799, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15557049718188168745524797 5833893644320563279571799)
                ·
                  refine ⟨8750840466480844919357699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5833893644320563279571799 8750840466480844919357699)
                  ·
                    refine ⟨13126260699721267379036549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8750840466480844919357699 13126260699721267379036549)
                    ·
                      refine ⟨2461173881197737633569353, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13126260699721267379036549 2461173881197737633569353)
                      ·
                        rfl

theorem cell23_4793119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 3, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 3, 1, 3, 1, 1, 4].length) (baseStart_4793119 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4793119 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4793119 prefixEnd_4793119 := by exact prefixLift 4793119
  have htrace : WordTrace (prefixWord ++ tailWord_4793119) baseStart_4793119 baseEnd_4793119 := by
    simpa [prefixWord, tailWord_4793119, baseEnd_4793119] using wordTrace_append hprefix tailTrace_4793119
  have hstable : (prefixWord ++ tailWord_4793119).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4793119).length < 2 ^ (prefixWord ++ tailWord_4793119).sum := by decide
  have hdescent : baseEnd_4793119 < baseStart_4793119 := by decide
  rcases family_descends (prefixWord ++ tailWord_4793119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4793125 : List Nat := [1, 3, 1, 2, 3, 1, 12]
def baseStart_4793125 : Nat := 118140960795 + 4793125 * 2 ^ 59
def prefixEnd_4793125 : Nat := 4983230072969 + 3 ^ 40 * 4793125 * 2
def baseEnd_4793125 : Nat := 30384900766440303828325

theorem tailTrace_4793125 : CollatzResearch.WordTrace tailWord_4793125 prefixEnd_4793125 30384900766440303828325 := by
  unfold tailWord_4793125
  simp only [CollatzResearch.WordTrace]
  refine ⟨174819630760334200422988829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116546420506889466948659219 174819630760334200422988829)
  ·
    refine ⟨65557361535125325158620811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 174819630760334200422988829 65557361535125325158620811)
    ·
      refine ⟨98336042302687987737931217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65557361535125325158620811 98336042302687987737931217)
      ·
        refine ⟨73752031727015990803448413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 98336042302687987737931217 73752031727015990803448413)
        ·
          refine ⟨27657011897630996551293155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 73752031727015990803448413 27657011897630996551293155)
          ·
            refine ⟨41485517846446494826939733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27657011897630996551293155 41485517846446494826939733)
            ·
              refine ⟨30384900766440303828325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 12 41485517846446494826939733 30384900766440303828325)
              ·
                rfl

theorem cell23_4793125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 12].length) (baseStart_4793125 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4793125 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4793125 prefixEnd_4793125 := by exact prefixLift 4793125
  have htrace : WordTrace (prefixWord ++ tailWord_4793125) baseStart_4793125 baseEnd_4793125 := by
    simpa [prefixWord, tailWord_4793125, baseEnd_4793125] using wordTrace_append hprefix tailTrace_4793125
  have hstable : (prefixWord ++ tailWord_4793125).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4793125).length < 2 ^ (prefixWord ++ tailWord_4793125).sum := by decide
  have hdescent : baseEnd_4793125 < baseStart_4793125 := by decide
  rcases family_descends (prefixWord ++ tailWord_4793125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4793146 : List Nat := [3, 1, 1, 1, 7, 1, 1, 1, 1, 6]
def baseStart_4793146 : Nat := 118140960795 + 4793146 * 2 ^ 59
def prefixEnd_4793146 : Nat := 4983230072969 + 3 ^ 40 * 4793146 * 2
def baseEnd_4793146 : Nat := 820395915058469675977243

theorem tailTrace_4793146 : CollatzResearch.WordTrace tailWord_4793146 prefixEnd_4793146 820395915058469675977243 := by
  unfold tailWord_4793146
  simp only [CollatzResearch.WordTrace]
  refine ⟨43705099173314530252375823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 116546931128838747339668861 43705099173314530252375823)
  ·
    refine ⟨65557648759971795378563735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43705099173314530252375823 65557648759971795378563735)
    ·
      refine ⟨98336473139957693067845603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65557648759971795378563735 98336473139957693067845603)
      ·
        refine ⟨147504709709936539601768405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 98336473139957693067845603 147504709709936539601768405)
        ·
          refine ⟨3457141633826637646916447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 147504709709936539601768405 3457141633826637646916447)
          ·
            refine ⟨5185712450739956470374671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3457141633826637646916447 5185712450739956470374671)
            ·
              refine ⟨7778568676109934705562007, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5185712450739956470374671 7778568676109934705562007)
              ·
                refine ⟨11667853014164902058343011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7778568676109934705562007 11667853014164902058343011)
                ·
                  refine ⟨17501779521247353087514517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11667853014164902058343011 17501779521247353087514517)
                  ·
                    refine ⟨820395915058469675977243, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17501779521247353087514517 820395915058469675977243)
                    ·
                      rfl

theorem cell23_4793146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 7, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 7, 1, 1, 1, 1, 6].length) (baseStart_4793146 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4793146 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4793146 prefixEnd_4793146 := by exact prefixLift 4793146
  have htrace : WordTrace (prefixWord ++ tailWord_4793146) baseStart_4793146 baseEnd_4793146 := by
    simpa [prefixWord, tailWord_4793146, baseEnd_4793146] using wordTrace_append hprefix tailTrace_4793146
  have hstable : (prefixWord ++ tailWord_4793146).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4793146).length < 2 ^ (prefixWord ++ tailWord_4793146).sum := by decide
  have hdescent : baseEnd_4793146 < baseStart_4793146 := by decide
  rcases family_descends (prefixWord ++ tailWord_4793146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4793149 : List Nat := [1, 4, 1, 4, 2, 1, 1, 1, 1, 1, 6]
def baseStart_4793149 : Nat := 118140960795 + 4793149 * 2 ^ 59
def prefixEnd_4793149 : Nat := 4983230072969 + 3 ^ 40 * 4793149 * 2
def baseEnd_4793149 : Nat := 2461189285617372516194215

theorem tailTrace_4793149 : CollatzResearch.WordTrace tailWord_4793149 prefixEnd_4793149 2461189285617372516194215 := by
  unfold tailWord_4793149
  simp only [CollatzResearch.WordTrace]
  refine ⟨174820506112247252521862501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116547004074831501681241667 174820506112247252521862501)
  ·
    refine ⟨32778844896046359847849219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 174820506112247252521862501 32778844896046359847849219)
    ·
      refine ⟨49168267344069539771773829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32778844896046359847849219 49168267344069539771773829)
      ·
        refine ⟨9219050127013038707207593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 49168267344069539771773829 9219050127013038707207593)
        ·
          refine ⟨6914287595259779030405695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9219050127013038707207593 6914287595259779030405695)
          ·
            refine ⟨10371431392889668545608543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6914287595259779030405695 10371431392889668545608543)
            ·
              refine ⟨15557147089334502818412815, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10371431392889668545608543 15557147089334502818412815)
              ·
                refine ⟨23335720634001754227619223, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15557147089334502818412815 23335720634001754227619223)
                ·
                  refine ⟨35003580951002631341428835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23335720634001754227619223 35003580951002631341428835)
                  ·
                    refine ⟨52505371426503947012143253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 35003580951002631341428835 52505371426503947012143253)
                    ·
                      refine ⟨2461189285617372516194215, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 52505371426503947012143253 2461189285617372516194215)
                      ·
                        rfl

theorem cell23_4793149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 2, 1, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 2, 1, 1, 1, 1, 1, 6].length) (baseStart_4793149 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4793149 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4793149 prefixEnd_4793149 := by exact prefixLift 4793149
  have htrace : WordTrace (prefixWord ++ tailWord_4793149) baseStart_4793149 baseEnd_4793149 := by
    simpa [prefixWord, tailWord_4793149, baseEnd_4793149] using wordTrace_append hprefix tailTrace_4793149
  have hstable : (prefixWord ++ tailWord_4793149).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4793149).length < 2 ^ (prefixWord ++ tailWord_4793149).sum := by decide
  have hdescent : baseEnd_4793149 < baseStart_4793149 := by decide
  rcases family_descends (prefixWord ++ tailWord_4793149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4793153 : List Nat := [1, 2, 5, 3, 1, 1, 2, 2, 1, 1, 4]
def baseStart_4793153 : Nat := 118140960795 + 4793153 * 2 ^ 59
def prefixEnd_4793153 : Nat := 4983230072969 + 3 ^ 40 * 4793153 * 2
def baseEnd_4793153 : Nat := 2461191339539990500544197

theorem tailTrace_4793153 : CollatzResearch.WordTrace tailWord_4793153 prefixEnd_4793153 2461191339539990500544197 := by
  unfold tailWord_4793153
  simp only [CollatzResearch.WordTrace]
  refine ⟨174820652004232761205008113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116547101336155174136672075 174820652004232761205008113)
  ·
    refine ⟨131115489003174570903756085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 174820652004232761205008113 131115489003174570903756085)
    ·
      refine ⟨12292077094047616022227133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 131115489003174570903756085 12292077094047616022227133)
      ·
        refine ⟨4609528910267856008335175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12292077094047616022227133 4609528910267856008335175)
        ·
          refine ⟨6914293365401784012502763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4609528910267856008335175 6914293365401784012502763)
          ·
            refine ⟨10371440048102676018754145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6914293365401784012502763 10371440048102676018754145)
            ·
              refine ⟨7778580036077007014065609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10371440048102676018754145 7778580036077007014065609)
              ·
                refine ⟨5833935027057755260549207, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7778580036077007014065609 5833935027057755260549207)
                ·
                  refine ⟨8750902540586632890823811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5833935027057755260549207 8750902540586632890823811)
                  ·
                    refine ⟨13126353810879949336235717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8750902540586632890823811 13126353810879949336235717)
                    ·
                      refine ⟨2461191339539990500544197, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13126353810879949336235717 2461191339539990500544197)
                      ·
                        rfl

theorem cell23_4793153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 1, 1, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 1, 1, 2, 2, 1, 1, 4].length) (baseStart_4793153 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4793153 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4793153 prefixEnd_4793153 := by exact prefixLift 4793153
  have htrace : WordTrace (prefixWord ++ tailWord_4793153) baseStart_4793153 baseEnd_4793153 := by
    simpa [prefixWord, tailWord_4793153, baseEnd_4793153] using wordTrace_append hprefix tailTrace_4793153
  have hstable : (prefixWord ++ tailWord_4793153).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4793153).length < 2 ^ (prefixWord ++ tailWord_4793153).sum := by decide
  have hdescent : baseEnd_4793153 < baseStart_4793153 := by decide
  rcases family_descends (prefixWord ++ tailWord_4793153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4793202 : List Nat := [3, 2, 1, 2, 1, 1, 2, 3, 2, 6]
def baseStart_4793202 : Nat := 118140960795 + 4793202 * 2 ^ 59
def prefixEnd_4793202 : Nat := 4983230072969 + 3 ^ 40 * 4793202 * 2
def baseEnd_4793202 : Nat := 820405500030686936277157

theorem tailTrace_4793202 : CollatzResearch.WordTrace tailWord_4793202 prefixEnd_4793202 820405500030686936277157 := by
  unfold tailWord_4793202
  simp only [CollatzResearch.WordTrace]
  refine ⟨43705609795263810643385465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 116548292787370161715694573 43705609795263810643385465)
  ·
    refine ⟨32779207346447857982539099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43705609795263810643385465 32779207346447857982539099)
    ·
      refine ⟨49168811019671786973808649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32779207346447857982539099 49168811019671786973808649)
      ·
        refine ⟨36876608264753840230356487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49168811019671786973808649 36876608264753840230356487)
        ·
          refine ⟨55314912397130760345534731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36876608264753840230356487 55314912397130760345534731)
          ·
            refine ⟨82972368595696140518302097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55314912397130760345534731 82972368595696140518302097)
            ·
              refine ⟨62229276446772105388726573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 82972368595696140518302097 62229276446772105388726573)
              ·
                refine ⟨23335978667539539520772465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 62229276446772105388726573 23335978667539539520772465)
                ·
                  refine ⟨17501984000654654640579349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23335978667539539520772465 17501984000654654640579349)
                  ·
                    refine ⟨820405500030686936277157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17501984000654654640579349 820405500030686936277157)
                    ·
                      rfl

theorem cell23_4793202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 2, 3, 2, 6].length) (baseStart_4793202 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4793202 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4793202 prefixEnd_4793202 := by exact prefixLift 4793202
  have htrace : WordTrace (prefixWord ++ tailWord_4793202) baseStart_4793202 baseEnd_4793202 := by
    simpa [prefixWord, tailWord_4793202, baseEnd_4793202] using wordTrace_append hprefix tailTrace_4793202
  have hstable : (prefixWord ++ tailWord_4793202).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4793202).length < 2 ^ (prefixWord ++ tailWord_4793202).sum := by decide
  have hdescent : baseEnd_4793202 < baseStart_4793202 := by decide
  rcases family_descends (prefixWord ++ tailWord_4793202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4793226 : List Nat := [3, 1, 2, 4, 1, 1, 1, 1, 3, 4, 2]
def baseStart_4793226 : Nat := 118140960795 + 4793226 * 2 ^ 59
def prefixEnd_4793226 : Nat := 4983230072969 + 3 ^ 40 * 4793226 * 2
def baseEnd_4793226 : Nat := 2461228823627768714931361

theorem tailTrace_4793226 : CollatzResearch.WordTrace tailWord_4793226 prefixEnd_4793226 2461228823627768714931361 := by
  unfold tailWord_4793226
  simp only [CollatzResearch.WordTrace]
  refine ⟨43705828633242073668103883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 116548876355312196448277021 43705828633242073668103883)
  ·
    refine ⟨65558742949863110502155825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43705828633242073668103883 65558742949863110502155825)
    ·
      refine ⟨49169057212397332876616869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 65558742949863110502155825 49169057212397332876616869)
      ·
        refine ⟨9219198227324499914365663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 49169057212397332876616869 9219198227324499914365663)
        ·
          refine ⟨13828797340986749871548495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9219198227324499914365663 13828797340986749871548495)
          ·
            refine ⟨20743196011480124807322743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13828797340986749871548495 20743196011480124807322743)
            ·
              refine ⟨31114794017220187210984115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20743196011480124807322743 31114794017220187210984115)
              ·
                refine ⟨46672191025830280816476173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31114794017220187210984115 46672191025830280816476173)
                ·
                  refine ⟨17502071634686355306178565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 46672191025830280816476173 17502071634686355306178565)
                  ·
                    refine ⟨3281638431503691619908481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17502071634686355306178565 3281638431503691619908481)
                    ·
                      refine ⟨2461228823627768714931361, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3281638431503691619908481 2461228823627768714931361)
                      ·
                        rfl

theorem cell23_4793226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 1, 1, 3, 4, 2].length) (baseStart_4793226 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4793226 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4793226 prefixEnd_4793226 := by exact prefixLift 4793226
  have htrace : WordTrace (prefixWord ++ tailWord_4793226) baseStart_4793226 baseEnd_4793226 := by
    simpa [prefixWord, tailWord_4793226, baseEnd_4793226] using wordTrace_append hprefix tailTrace_4793226
  have hstable : (prefixWord ++ tailWord_4793226).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4793226).length < 2 ^ (prefixWord ++ tailWord_4793226).sum := by decide
  have hdescent : baseEnd_4793226 < baseStart_4793226 := by decide
  rcases family_descends (prefixWord ++ tailWord_4793226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4793393 : List Nat := [1, 2, 2, 3, 1, 2, 4, 1, 2, 3, 2]
def baseStart_4793393 : Nat := 118140960795 + 4793393 * 2 ^ 59
def prefixEnd_4793393 : Nat := 4983230072969 + 3 ^ 40 * 4793393 * 2
def baseEnd_4793393 : Nat := 2461314574897069561543093

theorem tailTrace_4793393 : CollatzResearch.WordTrace tailWord_4793393 prefixEnd_4793393 2461314574897069561543093 := by
  unfold tailWord_4793393
  simp only [CollatzResearch.WordTrace]
  refine ⟨174829405523363282193744833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116552937015575521462496555 174829405523363282193744833)
  ·
    refine ⟨131122054142522461645308625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 174829405523363282193744833 131122054142522461645308625)
    ·
      refine ⟨98341540606891846233981469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 131122054142522461645308625 98341540606891846233981469)
      ·
        refine ⟨36878077727584442337743051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 98341540606891846233981469 36878077727584442337743051)
        ·
          refine ⟨55317116591376663506614577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36878077727584442337743051 55317116591376663506614577)
          ·
            refine ⟨41487837443532497629960933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 55317116591376663506614577 41487837443532497629960933)
            ·
              refine ⟨7778969520662343305617675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 41487837443532497629960933 7778969520662343305617675)
              ·
                refine ⟨11668454280993514958426513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7778969520662343305617675 11668454280993514958426513)
                ·
                  refine ⟨8751340710745136218819885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11668454280993514958426513 8751340710745136218819885)
                  ·
                    refine ⟨3281752766529426082057457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8751340710745136218819885 3281752766529426082057457)
                    ·
                      refine ⟨2461314574897069561543093, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3281752766529426082057457 2461314574897069561543093)
                      ·
                        rfl

theorem cell23_4793393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 4, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 4, 1, 2, 3, 2].length) (baseStart_4793393 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4793393 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4793393 prefixEnd_4793393 := by exact prefixLift 4793393
  have htrace : WordTrace (prefixWord ++ tailWord_4793393) baseStart_4793393 baseEnd_4793393 := by
    simpa [prefixWord, tailWord_4793393, baseEnd_4793393] using wordTrace_append hprefix tailTrace_4793393
  have hstable : (prefixWord ++ tailWord_4793393).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4793393).length < 2 ^ (prefixWord ++ tailWord_4793393).sum := by decide
  have hdescent : baseEnd_4793393 < baseStart_4793393 := by decide
  rcases family_descends (prefixWord ++ tailWord_4793393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4793456 : List Nat := [2, 1, 1, 1, 5, 1, 1, 4, 1, 3, 3]
def baseStart_4793456 : Nat := 118140960795 + 4793456 * 2 ^ 59
def prefixEnd_4793456 : Nat := 4983230072969 + 3 ^ 40 * 4793456 * 2
def baseEnd_4793456 : Nat := 2461346924178302815055303

theorem tailTrace_4793456 : CollatzResearch.WordTrace tailWord_4793456 prefixEnd_4793456 2461346924178302815055303 := by
  unfold tailWord_4793456
  simp only [CollatzResearch.WordTrace]
  refine ⟨87415851661067521976644111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116554468881423362635525481 87415851661067521976644111)
  ·
    refine ⟨131123777491601282964966167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87415851661067521976644111 131123777491601282964966167)
    ·
      refine ⟨196685666237401924447449251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 131123777491601282964966167 196685666237401924447449251)
      ·
        refine ⟨295028499356102886671173877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 196685666237401924447449251 295028499356102886671173877)
        ·
          refine ⟨27658921814634645625422551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 295028499356102886671173877 27658921814634645625422551)
          ·
            refine ⟨41488382721951968438133827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27658921814634645625422551 41488382721951968438133827)
            ·
              refine ⟨62232574082927952657200741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41488382721951968438133827 62232574082927952657200741)
              ·
                refine ⟨11668607640548991123225139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 62232574082927952657200741 11668607640548991123225139)
                ·
                  refine ⟨17502911460823486684837709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11668607640548991123225139 17502911460823486684837709)
                  ·
                    refine ⟨6563591797808807506814141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17502911460823486684837709 6563591797808807506814141)
                    ·
                      refine ⟨2461346924178302815055303, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6563591797808807506814141 2461346924178302815055303)
                      ·
                        rfl

theorem cell23_4793456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 1, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 1, 4, 1, 3, 3].length) (baseStart_4793456 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4793456 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4793456 prefixEnd_4793456 := by exact prefixLift 4793456
  have htrace : WordTrace (prefixWord ++ tailWord_4793456) baseStart_4793456 baseEnd_4793456 := by
    simpa [prefixWord, tailWord_4793456, baseEnd_4793456] using wordTrace_append hprefix tailTrace_4793456
  have hstable : (prefixWord ++ tailWord_4793456).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4793456).length < 2 ^ (prefixWord ++ tailWord_4793456).sum := by decide
  have hdescent : baseEnd_4793456 < baseStart_4793456 := by decide
  rcases family_descends (prefixWord ++ tailWord_4793456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4793490 : List Nat := [3, 2, 3, 1, 1, 4, 1, 1, 1, 3, 3]
def baseStart_4793490 : Nat := 118140960795 + 4793490 * 2 ^ 59
def prefixEnd_4793490 : Nat := 4983230072969 + 3 ^ 40 * 4793490 * 2
def baseEnd_4793490 : Nat := 2461364382520555682030147

theorem tailTrace_4793490 : CollatzResearch.WordTrace tailWord_4793490 prefixEnd_4793490 2461364382520555682030147 := by
  unfold tailWord_4793490
  simp only [CollatzResearch.WordTrace]
  refine ⟨43708235851002966940006481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 116555295602674578506683949 43708235851002966940006481)
  ·
    refine ⟨32781176888252225205004861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43708235851002966940006481 32781176888252225205004861)
    ·
      refine ⟨12292941333094584451876823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32781176888252225205004861 12292941333094584451876823)
      ·
        refine ⟨18439411999641876677815235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12292941333094584451876823 18439411999641876677815235)
        ·
          refine ⟨27659117999462815016722853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18439411999641876677815235 27659117999462815016722853)
          ·
            refine ⟨5186084624899277815635535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 27659117999462815016722853 5186084624899277815635535)
            ·
              refine ⟨7779126937348916723453303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5186084624899277815635535 7779126937348916723453303)
              ·
                refine ⟨11668690406023375085179955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7779126937348916723453303 11668690406023375085179955)
                ·
                  refine ⟨17503035609035062627769933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11668690406023375085179955 17503035609035062627769933)
                  ·
                    refine ⟨6563638353388148485413725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17503035609035062627769933 6563638353388148485413725)
                    ·
                      refine ⟨2461364382520555682030147, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6563638353388148485413725 2461364382520555682030147)
                      ·
                        rfl

theorem cell23_4793490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 4, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 4, 1, 1, 1, 3, 3].length) (baseStart_4793490 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4793490 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4793490 prefixEnd_4793490 := by exact prefixLift 4793490
  have htrace : WordTrace (prefixWord ++ tailWord_4793490) baseStart_4793490 baseEnd_4793490 := by
    simpa [prefixWord, tailWord_4793490, baseEnd_4793490] using wordTrace_append hprefix tailTrace_4793490
  have hstable : (prefixWord ++ tailWord_4793490).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4793490).length < 2 ^ (prefixWord ++ tailWord_4793490).sum := by decide
  have hdescent : baseEnd_4793490 < baseStart_4793490 := by decide
  rcases family_descends (prefixWord ++ tailWord_4793490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4793500 : List Nat := [2, 2, 3, 2, 1, 2, 1, 4, 1, 3, 2]
def baseStart_4793500 : Nat := 118140960795 + 4793500 * 2 ^ 59
def prefixEnd_4793500 : Nat := 4983230072969 + 3 ^ 40 * 4793500 * 2
def baseEnd_4793500 : Nat := 2461369517327100642905101

theorem tailTrace_4793500 : CollatzResearch.WordTrace tailWord_4793500 prefixEnd_4793500 2461369517327100642905101 := by
  unfold tailWord_4793500
  simp only [CollatzResearch.WordTrace]
  refine ⟨87416654066987819733944977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116555538755983759645259969 87416654066987819733944977)
  ·
    refine ⟨65562490550240864800458733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 87416654066987819733944977 65562490550240864800458733)
    ·
      refine ⟨24585933956340324300172025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 65562490550240864800458733 24585933956340324300172025)
      ·
        refine ⟨18439450467255243225129019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24585933956340324300172025 18439450467255243225129019)
        ·
          refine ⟨27659175700882864837693529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18439450467255243225129019 27659175700882864837693529)
          ·
            refine ⟨20744381775662148628270147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27659175700882864837693529 20744381775662148628270147)
            ·
              refine ⟨31116572663493222942405221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20744381775662148628270147 31116572663493222942405221)
              ·
                refine ⟨5834357374404979301700979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 31116572663493222942405221 5834357374404979301700979)
                ·
                  refine ⟨8751536061607468952551469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5834357374404979301700979 8751536061607468952551469)
                  ·
                    refine ⟨3281826023102800857206801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8751536061607468952551469 3281826023102800857206801)
                    ·
                      refine ⟨2461369517327100642905101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3281826023102800857206801 2461369517327100642905101)
                      ·
                        rfl

theorem cell23_4793500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 1, 4, 1, 3, 2].length) (baseStart_4793500 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4793500 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4793500 prefixEnd_4793500 := by exact prefixLift 4793500
  have htrace : WordTrace (prefixWord ++ tailWord_4793500) baseStart_4793500 baseEnd_4793500 := by
    simpa [prefixWord, tailWord_4793500, baseEnd_4793500] using wordTrace_append hprefix tailTrace_4793500
  have hstable : (prefixWord ++ tailWord_4793500).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4793500).length < 2 ^ (prefixWord ++ tailWord_4793500).sum := by decide
  have hdescent : baseEnd_4793500 < baseStart_4793500 := by decide
  rcases family_descends (prefixWord ++ tailWord_4793500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4793519 : List Nat := [1, 1, 2, 1, 2, 3, 2, 2, 9]
def baseStart_4793519 : Nat := 118140960795 + 4793519 * 2 ^ 59
def prefixEnd_4793519 : Nat := 4983230072969 + 3 ^ 40 * 4793519 * 2
def baseEnd_4793519 : Nat := 273486585939948452063057

theorem tailTrace_4793519 : CollatzResearch.WordTrace tailWord_4793519 prefixEnd_4793519 273486585939948452063057 := by
  unfold tailWord_4793519
  simp only [CollatzResearch.WordTrace]
  refine ⟨174834001120906805712831611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116556000747271203808554407 174834001120906805712831611)
  ·
    refine ⟨262251001681360208569247417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 174834001120906805712831611 262251001681360208569247417)
    ·
      refine ⟨196688251261020156426935563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 262251001681360208569247417 196688251261020156426935563)
      ·
        refine ⟨295032376891530234640403345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 196688251261020156426935563 295032376891530234640403345)
        ·
          refine ⟨221274282668647675980302509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 295032376891530234640403345 221274282668647675980302509)
          ·
            refine ⟨82977856000742878492613441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 221274282668647675980302509 82977856000742878492613441)
            ·
              refine ⟨62233392000557158869460081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 82977856000742878492613441 62233392000557158869460081)
              ·
                refine ⟨46675044000417869152095061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 62233392000557158869460081 46675044000417869152095061)
                ·
                  refine ⟨273486585939948452063057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 46675044000417869152095061 273486585939948452063057)
                  ·
                    rfl

theorem cell23_4793519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 2, 2, 9].length) (baseStart_4793519 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4793519 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4793519 prefixEnd_4793519 := by exact prefixLift 4793519
  have htrace : WordTrace (prefixWord ++ tailWord_4793519) baseStart_4793519 baseEnd_4793519 := by
    simpa [prefixWord, tailWord_4793519, baseEnd_4793519] using wordTrace_append hprefix tailTrace_4793519
  have hstable : (prefixWord ++ tailWord_4793519).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4793519).length < 2 ^ (prefixWord ++ tailWord_4793519).sum := by decide
  have hdescent : baseEnd_4793519 < baseStart_4793519 := by decide
  rcases family_descends (prefixWord ++ tailWord_4793519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4793530 : List Nat := [3, 1, 1, 1, 2, 2, 1, 6, 2, 2, 2]
def baseStart_4793530 : Nat := 118140960795 + 4793530 * 2 ^ 59
def prefixEnd_4793530 : Nat := 4983230072969 + 3 ^ 40 * 4793530 * 2
def baseEnd_4793530 : Nat := 2461384921746735525529963

theorem tailTrace_4793530 : CollatzResearch.WordTrace tailWord_4793530 prefixEnd_4793530 2461384921746735525529963 := by
  unfold tailWord_4793530
  simp only [CollatzResearch.WordTrace]
  refine ⟨43708600580966738647870511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 116556268215911303060988029 43708600580966738647870511)
  ·
    refine ⟨65562900871450107971805767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43708600580966738647870511 65562900871450107971805767)
    ·
      refine ⟨98344351307175161957708651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65562900871450107971805767 98344351307175161957708651)
      ·
        refine ⟨147516526960762742936562977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 98344351307175161957708651 147516526960762742936562977)
        ·
          refine ⟨110637395220572057202422233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 147516526960762742936562977 110637395220572057202422233)
          ·
            refine ⟨82978046415429042901816675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 110637395220572057202422233 82978046415429042901816675)
            ·
              refine ⟨124467069623143564352725013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 82978046415429042901816675 124467069623143564352725013)
              ·
                refine ⟨5834393888584854579033985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 124467069623143564352725013 5834393888584854579033985)
                ·
                  refine ⟨4375795416438640934275489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5834393888584854579033985 4375795416438640934275489)
                  ·
                    refine ⟨3281846562328980700706617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4375795416438640934275489 3281846562328980700706617)
                    ·
                      refine ⟨2461384921746735525529963, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3281846562328980700706617 2461384921746735525529963)
                      ·
                        rfl

theorem cell23_4793530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 1, 6, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 1, 6, 2, 2, 2].length) (baseStart_4793530 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4793530 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4793530 prefixEnd_4793530 := by exact prefixLift 4793530
  have htrace : WordTrace (prefixWord ++ tailWord_4793530) baseStart_4793530 baseEnd_4793530 := by
    simpa [prefixWord, tailWord_4793530, baseEnd_4793530] using wordTrace_append hprefix tailTrace_4793530
  have hstable : (prefixWord ++ tailWord_4793530).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4793530).length < 2 ^ (prefixWord ++ tailWord_4793530).sum := by decide
  have hdescent : baseEnd_4793530 < baseStart_4793530 := by decide
  rcases family_descends (prefixWord ++ tailWord_4793530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4793539 : List Nat := [1, 1, 1, 3, 1, 1, 1, 3, 2, 1, 8]
def baseStart_4793539 : Nat := 118140960795 + 4793539 * 2 ^ 59
def prefixEnd_4793539 : Nat := 4983230072969 + 3 ^ 40 * 4793539 * 2
def baseEnd_4793539 : Nat := 2461389543072625990317421

theorem tailTrace_4793539 : CollatzResearch.WordTrace tailWord_4793539 prefixEnd_4793539 2461389543072625990317421 := by
  unfold tailWord_4793539
  simp only [CollatzResearch.WordTrace]
  refine ⟨174834730580834349128559671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116556487053889566085706447 174834730580834349128559671)
  ·
    refine ⟨262252095871251523692839507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 174834730580834349128559671 262252095871251523692839507)
    ·
      refine ⟨393378143806877285539259261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 262252095871251523692839507 393378143806877285539259261)
      ·
        refine ⟨147516803927578982077222223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 393378143806877285539259261 147516803927578982077222223)
        ·
          refine ⟨221275205891368473115833335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 147516803927578982077222223 221275205891368473115833335)
          ·
            refine ⟨331912808837052709673750003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 221275205891368473115833335 331912808837052709673750003)
            ·
              refine ⟨497869213255579064510625005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 331912808837052709673750003 497869213255579064510625005)
              ·
                refine ⟨186700954970842149191484377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 497869213255579064510625005 186700954970842149191484377)
                ·
                  refine ⟨140025716228131611893613283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 186700954970842149191484377 140025716228131611893613283)
                  ·
                    refine ⟨210038574342197417840419925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 140025716228131611893613283 210038574342197417840419925)
                    ·
                      refine ⟨2461389543072625990317421, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 210038574342197417840419925 2461389543072625990317421)
                      ·
                        rfl

theorem cell23_4793539_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 3, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 3, 2, 1, 8].length) (baseStart_4793539 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4793539 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4793539 prefixEnd_4793539 := by exact prefixLift 4793539
  have htrace : WordTrace (prefixWord ++ tailWord_4793539) baseStart_4793539 baseEnd_4793539 := by
    simpa [prefixWord, tailWord_4793539, baseEnd_4793539] using wordTrace_append hprefix tailTrace_4793539
  have hstable : (prefixWord ++ tailWord_4793539).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4793539).length < 2 ^ (prefixWord ++ tailWord_4793539).sum := by decide
  have hdescent : baseEnd_4793539 < baseStart_4793539 := by decide
  rcases family_descends (prefixWord ++ tailWord_4793539) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4793576 : List Nat := [2, 1, 4, 1, 2, 1, 1, 1, 3, 2, 5]
def baseStart_4793576 : Nat := 118140960795 + 4793576 * 2 ^ 59
def prefixEnd_4793576 : Nat := 4983230072969 + 3 ^ 40 * 4793576 * 2
def baseEnd_4793576 : Nat := 2461408541856842345554751

theorem tailTrace_4793576 : CollatzResearch.WordTrace tailWord_4793576 prefixEnd_4793576 2461408541856842345554751 := by
  unfold tailWord_4793576
  simp only [CollatzResearch.WordTrace]
  refine ⟨87418040040850152223828291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116557386721133536298437721 87418040040850152223828291)
  ·
    refine ⟨131127060061275228335742437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87418040040850152223828291 131127060061275228335742437)
    ·
      refine ⟨24586323761489105312951707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 131127060061275228335742437 24586323761489105312951707)
      ·
        refine ⟨36879485642233657969427561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24586323761489105312951707 36879485642233657969427561)
        ·
          refine ⟨27659614231675243477070671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36879485642233657969427561 27659614231675243477070671)
          ·
            refine ⟨41489421347512865215606007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27659614231675243477070671 41489421347512865215606007)
            ·
              refine ⟨62234132021269297823409011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41489421347512865215606007 62234132021269297823409011)
              ·
                refine ⟨93351198031903946735113517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 62234132021269297823409011 93351198031903946735113517)
                ·
                  refine ⟨35006699261963980025667569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 93351198031903946735113517 35006699261963980025667569)
                  ·
                    refine ⟨26255024446472985019250677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 35006699261963980025667569 26255024446472985019250677)
                    ·
                      refine ⟨2461408541856842345554751, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26255024446472985019250677 2461408541856842345554751)
                      ·
                        rfl

theorem cell23_4793576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 1, 1, 3, 2, 5].length) (baseStart_4793576 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4793576 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4793576 prefixEnd_4793576 := by exact prefixLift 4793576
  have htrace : WordTrace (prefixWord ++ tailWord_4793576) baseStart_4793576 baseEnd_4793576 := by
    simpa [prefixWord, tailWord_4793576, baseEnd_4793576] using wordTrace_append hprefix tailTrace_4793576
  have hstable : (prefixWord ++ tailWord_4793576).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4793576).length < 2 ^ (prefixWord ++ tailWord_4793576).sum := by decide
  have hdescent : baseEnd_4793576 < baseStart_4793576 := by decide
  rcases family_descends (prefixWord ++ tailWord_4793576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4793603 : List Nat := [1, 1, 1, 3, 2, 4, 1, 1, 1, 6, 2]
def baseStart_4793603 : Nat := 118140960795 + 4793603 * 2 ^ 59
def prefixEnd_4793603 : Nat := 4983230072969 + 3 ^ 40 * 4793603 * 2
def baseEnd_4793603 : Nat := 2461422405834513739917127

theorem tailTrace_4793603 : CollatzResearch.WordTrace tailWord_4793603 prefixEnd_4793603 2461422405834513739917127 := by
  unfold tailWord_4793603
  simp only [CollatzResearch.WordTrace]
  refine ⟨174837064852602488058889463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116558043235068325372592975 174837064852602488058889463)
  ·
    refine ⟨262255597278903732088334195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 174837064852602488058889463 262255597278903732088334195)
    ·
      refine ⟨393383395918355598132501293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 262255597278903732088334195 393383395918355598132501293)
      ·
        refine ⟨147518773469383349299687985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 393383395918355598132501293 147518773469383349299687985)
        ·
          refine ⟨110639080102037511974765989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 147518773469383349299687985 110639080102037511974765989)
          ·
            refine ⟨20744827519132033495268623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 110639080102037511974765989 20744827519132033495268623)
            ·
              refine ⟨31117241278698050242902935, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20744827519132033495268623 31117241278698050242902935)
              ·
                refine ⟨46675861918047075364354403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31117241278698050242902935 46675861918047075364354403)
                ·
                  refine ⟨70013792877070613046531605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 46675861918047075364354403 70013792877070613046531605)
                  ·
                    refine ⟨3281896541112684986556169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 70013792877070613046531605 3281896541112684986556169)
                    ·
                      refine ⟨2461422405834513739917127, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3281896541112684986556169 2461422405834513739917127)
                      ·
                        rfl

theorem cell23_4793603_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 1, 1, 1, 6, 2].length) (baseStart_4793603 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4793603 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4793603 prefixEnd_4793603 := by exact prefixLift 4793603
  have htrace : WordTrace (prefixWord ++ tailWord_4793603) baseStart_4793603 baseEnd_4793603 := by
    simpa [prefixWord, tailWord_4793603, baseEnd_4793603] using wordTrace_append hprefix tailTrace_4793603
  have hstable : (prefixWord ++ tailWord_4793603).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4793603).length < 2 ^ (prefixWord ++ tailWord_4793603).sum := by decide
  have hdescent : baseEnd_4793603 < baseStart_4793603 := by decide
  rcases family_descends (prefixWord ++ tailWord_4793603) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4793623 : List Nat := [1, 1, 3, 4, 1, 1, 3, 1, 1, 4, 3]
def baseStart_4793623 : Nat := 118140960795 + 4793623 * 2 ^ 59
def prefixEnd_4793623 : Nat := 4983230072969 + 3 ^ 40 * 4793623 * 2
def baseEnd_4793623 : Nat := 2461432675447603661667035

theorem tailTrace_4793623 : CollatzResearch.WordTrace tailWord_4793623 prefixEnd_4793623 2461432675447603661667035 := by
  unfold tailWord_4793623
  simp only [CollatzResearch.WordTrace]
  refine ⟨174837794312530031474617523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116558529541686687649745015 174837794312530031474617523)
  ·
    refine ⟨262256691468795047211926285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 174837794312530031474617523 262256691468795047211926285)
    ·
      refine ⟨98346259300798142704472357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 262256691468795047211926285 98346259300798142704472357)
      ·
        refine ⟨18439923618899651757088567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 98346259300798142704472357 18439923618899651757088567)
        ·
          refine ⟨27659885428349477635632851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18439923618899651757088567 27659885428349477635632851)
          ·
            refine ⟨41489828142524216453449277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27659885428349477635632851 41489828142524216453449277)
            ·
              refine ⟨15558685553446581170043479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 41489828142524216453449277 15558685553446581170043479)
              ·
                refine ⟨23338028330169871755065219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15558685553446581170043479 23338028330169871755065219)
                ·
                  refine ⟨35007042495254807632597829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23338028330169871755065219 35007042495254807632597829)
                  ·
                    refine ⟨6563820467860276431112093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 35007042495254807632597829 6563820467860276431112093)
                    ·
                      refine ⟨2461432675447603661667035, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6563820467860276431112093 2461432675447603661667035)
                      ·
                        rfl

theorem cell23_4793623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 3, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 3, 1, 1, 4, 3].length) (baseStart_4793623 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4793623 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4793623 prefixEnd_4793623 := by exact prefixLift 4793623
  have htrace : WordTrace (prefixWord ++ tailWord_4793623) baseStart_4793623 baseEnd_4793623 := by
    simpa [prefixWord, tailWord_4793623, baseEnd_4793623] using wordTrace_append hprefix tailTrace_4793623
  have hstable : (prefixWord ++ tailWord_4793623).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4793623).length < 2 ^ (prefixWord ++ tailWord_4793623).sum := by decide
  have hdescent : baseEnd_4793623 < baseStart_4793623 := by decide
  rcases family_descends (prefixWord ++ tailWord_4793623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4793660 : List Nat := [2, 2, 2, 2, 1, 4, 3, 1, 6]
def baseStart_4793660 : Nat := 118140960795 + 4793660 * 2 ^ 59
def prefixEnd_4793660 : Nat := 4983230072969 + 3 ^ 40 * 4793660 * 2
def baseEnd_4793660 : Nat := 273494630470202224100485

theorem tailTrace_4793660 : CollatzResearch.WordTrace tailWord_4793660 prefixEnd_4793660 273494630470202224100485 := by
  unfold tailWord_4793660
  simp only [CollatzResearch.WordTrace]
  refine ⟨87419571906697993396857217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116559429208930657862476289 87419571906697993396857217)
  ·
    refine ⟨65564678930023495047642913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 87419571906697993396857217 65564678930023495047642913)
    ·
      refine ⟨49173509197517621285732185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 65564678930023495047642913 49173509197517621285732185)
      ·
        refine ⟨36880131898138215964299139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49173509197517621285732185 36880131898138215964299139)
        ·
          refine ⟨55320197847207323946448709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36880131898138215964299139 55320197847207323946448709)
          ·
            refine ⟨10372537096351373239959133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 55320197847207323946448709 10372537096351373239959133)
            ·
              refine ⟨3889701411131764964984675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10372537096351373239959133 3889701411131764964984675)
              ·
                refine ⟨5834552116697647447477013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3889701411131764964984675 5834552116697647447477013)
                ·
                  refine ⟨273494630470202224100485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5834552116697647447477013 273494630470202224100485)
                  ·
                    rfl

theorem cell23_4793660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 4, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 4, 3, 1, 6].length) (baseStart_4793660 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4793660 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4793660 prefixEnd_4793660 := by exact prefixLift 4793660
  have htrace : WordTrace (prefixWord ++ tailWord_4793660) baseStart_4793660 baseEnd_4793660 := by
    simpa [prefixWord, tailWord_4793660, baseEnd_4793660] using wordTrace_append hprefix tailTrace_4793660
  have hstable : (prefixWord ++ tailWord_4793660).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4793660).length < 2 ^ (prefixWord ++ tailWord_4793660).sum := by decide
  have hdescent : baseEnd_4793660 < baseStart_4793660 := by decide
  rcases family_descends (prefixWord ++ tailWord_4793660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4793673 : List Nat := [1, 2, 1, 1, 2, 3, 3, 4, 1, 5]
def baseStart_4793673 : Nat := 118140960795 + 4793673 * 2 ^ 59
def prefixEnd_4793673 : Nat := 4983230072969 + 3 ^ 40 * 4793673 * 2
def baseEnd_4793673 : Nat := 820486116493442822013935

theorem tailTrace_4793673 : CollatzResearch.WordTrace tailWord_4793673 prefixEnd_4793673 820486116493442822013935 := by
  unfold tailWord_4793673
  simp only [CollatzResearch.WordTrace]
  refine ⟨174839617962348890013937673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116559745308232593342625115 174839617962348890013937673)
  ·
    refine ⟨131129713471761667510453255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 174839617962348890013937673 131129713471761667510453255)
    ·
      refine ⟨196694570207642501265679883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 131129713471761667510453255 196694570207642501265679883)
      ·
        refine ⟨295041855311463751898519825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 196694570207642501265679883 295041855311463751898519825)
        ·
          refine ⟨221281391483597813923889869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 295041855311463751898519825 221281391483597813923889869)
          ·
            refine ⟨82980521806349180221458701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 221281391483597813923889869 82980521806349180221458701)
            ·
              refine ⟨31117695677380942583047013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 82980521806349180221458701 31117695677380942583047013)
              ·
                refine ⟨5834567939508926734321315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 31117695677380942583047013 5834567939508926734321315)
                ·
                  refine ⟨8751851909263390101481973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5834567939508926734321315 8751851909263390101481973)
                  ·
                    refine ⟨820486116493442822013935, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8751851909263390101481973 820486116493442822013935)
                    ·
                      rfl

theorem cell23_4793673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 3, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 3, 4, 1, 5].length) (baseStart_4793673 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4793673 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4793673 prefixEnd_4793673 := by exact prefixLift 4793673
  have htrace : WordTrace (prefixWord ++ tailWord_4793673) baseStart_4793673 baseEnd_4793673 := by
    simpa [prefixWord, tailWord_4793673, baseEnd_4793673] using wordTrace_append hprefix tailTrace_4793673
  have hstable : (prefixWord ++ tailWord_4793673).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4793673).length < 2 ^ (prefixWord ++ tailWord_4793673).sum := by decide
  have hdescent : baseEnd_4793673 < baseStart_4793673 := by decide
  rcases family_descends (prefixWord ++ tailWord_4793673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4793680 : List Nat := [2, 1, 1, 1, 1, 5, 2, 3, 2, 3, 2]
def baseStart_4793680 : Nat := 118140960795 + 4793680 * 2 ^ 59
def prefixEnd_4793680 : Nat := 4983230072969 + 3 ^ 40 * 4793680 * 2
def baseEnd_4793680 : Nat := 2461461943844909938654273

theorem tailTrace_4793680 : CollatzResearch.WordTrace tailWord_4793680 prefixEnd_4793680 2461461943844909938654273 := by
  unfold tailWord_4793680
  simp only [CollatzResearch.WordTrace]
  refine ⟨87419936636661765104721247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116559915515549020139628329 87419936636661765104721247)
  ·
    refine ⟨131129904954992647657081871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87419936636661765104721247 131129904954992647657081871)
    ·
      refine ⟨196694857432488971485622807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 131129904954992647657081871 196694857432488971485622807)
      ·
        refine ⟨295042286148733457228434211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 196694857432488971485622807 295042286148733457228434211)
        ·
          refine ⟨442563429223100185842651317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 295042286148733457228434211 442563429223100185842651317)
          ·
            refine ⟨41490321489665642422748561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 442563429223100185842651317 41490321489665642422748561)
            ·
              refine ⟨31117741117249231817061421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 41490321489665642422748561 31117741117249231817061421)
              ·
                refine ⟨11669152918968461931398033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 31117741117249231817061421 11669152918968461931398033)
                ·
                  refine ⟨8751864689226346448548525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11669152918968461931398033 8751864689226346448548525)
                  ·
                    refine ⟨3281949258459879918205697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8751864689226346448548525 3281949258459879918205697)
                    ·
                      refine ⟨2461461943844909938654273, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3281949258459879918205697 2461461943844909938654273)
                      ·
                        rfl

theorem cell23_4793680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 2, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 2, 3, 2, 3, 2].length) (baseStart_4793680 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4793680 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4793680 prefixEnd_4793680 := by exact prefixLift 4793680
  have htrace : WordTrace (prefixWord ++ tailWord_4793680) baseStart_4793680 baseEnd_4793680 := by
    simpa [prefixWord, tailWord_4793680, baseEnd_4793680] using wordTrace_append hprefix tailTrace_4793680
  have hstable : (prefixWord ++ tailWord_4793680).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4793680).length < 2 ^ (prefixWord ++ tailWord_4793680).sum := by decide
  have hdescent : baseEnd_4793680 < baseStart_4793680 := by decide
  rcases family_descends (prefixWord ++ tailWord_4793680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4793704 : List Nat := [2, 1, 4, 2, 3, 2, 1, 1, 3, 1, 3]
def baseStart_4793704 : Nat := 118140960795 + 4793704 * 2 ^ 59
def prefixEnd_4793704 : Nat := 4983230072969 + 3 ^ 40 * 4793704 * 2
def baseEnd_4793704 : Nat := 2461474267380617844754163

theorem tailTrace_4793704 : CollatzResearch.WordTrace tailWord_4793704 prefixEnd_4793704 2461474267380617844754163 := by
  unfold tailWord_4793704
  simp only [CollatzResearch.WordTrace]
  refine ⟨87420374312618291154158083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116560499083491054872210777 87420374312618291154158083)
  ·
    refine ⟨131130561468927436731237125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87420374312618291154158083 131130561468927436731237125)
    ·
      refine ⟨24586980275423894387106961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 131130561468927436731237125 24586980275423894387106961)
      ·
        refine ⟨18440235206567920790330221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24586980275423894387106961 18440235206567920790330221)
        ·
          refine ⟨6915088202462970296373833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18440235206567920790330221 6915088202462970296373833)
          ·
            refine ⟨5186316151847227722280375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6915088202462970296373833 5186316151847227722280375)
            ·
              refine ⟨7779474227770841583420563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5186316151847227722280375 7779474227770841583420563)
              ·
                refine ⟨11669211341656262375130845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7779474227770841583420563 11669211341656262375130845)
                ·
                  refine ⟨4375954253121098390674067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11669211341656262375130845 4375954253121098390674067)
                  ·
                    refine ⟨6563931379681647586011101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4375954253121098390674067 6563931379681647586011101)
                    ·
                      refine ⟨2461474267380617844754163, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6563931379681647586011101 2461474267380617844754163)
                      ·
                        rfl

theorem cell23_4793704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 3, 2, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 3, 2, 1, 1, 3, 1, 3].length) (baseStart_4793704 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4793704 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4793704 prefixEnd_4793704 := by exact prefixLift 4793704
  have htrace : WordTrace (prefixWord ++ tailWord_4793704) baseStart_4793704 baseEnd_4793704 := by
    simpa [prefixWord, tailWord_4793704, baseEnd_4793704] using wordTrace_append hprefix tailTrace_4793704
  have hstable : (prefixWord ++ tailWord_4793704).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4793704).length < 2 ^ (prefixWord ++ tailWord_4793704).sum := by decide
  have hdescent : baseEnd_4793704 < baseStart_4793704 := by decide
  rcases family_descends (prefixWord ++ tailWord_4793704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4793713 : List Nat := [1, 2, 2, 2, 1, 2, 4, 2, 1, 1, 5]
def baseStart_4793713 : Nat := 118140960795 + 4793713 * 2 ^ 59
def prefixEnd_4793713 : Nat := 4983230072969 + 3 ^ 40 * 4793713 * 2
def baseEnd_4793713 : Nat := 2461478888706508309541621

theorem tailTrace_4793713 : CollatzResearch.WordTrace tailWord_4793713 prefixEnd_4793713 2461478888706508309541621 := by
  unfold tailWord_4793713
  simp only [CollatzResearch.WordTrace]
  refine ⟨174841076882203976845393793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116560717921469317896929195 174841076882203976845393793)
  ·
    refine ⟨131130807661652982634045345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 174841076882203976845393793 131130807661652982634045345)
    ·
      refine ⟨98348105746239736975534009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 131130807661652982634045345 98348105746239736975534009)
      ·
        refine ⟨73761079309679802731650507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 98348105746239736975534009 73761079309679802731650507)
        ·
          refine ⟨110641618964519704097475761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 73761079309679802731650507 110641618964519704097475761)
          ·
            refine ⟨82981214223389778073106821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 110641618964519704097475761 82981214223389778073106821)
            ·
              refine ⟨15558977666885583388707529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 82981214223389778073106821 15558977666885583388707529)
              ·
                refine ⟨11669233250164187541530647, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15558977666885583388707529 11669233250164187541530647)
                ·
                  refine ⟨17503849875246281312295971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11669233250164187541530647 17503849875246281312295971)
                  ·
                    refine ⟨26255774812869421968443957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17503849875246281312295971 26255774812869421968443957)
                    ·
                      refine ⟨2461478888706508309541621, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26255774812869421968443957 2461478888706508309541621)
                      ·
                        rfl

theorem cell23_4793713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 4, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 4, 2, 1, 1, 5].length) (baseStart_4793713 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4793713 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4793713 prefixEnd_4793713 := by exact prefixLift 4793713
  have htrace : WordTrace (prefixWord ++ tailWord_4793713) baseStart_4793713 baseEnd_4793713 := by
    simpa [prefixWord, tailWord_4793713, baseEnd_4793713] using wordTrace_append hprefix tailTrace_4793713
  have hstable : (prefixWord ++ tailWord_4793713).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4793713).length < 2 ^ (prefixWord ++ tailWord_4793713).sum := by decide
  have hdescent : baseEnd_4793713 < baseStart_4793713 := by decide
  rcases family_descends (prefixWord ++ tailWord_4793713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4793723 : List Nat := [1, 1, 1, 1, 1, 6, 2, 3, 1, 2, 4]
def baseStart_4793723 : Nat := 118140960795 + 4793723 * 2 ^ 59
def prefixEnd_4793723 : Nat := 4983230072969 + 3 ^ 40 * 4793723 * 2
def baseEnd_4793723 : Nat := 2461484023513053270416575

theorem tailTrace_4793723 : CollatzResearch.WordTrace tailWord_4793723 prefixEnd_4793723 2461484023513053270416575 := by
  unfold tailWord_4793723
  simp only [CollatzResearch.WordTrace]
  refine ⟨174841441612167748553257823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116560961074778499035505215 174841441612167748553257823)
  ·
    refine ⟨262262162418251622829886735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 174841441612167748553257823 262262162418251622829886735)
    ·
      refine ⟨393393243627377434244830103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 262262162418251622829886735 393393243627377434244830103)
      ·
        refine ⟨590089865441066151367245155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 393393243627377434244830103 590089865441066151367245155)
        ·
          refine ⟨885134798161599227050867733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 590089865441066151367245155 885134798161599227050867733)
          ·
            refine ⟨41490693663824963768009425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 885134798161599227050867733 41490693663824963768009425)
            ·
              refine ⟨31118020247868722826007069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 41490693663824963768009425 31118020247868722826007069)
              ·
                refine ⟨11669257592950771059752651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 31118020247868722826007069 11669257592950771059752651)
                ·
                  refine ⟨17503886389426156589628977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11669257592950771059752651 17503886389426156589628977)
                  ·
                    refine ⟨13127914792069617442221733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17503886389426156589628977 13127914792069617442221733)
                    ·
                      refine ⟨2461484023513053270416575, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13127914792069617442221733 2461484023513053270416575)
                      ·
                        rfl

theorem cell23_4793723_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 2, 3, 1, 2, 4].length) (baseStart_4793723 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4793723 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4793723 prefixEnd_4793723 := by exact prefixLift 4793723
  have htrace : WordTrace (prefixWord ++ tailWord_4793723) baseStart_4793723 baseEnd_4793723 := by
    simpa [prefixWord, tailWord_4793723, baseEnd_4793723] using wordTrace_append hprefix tailTrace_4793723
  have hstable : (prefixWord ++ tailWord_4793723).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4793723).length < 2 ^ (prefixWord ++ tailWord_4793723).sum := by decide
  have hdescent : baseEnd_4793723 < baseStart_4793723 := by decide
  rcases family_descends (prefixWord ++ tailWord_4793723) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4793750 : List Nat := [5, 3, 1, 14]
def baseStart_4793750 : Nat := 118140960795 + 4793750 * 2 ^ 59
def prefixEnd_4793750 : Nat := 4983230072969 + 3 ^ 40 * 4793750 * 2
def baseEnd_4793750 : Nat := 1125513437352869073973

theorem tailTrace_4793750 : CollatzResearch.WordTrace tailWord_4793750 prefixEnd_4793750 1125513437352869073973 := by
  unfold tailWord_4793750
  simp only [CollatzResearch.WordTrace]
  refine ⟨10927651648941870760280669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 116561617588713288109660469 10927651648941870760280669)
  ·
    refine ⟨4097869368353201535105251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10927651648941870760280669 4097869368353201535105251)
    ·
      refine ⟨6146804052529802302657877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4097869368353201535105251 6146804052529802302657877)
      ·
        refine ⟨1125513437352869073973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 14 6146804052529802302657877 1125513437352869073973)
        ·
          rfl

theorem cell23_4793750_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 14].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 14].length) (baseStart_4793750 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4793750 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4793750 prefixEnd_4793750 := by exact prefixLift 4793750
  have htrace : WordTrace (prefixWord ++ tailWord_4793750) baseStart_4793750 baseEnd_4793750 := by
    simpa [prefixWord, tailWord_4793750, baseEnd_4793750] using wordTrace_append hprefix tailTrace_4793750
  have hstable : (prefixWord ++ tailWord_4793750).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4793750).length < 2 ^ (prefixWord ++ tailWord_4793750).sum := by decide
  have hdescent : baseEnd_4793750 < baseStart_4793750 := by decide
  rcases family_descends (prefixWord ++ tailWord_4793750) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4793777 : List Nat := [1, 2, 2, 4, 1, 1, 1, 5, 2, 1, 3]
def baseStart_4793777 : Nat := 118140960795 + 4793777 * 2 ^ 59
def prefixEnd_4793777 : Nat := 4983230072969 + 3 ^ 40 * 4793777 * 2
def baseEnd_4793777 : Nat := 2461511751468396059141327

theorem tailTrace_4793777 : CollatzResearch.WordTrace tailWord_4793777 prefixEnd_4793777 2461511751468396059141327 := by
  unfold tailWord_4793777
  simp only [CollatzResearch.WordTrace]
  refine ⟨174843411153972115775723585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116562274102648077183815723 174843411153972115775723585)
  ·
    refine ⟨131132558365479086831792689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 174843411153972115775723585 131132558365479086831792689)
    ·
      refine ⟨98349418774109315123844517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 131132558365479086831792689 98349418774109315123844517)
      ·
        refine ⟨18440516020145496585720847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 98349418774109315123844517 18440516020145496585720847)
        ·
          refine ⟨27660774030218244878581271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18440516020145496585720847 27660774030218244878581271)
          ·
            refine ⟨41491161045327367317871907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27660774030218244878581271 41491161045327367317871907)
            ·
              refine ⟨62236741567991050976807861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41491161045327367317871907 62236741567991050976807861)
              ·
                refine ⟨5834694521999161029075737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 62236741567991050976807861 5834694521999161029075737)
                ·
                  refine ⟨4376020891499370771806803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5834694521999161029075737 4376020891499370771806803)
                  ·
                    refine ⟨6564031337249056157710205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4376020891499370771806803 6564031337249056157710205)
                    ·
                      refine ⟨2461511751468396059141327, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6564031337249056157710205 2461511751468396059141327)
                      ·
                        rfl

theorem cell23_4793777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 1, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 1, 5, 2, 1, 3].length) (baseStart_4793777 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4793777 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4793777 prefixEnd_4793777 := by exact prefixLift 4793777
  have htrace : WordTrace (prefixWord ++ tailWord_4793777) baseStart_4793777 baseEnd_4793777 := by
    simpa [prefixWord, tailWord_4793777, baseEnd_4793777] using wordTrace_append hprefix tailTrace_4793777
  have hstable : (prefixWord ++ tailWord_4793777).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4793777).length < 2 ^ (prefixWord ++ tailWord_4793777).sum := by decide
  have hdescent : baseEnd_4793777 < baseStart_4793777 := by decide
  rcases family_descends (prefixWord ++ tailWord_4793777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4793783 : List Nat := [1, 1, 3, 1, 3, 2, 1, 2, 2, 3, 4]
def baseStart_4793783 : Nat := 118140960795 + 4793783 * 2 ^ 59
def prefixEnd_4793783 : Nat := 4983230072969 + 3 ^ 40 * 4793783 * 2
def baseEnd_4793783 : Nat := 2461514832352323035666299

theorem tailTrace_4793783 : CollatzResearch.WordTrace tailWord_4793783 prefixEnd_4793783 2461514832352323035666299 := by
  unfold tailWord_4793783
  simp only [CollatzResearch.WordTrace]
  refine ⟨174843629991950378800442003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116562419994633585866961335 174843629991950378800442003)
  ·
    refine ⟨262265444987925568200663005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 174843629991950378800442003 262265444987925568200663005)
    ·
      refine ⟨98349541870472088075248627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 262265444987925568200663005 98349541870472088075248627)
      ·
        refine ⟨147524312805708132112872941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 98349541870472088075248627 147524312805708132112872941)
        ·
          refine ⟨55321617302140549542327353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 147524312805708132112872941 55321617302140549542327353)
          ·
            refine ⟨41491212976605412156745515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 55321617302140549542327353 41491212976605412156745515)
            ·
              refine ⟨62236819464908118235118273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41491212976605412156745515 62236819464908118235118273)
              ·
                refine ⟨46677614598681088676338705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 62236819464908118235118273 46677614598681088676338705)
                ·
                  refine ⟨35008210949010816507254029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 46677614598681088676338705 35008210949010816507254029)
                  ·
                    refine ⟨13128079105879056190220261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 35008210949010816507254029 13128079105879056190220261)
                    ·
                      refine ⟨2461514832352323035666299, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13128079105879056190220261 2461514832352323035666299)
                      ·
                        rfl

theorem cell23_4793783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 1, 2, 2, 3, 4].length) (baseStart_4793783 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4793783 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4793783 prefixEnd_4793783 := by exact prefixLift 4793783
  have htrace : WordTrace (prefixWord ++ tailWord_4793783) baseStart_4793783 baseEnd_4793783 := by
    simpa [prefixWord, tailWord_4793783, baseEnd_4793783] using wordTrace_append hprefix tailTrace_4793783
  have hstable : (prefixWord ++ tailWord_4793783).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4793783).length < 2 ^ (prefixWord ++ tailWord_4793783).sum := by decide
  have hdescent : baseEnd_4793783 < baseStart_4793783 := by decide
  rcases family_descends (prefixWord ++ tailWord_4793783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4793803 : List Nat := [1, 1, 1, 1, 3, 3, 2, 3, 2, 1, 5]
def baseStart_4793803 : Nat := 118140960795 + 4793803 * 2 ^ 59
def prefixEnd_4793803 : Nat := 4983230072969 + 3 ^ 40 * 4793803 * 2
def baseEnd_4793803 : Nat := 2461525101965412957416207

theorem tailTrace_4793803 : CollatzResearch.WordTrace tailWord_4793803 prefixEnd_4793803 2461525101965412957416207 := by
  unfold tailWord_4793803
  simp only [CollatzResearch.WordTrace]
  refine ⟨174844359451877922216170063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116562906301251948144113375 174844359451877922216170063)
  ·
    refine ⟨262266539177816883324255095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 174844359451877922216170063 262266539177816883324255095)
    ·
      refine ⟨393399808766725324986382643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 262266539177816883324255095 393399808766725324986382643)
      ·
        refine ⟨590099713150087987479573965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 393399808766725324986382643 590099713150087987479573965)
        ·
          refine ⟨221287392431282995304840237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 590099713150087987479573965 221287392431282995304840237)
          ·
            refine ⟨82982772161731123239315089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 221287392431282995304840237 82982772161731123239315089)
            ·
              refine ⟨62237079121298342429486317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 82982772161731123239315089 62237079121298342429486317)
              ·
                refine ⟨23338904670486878411057369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 62237079121298342429486317 23338904670486878411057369)
                ·
                  refine ⟨17504178502865158808293027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23338904670486878411057369 17504178502865158808293027)
                  ·
                    refine ⟨26256267754297738212439541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17504178502865158808293027 26256267754297738212439541)
                    ·
                      refine ⟨2461525101965412957416207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26256267754297738212439541 2461525101965412957416207)
                      ·
                        rfl

theorem cell23_4793803_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 2, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 2, 3, 2, 1, 5].length) (baseStart_4793803 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4793803 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4793803 prefixEnd_4793803 := by exact prefixLift 4793803
  have htrace : WordTrace (prefixWord ++ tailWord_4793803) baseStart_4793803 baseEnd_4793803 := by
    simpa [prefixWord, tailWord_4793803, baseEnd_4793803] using wordTrace_append hprefix tailTrace_4793803
  have hstable : (prefixWord ++ tailWord_4793803).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4793803).length < 2 ^ (prefixWord ++ tailWord_4793803).sum := by decide
  have hdescent : baseEnd_4793803 < baseStart_4793803 := by decide
  rcases family_descends (prefixWord ++ tailWord_4793803) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4793804 : List Nat := [2, 2, 1, 4, 2, 2, 1, 3, 1, 3, 2]
def baseStart_4793804 : Nat := 118140960795 + 4793804 * 2 ^ 59
def prefixEnd_4793804 : Nat := 4983230072969 + 3 ^ 40 * 4793804 * 2
def baseEnd_4793804 : Nat := 2461525615446067453503703

theorem tailTrace_4793804 : CollatzResearch.WordTrace tailWord_4793804 prefixEnd_4793804 2461525615446067453503703 := by
  unfold tailWord_4793804
  simp only [CollatzResearch.WordTrace]
  refine ⟨87422197962437149693478233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116562930616582866257970977 87422197962437149693478233)
  ·
    refine ⟨65566648471827862270108675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 87422197962437149693478233 65566648471827862270108675)
    ·
      refine ⟨98349972707741793405163013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65566648471827862270108675 98349972707741793405163013)
      ·
        refine ⟨18440619882701586263468065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 98349972707741793405163013 18440619882701586263468065)
        ·
          refine ⟨13830464912026189697601049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18440619882701586263468065 13830464912026189697601049)
          ·
            refine ⟨10372848684019642273200787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13830464912026189697601049 10372848684019642273200787)
            ·
              refine ⟨15559273026029463409801181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10372848684019642273200787 15559273026029463409801181)
              ·
                refine ⟨5834727384761048778675443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15559273026029463409801181 5834727384761048778675443)
                ·
                  refine ⟨8752091077141573168013165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5834727384761048778675443 8752091077141573168013165)
                  ·
                    refine ⟨3282034153928089938004937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8752091077141573168013165 3282034153928089938004937)
                    ·
                      refine ⟨2461525615446067453503703, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3282034153928089938004937 2461525615446067453503703)
                      ·
                        rfl

theorem cell23_4793804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 2, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 2, 1, 3, 1, 3, 2].length) (baseStart_4793804 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4793804 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4793804 prefixEnd_4793804 := by exact prefixLift 4793804
  have htrace : WordTrace (prefixWord ++ tailWord_4793804) baseStart_4793804 baseEnd_4793804 := by
    simpa [prefixWord, tailWord_4793804, baseEnd_4793804] using wordTrace_append hprefix tailTrace_4793804
  have hstable : (prefixWord ++ tailWord_4793804).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4793804).length < 2 ^ (prefixWord ++ tailWord_4793804).sum := by decide
  have hdescent : baseEnd_4793804 < baseStart_4793804 := by decide
  rcases family_descends (prefixWord ++ tailWord_4793804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4793854 : List Nat := [4, 2, 2, 3, 1, 1, 1, 1, 2, 1, 5]
def baseStart_4793854 : Nat := 118140960795 + 4793854 * 2 ^ 59
def prefixEnd_4793854 : Nat := 4983230072969 + 3 ^ 40 * 4793854 * 2
def baseEnd_4793854 : Nat := 2461551289478792257878473

theorem tailTrace_4793854 : CollatzResearch.WordTrace tailWord_4793854 prefixEnd_4793854 2461551289478792257878473 := by
  unfold tailWord_4793854
  simp only [CollatzResearch.WordTrace]
  refine ⟨21855777446836644740784577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 116564146383128771950851077 21855777446836644740784577)
  ·
    refine ⟨16391833085127483555588433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21855777446836644740784577 16391833085127483555588433)
    ·
      refine ⟨12293874813845612666691325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16391833085127483555588433 12293874813845612666691325)
      ·
        refine ⟨4610203055192104750009247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12293874813845612666691325 4610203055192104750009247)
        ·
          refine ⟨6915304582788157125013871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4610203055192104750009247 6915304582788157125013871)
          ·
            refine ⟨10372956874182235687520807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6915304582788157125013871 10372956874182235687520807)
            ·
              refine ⟨15559435311273353531281211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10372956874182235687520807 15559435311273353531281211)
              ·
                refine ⟨23339152966910030296921817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15559435311273353531281211 23339152966910030296921817)
                ·
                  refine ⟨17504364725182522722691363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23339152966910030296921817 17504364725182522722691363)
                  ·
                    refine ⟨26256547087773784084037045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17504364725182522722691363 26256547087773784084037045)
                    ·
                      refine ⟨2461551289478792257878473, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26256547087773784084037045 2461551289478792257878473)
                      ·
                        rfl

theorem cell23_4793854_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 1, 1, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 1, 1, 1, 1, 2, 1, 5].length) (baseStart_4793854 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4793854 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4793854 prefixEnd_4793854 := by exact prefixLift 4793854
  have htrace : WordTrace (prefixWord ++ tailWord_4793854) baseStart_4793854 baseEnd_4793854 := by
    simpa [prefixWord, tailWord_4793854, baseEnd_4793854] using wordTrace_append hprefix tailTrace_4793854
  have hstable : (prefixWord ++ tailWord_4793854).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4793854).length < 2 ^ (prefixWord ++ tailWord_4793854).sum := by decide
  have hdescent : baseEnd_4793854 < baseStart_4793854 := by decide
  rcases family_descends (prefixWord ++ tailWord_4793854) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4793890 : List Nat := [3, 3, 1, 1, 1, 1, 2, 1, 3, 3, 4]
def baseStart_4793890 : Nat := 118140960795 + 4793890 * 2 ^ 59
def prefixEnd_4793890 : Nat := 4983230072969 + 3 ^ 40 * 4793890 * 2
def baseEnd_4793890 : Nat := 2461569774782354117028307

theorem tailTrace_4793890 : CollatzResearch.WordTrace tailWord_4793890 prefixEnd_4793890 2461569774782354117028307 := by
  unfold tailWord_4793890
  simp only [CollatzResearch.WordTrace]
  refine ⟨43711883150640684018646781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 116565021735041824049724749 43711883150640684018646781)
  ·
    refine ⟨16391956181490256506992543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 43711883150640684018646781 16391956181490256506992543)
    ·
      refine ⟨24587934272235384760488815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16391956181490256506992543 24587934272235384760488815)
      ·
        refine ⟨36881901408353077140733223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24587934272235384760488815 36881901408353077140733223)
        ·
          refine ⟨55322852112529615711099835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36881901408353077140733223 55322852112529615711099835)
          ·
            refine ⟨82984278168794423566649753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55322852112529615711099835 82984278168794423566649753)
            ·
              refine ⟨62238208626595817674987315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 82984278168794423566649753 62238208626595817674987315)
              ·
                refine ⟨93357312939893726512480973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 62238208626595817674987315 93357312939893726512480973)
                ·
                  refine ⟨35008992352460147442180365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 93357312939893726512480973 35008992352460147442180365)
                  ·
                    refine ⟨13128372132172555290817637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 35008992352460147442180365 13128372132172555290817637)
                    ·
                      refine ⟨2461569774782354117028307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13128372132172555290817637 2461569774782354117028307)
                      ·
                        rfl

theorem cell23_4793890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 2, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 2, 1, 3, 3, 4].length) (baseStart_4793890 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4793890 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4793890 prefixEnd_4793890 := by exact prefixLift 4793890
  have htrace : WordTrace (prefixWord ++ tailWord_4793890) baseStart_4793890 baseEnd_4793890 := by
    simpa [prefixWord, tailWord_4793890, baseEnd_4793890] using wordTrace_append hprefix tailTrace_4793890
  have hstable : (prefixWord ++ tailWord_4793890).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4793890).length < 2 ^ (prefixWord ++ tailWord_4793890).sum := by decide
  have hdescent : baseEnd_4793890 < baseStart_4793890 := by decide
  rcases family_descends (prefixWord ++ tailWord_4793890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4793907 : List Nat := [1, 1, 1, 2, 4, 4, 2, 1, 2, 1, 4]
def baseStart_4793907 : Nat := 118140960795 + 4793907 * 2 ^ 59
def prefixEnd_4793907 : Nat := 4983230072969 + 3 ^ 40 * 4793907 * 2
def baseEnd_4793907 : Nat := 2461578503953480550515729

theorem tailTrace_4793907 : CollatzResearch.WordTrace tailWord_4793907 prefixEnd_4793907 2461578503953480550515729 := by
  unfold tailWord_4793907
  simp only [CollatzResearch.WordTrace]
  refine ⟨174848152643501147977955975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116565435095667431985303983 174848152643501147977955975)
  ·
    refine ⟨262272228965251721966933963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 174848152643501147977955975 262272228965251721966933963)
    ·
      refine ⟨393408343447877582950400945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 262272228965251721966933963 393408343447877582950400945)
      ·
        refine ⟨295056257585908187212800709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 393408343447877582950400945 295056257585908187212800709)
        ·
          refine ⟨55323048297357785102400133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 295056257585908187212800709 55323048297357785102400133)
          ·
            refine ⟨10373071555754584706700025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 55323048297357785102400133 10373071555754584706700025)
            ·
              refine ⟨7779803666815938530025019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10373071555754584706700025 7779803666815938530025019)
              ·
                refine ⟨11669705500223907795037529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7779803666815938530025019 11669705500223907795037529)
                ·
                  refine ⟨8752279125167930846278147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11669705500223907795037529 8752279125167930846278147)
                  ·
                    refine ⟨13128418687751896269417221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8752279125167930846278147 13128418687751896269417221)
                    ·
                      refine ⟨2461578503953480550515729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13128418687751896269417221 2461578503953480550515729)
                      ·
                        rfl

theorem cell23_4793907_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 4, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 4, 2, 1, 2, 1, 4].length) (baseStart_4793907 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4793907 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4793907 prefixEnd_4793907 := by exact prefixLift 4793907
  have htrace : WordTrace (prefixWord ++ tailWord_4793907) baseStart_4793907 baseEnd_4793907 := by
    simpa [prefixWord, tailWord_4793907, baseEnd_4793907] using wordTrace_append hprefix tailTrace_4793907
  have hstable : (prefixWord ++ tailWord_4793907).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4793907).length < 2 ^ (prefixWord ++ tailWord_4793907).sum := by decide
  have hdescent : baseEnd_4793907 < baseStart_4793907 := by decide
  rcases family_descends (prefixWord ++ tailWord_4793907) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4793977 : List Nat := [1, 2, 1, 3, 3, 1, 3, 3, 1, 5]
def baseStart_4793977 : Nat := 118140960795 + 4793977 * 2 ^ 59
def prefixEnd_4793977 : Nat := 4983230072969 + 3 ^ 40 * 4793977 * 2
def baseEnd_4793977 : Nat := 820538149199765092213469

theorem tailTrace_4793977 : CollatzResearch.WordTrace tailWord_4793977 prefixEnd_4793977 820538149199765092213469 := by
  unfold tailWord_4793977
  simp only [CollatzResearch.WordTrace]
  refine ⟨174850705753247549933004185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116567137168831699955336123 174850705753247549933004185)
  ·
    refine ⟨131138029314935662449753139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 174850705753247549933004185 131138029314935662449753139)
    ·
      refine ⟨196707043972403493674629709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 131138029314935662449753139 196707043972403493674629709)
      ·
        refine ⟨73765141489651310127986141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 196707043972403493674629709 73765141489651310127986141)
        ·
          refine ⟨27661928058619241297994803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 73765141489651310127986141 27661928058619241297994803)
          ·
            refine ⟨41492892087928861946992205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27661928058619241297994803 41492892087928861946992205)
            ·
              refine ⟨15559834532973323230122077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 41492892087928861946992205 15559834532973323230122077)
              ·
                refine ⟨5834937949864996211295779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15559834532973323230122077 5834937949864996211295779)
                ·
                  refine ⟨8752406924797494316943669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5834937949864996211295779 8752406924797494316943669)
                  ·
                    refine ⟨820538149199765092213469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8752406924797494316943669 820538149199765092213469)
                    ·
                      rfl

theorem cell23_4793977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 3, 3, 1, 5].length) (baseStart_4793977 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4793977 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4793977 prefixEnd_4793977 := by exact prefixLift 4793977
  have htrace : WordTrace (prefixWord ++ tailWord_4793977) baseStart_4793977 baseEnd_4793977 := by
    simpa [prefixWord, tailWord_4793977, baseEnd_4793977] using wordTrace_append hprefix tailTrace_4793977
  have hstable : (prefixWord ++ tailWord_4793977).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4793977).length < 2 ^ (prefixWord ++ tailWord_4793977).sum := by decide
  have hdescent : baseEnd_4793977 < baseStart_4793977 := by decide
  rcases family_descends (prefixWord ++ tailWord_4793977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4793991 : List Nat := [1, 1, 4, 2, 1, 3, 2, 4, 1, 1, 3]
def baseStart_4793991 : Nat := 118140960795 + 4793991 * 2 ^ 59
def prefixEnd_4793991 : Nat := 4983230072969 + 3 ^ 40 * 4793991 * 2
def baseEnd_4793991 : Nat := 2461621636328458221865343

theorem tailTrace_4793991 : CollatzResearch.WordTrace tailWord_4793991 prefixEnd_4793991 2461621636328458221865343 := by
  unfold tailWord_4793991
  simp only [CollatzResearch.WordTrace]
  refine ⟨174851216375196830324013827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116567477583464553549342551 174851216375196830324013827)
  ·
    refine ⟨262276824562795245486020741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 174851216375196830324013827 262276824562795245486020741)
    ·
      refine ⟨49176904605524108528628889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 262276824562795245486020741 49176904605524108528628889)
      ·
        refine ⟨36882678454143081396471667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49176904605524108528628889 36882678454143081396471667)
        ·
          refine ⟨55324017681214622094707501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36882678454143081396471667 55324017681214622094707501)
          ·
            refine ⟨20746506630455483285515313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 55324017681214622094707501 20746506630455483285515313)
            ·
              refine ⟨15559879972841612464136485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20746506630455483285515313 15559879972841612464136485)
              ·
                refine ⟨2917477494907802337025591, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15559879972841612464136485 2917477494907802337025591)
                ·
                  refine ⟨4376216242361703505538387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2917477494907802337025591 4376216242361703505538387)
                  ·
                    refine ⟨6564324363542555258307581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4376216242361703505538387 6564324363542555258307581)
                    ·
                      refine ⟨2461621636328458221865343, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6564324363542555258307581 2461621636328458221865343)
                      ·
                        rfl

theorem cell23_4793991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 2, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 2, 4, 1, 1, 3].length) (baseStart_4793991 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4793991 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4793991 prefixEnd_4793991 := by exact prefixLift 4793991
  have htrace : WordTrace (prefixWord ++ tailWord_4793991) baseStart_4793991 baseEnd_4793991 := by
    simpa [prefixWord, tailWord_4793991, baseEnd_4793991] using wordTrace_append hprefix tailTrace_4793991
  have hstable : (prefixWord ++ tailWord_4793991).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4793991).length < 2 ^ (prefixWord ++ tailWord_4793991).sum := by decide
  have hdescent : baseEnd_4793991 < baseStart_4793991 := by decide
  rcases family_descends (prefixWord ++ tailWord_4793991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4794007 : List Nat := [1, 1, 3, 3, 2, 2, 3, 1, 1, 6]
def baseStart_4794007 : Nat := 118140960795 + 4794007 * 2 ^ 59
def prefixEnd_4794007 : Nat := 4983230072969 + 3 ^ 40 * 4794007 * 2
def baseEnd_4794007 : Nat := 820543284006310053088423

theorem tailTrace_4794007 : CollatzResearch.WordTrace tailWord_4794007 prefixEnd_4794007 820543284006310053088423 := by
  unfold tailWord_4794007
  simp only [CollatzResearch.WordTrace]
  refine ⟨174851799943138865056596275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116567866628759243371064183 174851799943138865056596275)
  ·
    refine ⟨262277699914708297584894413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 174851799943138865056596275 262277699914708297584894413)
    ·
      refine ⟨98354137468015611594335405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 262277699914708297584894413 98354137468015611594335405)
      ·
        refine ⟨36882801550505854347875777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 98354137468015611594335405 36882801550505854347875777)
        ·
          refine ⟨27662101162879390760906833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36882801550505854347875777 27662101162879390760906833)
          ·
            refine ⟨20746575872159543070680125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27662101162879390760906833 20746575872159543070680125)
            ·
              refine ⟨7779965952059828651505047, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20746575872159543070680125 7779965952059828651505047)
              ·
                refine ⟨11669948928089742977257571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7779965952059828651505047 11669948928089742977257571)
                ·
                  refine ⟨17504923392134614465886357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11669948928089742977257571 17504923392134614465886357)
                  ·
                    refine ⟨820543284006310053088423, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17504923392134614465886357 820543284006310053088423)
                    ·
                      rfl

theorem cell23_4794007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 3, 1, 1, 6].length) (baseStart_4794007 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4794007 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4794007 prefixEnd_4794007 := by exact prefixLift 4794007
  have htrace : WordTrace (prefixWord ++ tailWord_4794007) baseStart_4794007 baseEnd_4794007 := by
    simpa [prefixWord, tailWord_4794007, baseEnd_4794007] using wordTrace_append hprefix tailTrace_4794007
  have hstable : (prefixWord ++ tailWord_4794007).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4794007).length < 2 ^ (prefixWord ++ tailWord_4794007).sum := by decide
  have hdescent : baseEnd_4794007 < baseStart_4794007 := by decide
  rcases family_descends (prefixWord ++ tailWord_4794007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4794034 : List Nat := [3, 2, 1, 1, 1, 2, 4, 3, 1, 2, 3]
def baseStart_4794034 : Nat := 118140960795 + 4794034 * 2 ^ 59
def prefixEnd_4794034 : Nat := 4983230072969 + 3 ^ 40 * 4794034 * 2
def baseEnd_4794034 : Nat := 2461643715996601553627645

theorem tailTrace_4794034 : CollatzResearch.WordTrace tailWord_4794034 prefixEnd_4794034 2461643715996601553627645 := by
  unfold tailWord_4794034
  simp only [CollatzResearch.WordTrace]
  refine ⟨43713196178510262166957289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 116568523142694032445219437 43713196178510262166957289)
  ·
    refine ⟨32784897133882696625217967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43713196178510262166957289 32784897133882696625217967)
    ·
      refine ⟨49177345700824044937826951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32784897133882696625217967 49177345700824044937826951)
      ·
        refine ⟨73766018551236067406740427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49177345700824044937826951 73766018551236067406740427)
        ·
          refine ⟨110649027826854101110110641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 73766018551236067406740427 110649027826854101110110641)
          ·
            refine ⟨82986770870140575832582981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 110649027826854101110110641 82986770870140575832582981)
            ·
              refine ⟨15560019538151357968609309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 82986770870140575832582981 15560019538151357968609309)
              ·
                refine ⟨5835007326806759238228491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15560019538151357968609309 5835007326806759238228491)
                ·
                  refine ⟨8752510990210138857342737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5835007326806759238228491 8752510990210138857342737)
                  ·
                    refine ⟨6564383242657604143007053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8752510990210138857342737 6564383242657604143007053)
                    ·
                      refine ⟨2461643715996601553627645, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6564383242657604143007053 2461643715996601553627645)
                      ·
                        rfl

theorem cell23_4794034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 4, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 4, 3, 1, 2, 3].length) (baseStart_4794034 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4794034 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4794034 prefixEnd_4794034 := by exact prefixLift 4794034
  have htrace : WordTrace (prefixWord ++ tailWord_4794034) baseStart_4794034 baseEnd_4794034 := by
    simpa [prefixWord, tailWord_4794034, baseEnd_4794034] using wordTrace_append hprefix tailTrace_4794034
  have hstable : (prefixWord ++ tailWord_4794034).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4794034).length < 2 ^ (prefixWord ++ tailWord_4794034).sum := by decide
  have hdescent : baseEnd_4794034 < baseStart_4794034 := by decide
  rcases family_descends (prefixWord ++ tailWord_4794034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4794058 : List Nat := [3, 1, 2, 1, 5, 2, 2, 1, 2, 4]
def baseStart_4794058 : Nat := 118140960795 + 4794058 * 2 ^ 59
def prefixEnd_4794058 : Nat := 4983230072969 + 3 ^ 40 * 4794058 * 2
def baseEnd_4794058 : Nat := 820552013177436486575845

theorem tailTrace_4794058 : CollatzResearch.WordTrace tailWord_4794058 prefixEnd_4794058 820552013177436486575845 := by
  unfold tailWord_4794058
  simp only [CollatzResearch.WordTrace]
  refine ⟨43713415016488525191675707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 116569106710636067177801885 43713415016488525191675707)
  ·
    refine ⟨65570122524732787787513561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43713415016488525191675707 65570122524732787787513561)
    ·
      refine ⟨49177591893549590840635171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 65570122524732787787513561 49177591893549590840635171)
      ·
        refine ⟨73766387840324386260952757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49177591893549590840635171 73766387840324386260952757)
        ·
          refine ⟨6915598860030411211964321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 73766387840324386260952757 6915598860030411211964321)
          ·
            refine ⟨5186699145022808408973241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6915598860030411211964321 5186699145022808408973241)
            ·
              refine ⟨3890024358767106306729931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5186699145022808408973241 3890024358767106306729931)
              ·
                refine ⟨5835036538150659460094897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3890024358767106306729931 5835036538150659460094897)
                ·
                  refine ⟨4376277403612994595071173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5835036538150659460094897 4376277403612994595071173)
                  ·
                    refine ⟨820552013177436486575845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4376277403612994595071173 820552013177436486575845)
                    ·
                      rfl

theorem cell23_4794058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 5, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 5, 2, 2, 1, 2, 4].length) (baseStart_4794058 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4794058 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4794058 prefixEnd_4794058 := by exact prefixLift 4794058
  have htrace : WordTrace (prefixWord ++ tailWord_4794058) baseStart_4794058 baseEnd_4794058 := by
    simpa [prefixWord, tailWord_4794058, baseEnd_4794058] using wordTrace_append hprefix tailTrace_4794058
  have hstable : (prefixWord ++ tailWord_4794058).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4794058).length < 2 ^ (prefixWord ++ tailWord_4794058).sum := by decide
  have hdescent : baseEnd_4794058 < baseStart_4794058 := by decide
  rcases family_descends (prefixWord ++ tailWord_4794058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4794068 : List Nat := [2, 4, 1, 3, 1, 3, 1, 2, 1, 2, 3]
def baseStart_4794068 : Nat := 118140960795 + 4794068 * 2 ^ 59
def prefixEnd_4794068 : Nat := 4983230072969 + 3 ^ 40 * 4794068 * 2
def baseEnd_4794068 : Nat := 2461661174338854420602489

theorem tailTrace_4794068 : CollatzResearch.WordTrace tailWord_4794068 prefixEnd_4794068 2461661174338854420602489 := by
  unfold tailWord_4794068
  simp only [CollatzResearch.WordTrace]
  refine ⟨87427012397958936237283429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116569349863945248316377905 87427012397958936237283429)
  ·
    refine ⟨16392564824617300544490643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 87427012397958936237283429 16392564824617300544490643)
    ·
      refine ⟨24588847236925950816735965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16392564824617300544490643 24588847236925950816735965)
      ·
        refine ⟨9220817713847231556275987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24588847236925950816735965 9220817713847231556275987)
        ·
          refine ⟨13831226570770847334413981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9220817713847231556275987 13831226570770847334413981)
          ·
            refine ⟨5186709964039067750405243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13831226570770847334413981 5186709964039067750405243)
            ·
              refine ⟨7780064946058601625607865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5186709964039067750405243 7780064946058601625607865)
              ·
                refine ⟨5835048709543951219205899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7780064946058601625607865 5835048709543951219205899)
                ·
                  refine ⟨8752573064315926828808849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5835048709543951219205899 8752573064315926828808849)
                  ·
                    refine ⟨6564429798236945121606637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8752573064315926828808849 6564429798236945121606637)
                    ·
                      refine ⟨2461661174338854420602489, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6564429798236945121606637 2461661174338854420602489)
                      ·
                        rfl

theorem cell23_4794068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 3, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 3, 1, 2, 1, 2, 3].length) (baseStart_4794068 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4794068 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4794068 prefixEnd_4794068 := by exact prefixLift 4794068
  have htrace : WordTrace (prefixWord ++ tailWord_4794068) baseStart_4794068 baseEnd_4794068 := by
    simpa [prefixWord, tailWord_4794068, baseEnd_4794068] using wordTrace_append hprefix tailTrace_4794068
  have hstable : (prefixWord ++ tailWord_4794068).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4794068).length < 2 ^ (prefixWord ++ tailWord_4794068).sum := by decide
  have hdescent : baseEnd_4794068 < baseStart_4794068 := by decide
  rcases family_descends (prefixWord ++ tailWord_4794068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4794114 : List Nat := [3, 4, 1, 1, 1, 1, 3, 1, 2, 6]
def baseStart_4794114 : Nat := 118140960795 + 4794114 * 2 ^ 59
def prefixEnd_4794114 : Nat := 4983230072969 + 3 ^ 40 * 4794114 * 2
def baseEnd_4794114 : Nat := 820561598149653746875759

theorem tailTrace_4794114 : CollatzResearch.WordTrace tailWord_4794114 prefixEnd_4794114 820561598149653746875759 := by
  unfold tailWord_4794114
  simp only [CollatzResearch.WordTrace]
  refine ⟨43713925638437805582685349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 116570468369167481553827597 43713925638437805582685349)
  ·
    refine ⟨8196361057207088546753503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 43713925638437805582685349 8196361057207088546753503)
    ·
      refine ⟨12294541585810632820130255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8196361057207088546753503 12294541585810632820130255)
      ·
        refine ⟨18441812378715949230195383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12294541585810632820130255 18441812378715949230195383)
        ·
          refine ⟨27662718568073923845293075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18441812378715949230195383 27662718568073923845293075)
          ·
            refine ⟨41494077852110885767939613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27662718568073923845293075 41494077852110885767939613)
            ·
              refine ⟨15560279194541582162977355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 41494077852110885767939613 15560279194541582162977355)
              ·
                refine ⟨23340418791812373244466033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15560279194541582162977355 23340418791812373244466033)
                ·
                  refine ⟨17505314093859279933349525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23340418791812373244466033 17505314093859279933349525)
                  ·
                    refine ⟨820561598149653746875759, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17505314093859279933349525 820561598149653746875759)
                    ·
                      rfl

theorem cell23_4794114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 3, 1, 2, 6].length) (baseStart_4794114 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4794114 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4794114 prefixEnd_4794114 := by exact prefixLift 4794114
  have htrace : WordTrace (prefixWord ++ tailWord_4794114) baseStart_4794114 baseEnd_4794114 := by
    simpa [prefixWord, tailWord_4794114, baseEnd_4794114] using wordTrace_append hprefix tailTrace_4794114
  have hstable : (prefixWord ++ tailWord_4794114).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4794114).length < 2 ^ (prefixWord ++ tailWord_4794114).sum := by decide
  have hdescent : baseEnd_4794114 < baseStart_4794114 := by decide
  rcases family_descends (prefixWord ++ tailWord_4794114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4794142 : List Nat := [4, 3, 2, 2, 1, 1, 1, 3, 1, 3, 2]
def baseStart_4794142 : Nat := 118140960795 + 4794142 * 2 ^ 59
def prefixEnd_4794142 : Nat := 4983230072969 + 3 ^ 40 * 4794142 * 2
def baseEnd_4794142 : Nat := 2461699171907287131077149

theorem tailTrace_4794142 : CollatzResearch.WordTrace tailWord_4794142 prefixEnd_4794142 2461699171907287131077149 := by
  unfold tailWord_4794142
  simp only [CollatzResearch.WordTrace]
  refine ⟨21857090474706222889095085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 116571149198433188741840453 21857090474706222889095085)
  ·
    refine ⟨8196408928014833583410657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21857090474706222889095085 8196408928014833583410657)
    ·
      refine ⟨6147306696011125187557993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8196408928014833583410657 6147306696011125187557993)
      ·
        refine ⟨4610480022008343890668495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6147306696011125187557993 4610480022008343890668495)
        ·
          refine ⟨6915720033012515836002743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4610480022008343890668495 6915720033012515836002743)
          ·
            refine ⟨10373580049518773754004115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6915720033012515836002743 10373580049518773754004115)
            ·
              refine ⟨15560370074278160631006173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10373580049518773754004115 15560370074278160631006173)
              ·
                refine ⟨5835138777854310236627315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15560370074278160631006173 5835138777854310236627315)
                ·
                  refine ⟨8752708166781465354940973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5835138777854310236627315 8752708166781465354940973)
                  ·
                    refine ⟨3282265562543049508102865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8752708166781465354940973 3282265562543049508102865)
                    ·
                      refine ⟨2461699171907287131077149, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3282265562543049508102865 2461699171907287131077149)
                      ·
                        rfl

theorem cell23_4794142_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 1, 1, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 1, 1, 1, 3, 1, 3, 2].length) (baseStart_4794142 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4794142 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4794142 prefixEnd_4794142 := by exact prefixLift 4794142
  have htrace : WordTrace (prefixWord ++ tailWord_4794142) baseStart_4794142 baseEnd_4794142 := by
    simpa [prefixWord, tailWord_4794142, baseEnd_4794142] using wordTrace_append hprefix tailTrace_4794142
  have hstable : (prefixWord ++ tailWord_4794142).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4794142).length < 2 ^ (prefixWord ++ tailWord_4794142).sum := by decide
  have hdescent : baseEnd_4794142 < baseStart_4794142 := by decide
  rcases family_descends (prefixWord ++ tailWord_4794142) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4794174 : List Nat := [4, 2, 1, 2, 2, 1, 1, 2, 1, 7]
def baseStart_4794174 : Nat := 118140960795 + 4794174 * 2 ^ 59
def prefixEnd_4794174 : Nat := 4983230072969 + 3 ^ 40 * 4794174 * 2
def baseEnd_4794174 : Nat := 820571867762743668625667

theorem tailTrace_4794174 : CollatzResearch.WordTrace tailWord_4794174 prefixEnd_4794174 820571867762743668625667 := by
  unfold tailWord_4794174
  simp only [CollatzResearch.WordTrace]
  refine ⟨21857236366691731572240697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 116571927289022568385283717 21857236366691731572240697)
  ·
    refine ⟨16392927275018798679180523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21857236366691731572240697 16392927275018798679180523)
    ·
      refine ⟨24589390912528198018770785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16392927275018798679180523 24589390912528198018770785)
      ·
        refine ⟨18442043184396148514078089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24589390912528198018770785 18442043184396148514078089)
        ·
          refine ⟨13831532388297111385558567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18442043184396148514078089 13831532388297111385558567)
          ·
            refine ⟨20747298582445667078337851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13831532388297111385558567 20747298582445667078337851)
            ·
              refine ⟨31120947873668500617506777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20747298582445667078337851 31120947873668500617506777)
              ·
                refine ⟨23340710905251375463130083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31120947873668500617506777 23340710905251375463130083)
                ·
                  refine ⟨35011066357877063194695125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23340710905251375463130083 35011066357877063194695125)
                  ·
                    refine ⟨820571867762743668625667, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 35011066357877063194695125 820571867762743668625667)
                    ·
                      rfl

theorem cell23_4794174_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 1, 2, 1, 7].length) (baseStart_4794174 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4794174 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4794174 prefixEnd_4794174 := by exact prefixLift 4794174
  have htrace : WordTrace (prefixWord ++ tailWord_4794174) baseStart_4794174 baseEnd_4794174 := by
    simpa [prefixWord, tailWord_4794174, baseEnd_4794174] using wordTrace_append hprefix tailTrace_4794174
  have hstable : (prefixWord ++ tailWord_4794174).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4794174).length < 2 ^ (prefixWord ++ tailWord_4794174).sum := by decide
  have hdescent : baseEnd_4794174 < baseStart_4794174 := by decide
  rcases family_descends (prefixWord ++ tailWord_4794174) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4794194 : List Nat := [3, 2, 2, 1, 1, 3, 2, 1, 1, 3, 4]
def baseStart_4794194 : Nat := 118140960795 + 4794194 * 2 ^ 59
def prefixEnd_4794194 : Nat := 4983230072969 + 3 ^ 40 * 4794194 * 2
def baseEnd_4794194 : Nat := 2461725872901320927626909

theorem tailTrace_4794194 : CollatzResearch.WordTrace tailWord_4794194 prefixEnd_4794194 2461725872901320927626909 := by
  unfold tailWord_4794194
  simp only [CollatzResearch.WordTrace]
  refine ⟨43714655098365348998413409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 116572413595640930662435757 43714655098365348998413409)
  ·
    refine ⟨32785991323774011748810057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43714655098365348998413409 32785991323774011748810057)
    ·
      refine ⟨24589493492830508811607543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32785991323774011748810057 24589493492830508811607543)
      ·
        refine ⟨36884240239245763217411315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24589493492830508811607543 36884240239245763217411315)
        ·
          refine ⟨55326360358868644826116973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36884240239245763217411315 55326360358868644826116973)
          ·
            refine ⟨20747385134575741809793865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 55326360358868644826116973 20747385134575741809793865)
            ·
              refine ⟨15560538850931806357345399, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20747385134575741809793865 15560538850931806357345399)
              ·
                refine ⟨23340808276397709536018099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15560538850931806357345399 23340808276397709536018099)
                ·
                  refine ⟨35011212414596564304027149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23340808276397709536018099 35011212414596564304027149)
                  ·
                    refine ⟨13129204655473711614010181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 35011212414596564304027149 13129204655473711614010181)
                    ·
                      refine ⟨2461725872901320927626909, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13129204655473711614010181 2461725872901320927626909)
                      ·
                        rfl

theorem cell23_4794194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 2, 1, 1, 3, 4].length) (baseStart_4794194 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4794194 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4794194 prefixEnd_4794194 := by exact prefixLift 4794194
  have htrace : WordTrace (prefixWord ++ tailWord_4794194) baseStart_4794194 baseEnd_4794194 := by
    simpa [prefixWord, tailWord_4794194, baseEnd_4794194] using wordTrace_append hprefix tailTrace_4794194
  have hstable : (prefixWord ++ tailWord_4794194).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4794194).length < 2 ^ (prefixWord ++ tailWord_4794194).sum := by decide
  have hdescent : baseEnd_4794194 < baseStart_4794194 := by decide
  rcases family_descends (prefixWord ++ tailWord_4794194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4794211 : List Nat := [1, 1, 1, 5, 4, 1, 1, 2, 2, 1, 4]
def baseStart_4794211 : Nat := 118140960795 + 4794211 * 2 ^ 59
def prefixEnd_4794211 : Nat := 4983230072969 + 3 ^ 40 * 4794211 * 2
def baseEnd_4794211 : Nat := 2461734602072447361114331

theorem tailTrace_4794211 : CollatzResearch.WordTrace tailWord_4794211 prefixEnd_4794211 2461734602072447361114331 := by
  unfold tailWord_4794211
  simp only [CollatzResearch.WordTrace]
  refine ⟨174859240434399807897022487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116572826956266538598014991 174859240434399807897022487)
  ·
    refine ⟨262288860651599711845533731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 174859240434399807897022487 262288860651599711845533731)
    ·
      refine ⟨393433290977399567768300597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 262288860651599711845533731 393433290977399567768300597)
      ·
        refine ⟨36884371029131209478278181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 393433290977399567768300597 36884371029131209478278181)
        ·
          refine ⟨6915819567962101777177159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 36884371029131209478278181 6915819567962101777177159)
          ·
            refine ⟨10373729351943152665765739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6915819567962101777177159 10373729351943152665765739)
            ·
              refine ⟨15560594027914728998648609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10373729351943152665765739 15560594027914728998648609)
              ·
                refine ⟨11670445520936046748986457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15560594027914728998648609 11670445520936046748986457)
                ·
                  refine ⟨8752834140702035061739843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11670445520936046748986457 8752834140702035061739843)
                  ·
                    refine ⟨13129251211053052592609765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8752834140702035061739843 13129251211053052592609765)
                    ·
                      refine ⟨2461734602072447361114331, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13129251211053052592609765 2461734602072447361114331)
                      ·
                        rfl

theorem cell23_4794211_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 4, 1, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 4, 1, 1, 2, 2, 1, 4].length) (baseStart_4794211 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4794211 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4794211 prefixEnd_4794211 := by exact prefixLift 4794211
  have htrace : WordTrace (prefixWord ++ tailWord_4794211) baseStart_4794211 baseEnd_4794211 := by
    simpa [prefixWord, tailWord_4794211, baseEnd_4794211] using wordTrace_append hprefix tailTrace_4794211
  have hstable : (prefixWord ++ tailWord_4794211).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4794211).length < 2 ^ (prefixWord ++ tailWord_4794211).sum := by decide
  have hdescent : baseEnd_4794211 < baseStart_4794211 := by decide
  rcases family_descends (prefixWord ++ tailWord_4794211) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4794221 : List Nat := [1, 5, 1, 1, 1, 1, 5, 1, 3, 4]
def baseStart_4794221 : Nat := 118140960795 + 4794221 * 2 ^ 59
def prefixEnd_4794221 : Nat := 4983230072969 + 3 ^ 40 * 4794221 * 2
def baseEnd_4794221 : Nat := 820579912292997440663095

theorem tailTrace_4794221 : CollatzResearch.WordTrace tailWord_4794221 prefixEnd_4794221 820579912292997440663095 := by
  unfold tailWord_4794221
  simp only [CollatzResearch.WordTrace]
  refine ⟨174859605164363579604886517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116573070109575719736591011 174859605164363579604886517)
  ·
    refine ⟨16393087984159085587958111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 174859605164363579604886517 16393087984159085587958111)
    ·
      refine ⟨24589631976238628381937167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16393087984159085587958111 24589631976238628381937167)
      ·
        refine ⟨36884447964357942572905751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24589631976238628381937167 36884447964357942572905751)
        ·
          refine ⟨55326671946536913859358627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36884447964357942572905751 55326671946536913859358627)
          ·
            refine ⟨82990007919805370789037941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55326671946536913859358627 82990007919805370789037941)
            ·
              refine ⟨7780313242481753511472307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 82990007919805370789037941 7780313242481753511472307)
              ·
                refine ⟨11670469863722630267208461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7780313242481753511472307 11670469863722630267208461)
                ·
                  refine ⟨4376426198895986350203173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11670469863722630267208461 4376426198895986350203173)
                  ·
                    refine ⟨820579912292997440663095, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4376426198895986350203173 820579912292997440663095)
                    ·
                      rfl

theorem cell23_4794221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 5, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 5, 1, 3, 4].length) (baseStart_4794221 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4794221 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4794221 prefixEnd_4794221 := by exact prefixLift 4794221
  have htrace : WordTrace (prefixWord ++ tailWord_4794221) baseStart_4794221 baseEnd_4794221 := by
    simpa [prefixWord, tailWord_4794221, baseEnd_4794221] using wordTrace_append hprefix tailTrace_4794221
  have hstable : (prefixWord ++ tailWord_4794221).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4794221).length < 2 ^ (prefixWord ++ tailWord_4794221).sum := by decide
  have hdescent : baseEnd_4794221 < baseStart_4794221 := by decide
  rcases family_descends (prefixWord ++ tailWord_4794221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4794244 : List Nat := [2, 3, 2, 1, 1, 1, 2, 1, 2, 5, 3]
def baseStart_4794244 : Nat := 118140960795 + 4794244 * 2 ^ 59
def prefixEnd_4794244 : Nat := 4983230072969 + 3 ^ 40 * 4794244 * 2
def baseEnd_4794244 : Nat := 2461751546934045732001679

theorem tailTrace_4794244 : CollatzResearch.WordTrace tailWord_4794244 prefixEnd_4794244 2461751546934045732001679 := by
  unfold tailWord_4794244
  simp only [CollatzResearch.WordTrace]
  refine ⟨87430222021640127266486893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116573629362186836355315857 87430222021640127266486893)
  ·
    refine ⟨32786333258115047724932585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 87430222021640127266486893 32786333258115047724932585)
    ·
      refine ⟨24589749943586285793699439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32786333258115047724932585 24589749943586285793699439)
      ·
        refine ⟨36884624915379428690549159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24589749943586285793699439 36884624915379428690549159)
        ·
          refine ⟨55326937373069143035823739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36884624915379428690549159 55326937373069143035823739)
          ·
            refine ⟨82990406059603714553735609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55326937373069143035823739 82990406059603714553735609)
            ·
              refine ⟨62242804544702785915301707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 82990406059603714553735609 62242804544702785915301707)
              ·
                refine ⟨93364206817054178872952561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 62242804544702785915301707 93364206817054178872952561)
                ·
                  refine ⟨70023155112790634154714421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 93364206817054178872952561 70023155112790634154714421)
                  ·
                    refine ⟨6564670791824121952004477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 70023155112790634154714421 6564670791824121952004477)
                    ·
                      refine ⟨2461751546934045732001679, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6564670791824121952004477 2461751546934045732001679)
                      ·
                        rfl

theorem cell23_4794244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 2, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 2, 1, 2, 5, 3].length) (baseStart_4794244 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4794244 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4794244 prefixEnd_4794244 := by exact prefixLift 4794244
  have htrace : WordTrace (prefixWord ++ tailWord_4794244) baseStart_4794244 baseEnd_4794244 := by
    simpa [prefixWord, tailWord_4794244, baseEnd_4794244] using wordTrace_append hprefix tailTrace_4794244
  have hstable : (prefixWord ++ tailWord_4794244).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4794244).length < 2 ^ (prefixWord ++ tailWord_4794244).sum := by decide
  have hdescent : baseEnd_4794244 < baseStart_4794244 := by decide
  rcases family_descends (prefixWord ++ tailWord_4794244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4794248 : List Nat := [2, 1, 3, 3, 3, 1, 2, 1, 2, 2, 3]
def baseStart_4794248 : Nat := 118140960795 + 4794248 * 2 ^ 59
def prefixEnd_4794248 : Nat := 4983230072969 + 3 ^ 40 * 4794248 * 2
def baseEnd_4794248 : Nat := 2461753600856663716351661

theorem tailTrace_4794248 : CollatzResearch.WordTrace tailWord_4794248 prefixEnd_4794248 2461753600856663716351661 := by
  unfold tailWord_4794248
  simp only [CollatzResearch.WordTrace]
  refine ⟨87430294967632881608059699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116573726623510508810746265 87430294967632881608059699)
  ·
    refine ⟨131145442451449322412089549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87430294967632881608059699 131145442451449322412089549)
    ·
      refine ⟨49179540919293495904533581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 131145442451449322412089549 49179540919293495904533581)
      ·
        refine ⟨18442327844735060964200093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 49179540919293495904533581 18442327844735060964200093)
        ·
          refine ⟨6915872941775647861575035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18442327844735060964200093 6915872941775647861575035)
          ·
            refine ⟨10373809412663471792362553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6915872941775647861575035 10373809412663471792362553)
            ·
              refine ⟨7780357059497603844271915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10373809412663471792362553 7780357059497603844271915)
              ·
                refine ⟨11670535589246405766407873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7780357059497603844271915 11670535589246405766407873)
                ·
                  refine ⟨8752901691934804324805905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11670535589246405766407873 8752901691934804324805905)
                  ·
                    refine ⟨6564676268951103243604429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8752901691934804324805905 6564676268951103243604429)
                    ·
                      refine ⟨2461753600856663716351661, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6564676268951103243604429 2461753600856663716351661)
                      ·
                        rfl

theorem cell23_4794248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 3, 1, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 3, 1, 2, 1, 2, 2, 3].length) (baseStart_4794248 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4794248 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4794248 prefixEnd_4794248 := by exact prefixLift 4794248
  have htrace : WordTrace (prefixWord ++ tailWord_4794248) baseStart_4794248 baseEnd_4794248 := by
    simpa [prefixWord, tailWord_4794248, baseEnd_4794248] using wordTrace_append hprefix tailTrace_4794248
  have hstable : (prefixWord ++ tailWord_4794248).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4794248).length < 2 ^ (prefixWord ++ tailWord_4794248).sum := by decide
  have hdescent : baseEnd_4794248 < baseStart_4794248 := by decide
  rcases family_descends (prefixWord ++ tailWord_4794248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4794301 : List Nat := [1, 4, 1, 2, 3, 1, 2, 1, 3, 1, 4]
def baseStart_4794301 : Nat := 118140960795 + 4794301 * 2 ^ 59
def prefixEnd_4794301 : Nat := 4983230072969 + 3 ^ 40 * 4794301 * 2
def baseEnd_4794301 : Nat := 2461780815331352008988917

theorem tailTrace_4794301 : CollatzResearch.WordTrace tailWord_4794301 prefixEnd_4794301 2461780815331352008988917 := by
  unfold tailWord_4794301
  simp only [CollatzResearch.WordTrace]
  refine ⟨174862523004073753267798757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116575015336049168845199171 174862523004073753267798757)
  ·
    refine ⟨32786723063263828737712267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 174862523004073753267798757 32786723063263828737712267)
    ·
      refine ⟨49180084594895743106568401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32786723063263828737712267 49180084594895743106568401)
      ·
        refine ⟨36885063446171807329926301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49180084594895743106568401 36885063446171807329926301)
        ·
          refine ⟨13831898792314427748722363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 36885063446171807329926301 13831898792314427748722363)
          ·
            refine ⟨20747848188471641623083545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13831898792314427748722363 20747848188471641623083545)
            ·
              refine ⟨15560886141353731217312659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20747848188471641623083545 15560886141353731217312659)
              ·
                refine ⟨23341329212030596825968989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15560886141353731217312659 23341329212030596825968989)
                ·
                  refine ⟨8752998454511473809738371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23341329212030596825968989 8752998454511473809738371)
                  ·
                    refine ⟨13129497681767210714607557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8752998454511473809738371 13129497681767210714607557)
                    ·
                      refine ⟨2461780815331352008988917, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13129497681767210714607557 2461780815331352008988917)
                      ·
                        rfl

theorem cell23_4794301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 2, 1, 3, 1, 4].length) (baseStart_4794301 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4794301 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4794301 prefixEnd_4794301 := by exact prefixLift 4794301
  have htrace : WordTrace (prefixWord ++ tailWord_4794301) baseStart_4794301 baseEnd_4794301 := by
    simpa [prefixWord, tailWord_4794301, baseEnd_4794301] using wordTrace_append hprefix tailTrace_4794301
  have hstable : (prefixWord ++ tailWord_4794301).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4794301).length < 2 ^ (prefixWord ++ tailWord_4794301).sum := by decide
  have hdescent : baseEnd_4794301 < baseStart_4794301 := by decide
  rcases family_descends (prefixWord ++ tailWord_4794301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4794318 : List Nat := [4, 1, 1, 1, 2, 2, 1, 2, 5, 2, 2]
def baseStart_4794318 : Nat := 118140960795 + 4794318 * 2 ^ 59
def prefixEnd_4794318 : Nat := 4983230072969 + 3 ^ 40 * 4794318 * 2
def baseEnd_4794318 : Nat := 2461789544502478442476339

theorem tailTrace_4794318 : CollatzResearch.WordTrace tailWord_4794318 prefixEnd_4794318 2461789544502478442476339 := by
  unfold tailWord_4794318
  simp only [CollatzResearch.WordTrace]
  refine ⟨21857892880626520646395951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 116575428696674776780778405 21857892880626520646395951)
  ·
    refine ⟨32786839320939780969593927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21857892880626520646395951 32786839320939780969593927)
    ·
      refine ⟨49180258981409671454390891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32786839320939780969593927 49180258981409671454390891)
      ·
        refine ⟨73770388472114507181586337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49180258981409671454390891 73770388472114507181586337)
        ·
          refine ⟨55327791354085880386189753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 73770388472114507181586337 55327791354085880386189753)
          ·
            refine ⟨41495843515564410289642315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 55327791354085880386189753 41495843515564410289642315)
            ·
              refine ⟨62243765273346615434463473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41495843515564410289642315 62243765273346615434463473)
              ·
                refine ⟨46682823955009961575847605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 62243765273346615434463473 46682823955009961575847605)
                ·
                  refine ⟨4376514745782183897735713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 46682823955009961575847605 4376514745782183897735713)
                  ·
                    refine ⟨3282386059336637923301785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4376514745782183897735713 3282386059336637923301785)
                    ·
                      refine ⟨2461789544502478442476339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3282386059336637923301785 2461789544502478442476339)
                      ·
                        rfl

theorem cell23_4794318_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 1, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 1, 2, 5, 2, 2].length) (baseStart_4794318 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4794318 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4794318 prefixEnd_4794318 := by exact prefixLift 4794318
  have htrace : WordTrace (prefixWord ++ tailWord_4794318) baseStart_4794318 baseEnd_4794318 := by
    simpa [prefixWord, tailWord_4794318, baseEnd_4794318] using wordTrace_append hprefix tailTrace_4794318
  have hstable : (prefixWord ++ tailWord_4794318).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4794318).length < 2 ^ (prefixWord ++ tailWord_4794318).sum := by decide
  have hdescent : baseEnd_4794318 < baseStart_4794318 := by decide
  rcases family_descends (prefixWord ++ tailWord_4794318) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4794324 : List Nat := [2, 4, 1, 2, 1, 1, 12]
def baseStart_4794324 : Nat := 118140960795 + 4794324 * 2 ^ 59
def prefixEnd_4794324 : Nat := 4983230072969 + 3 ^ 40 * 4794324 * 2
def baseEnd_4794324 : Nat := 30392501547980313814831

theorem tailTrace_4794324 : CollatzResearch.WordTrace tailWord_4794324 prefixEnd_4794324 30392501547980313814831 := by
  unfold tailWord_4794324
  simp only [CollatzResearch.WordTrace]
  refine ⟨87431680941495214097943013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116575574588660285463924017 87431680941495214097943013)
  ·
    refine ⟨16393440176530352643364315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 87431680941495214097943013 16393440176530352643364315)
    ·
      refine ⟨24590160264795528965046473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16393440176530352643364315 24590160264795528965046473)
      ·
        refine ⟨18442620198596646723784855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24590160264795528965046473 18442620198596646723784855)
        ·
          refine ⟨27663930297894970085677283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18442620198596646723784855 27663930297894970085677283)
          ·
            refine ⟨41495895446842455128515925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27663930297894970085677283 41495895446842455128515925)
            ·
              refine ⟨30392501547980313814831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 12 41495895446842455128515925 30392501547980313814831)
              ·
                rfl

theorem cell23_4794324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 12].length) (baseStart_4794324 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4794324 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4794324 prefixEnd_4794324 := by exact prefixLift 4794324
  have htrace : WordTrace (prefixWord ++ tailWord_4794324) baseStart_4794324 baseEnd_4794324 := by
    simpa [prefixWord, tailWord_4794324, baseEnd_4794324] using wordTrace_append hprefix tailTrace_4794324
  have hstable : (prefixWord ++ tailWord_4794324).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4794324).length < 2 ^ (prefixWord ++ tailWord_4794324).sum := by decide
  have hdescent : baseEnd_4794324 < baseStart_4794324 := by decide
  rcases family_descends (prefixWord ++ tailWord_4794324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4794335 : List Nat := [1, 1, 2, 3, 4, 2, 2, 1, 3, 2, 2]
def baseStart_4794335 : Nat := 118140960795 + 4794335 * 2 ^ 59
def prefixEnd_4794335 : Nat := 4983230072969 + 3 ^ 40 * 4794335 * 2
def baseEnd_4794335 : Nat := 2461798273673604875963761

theorem tailTrace_4794335 : CollatzResearch.WordTrace tailWord_4794335 prefixEnd_4794335 2461798273673604875963761 := by
  unfold tailWord_4794335
  simp only [CollatzResearch.WordTrace]
  refine ⟨174863763085950577074536459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116575842057300384716357639 174863763085950577074536459)
  ·
    refine ⟨262295644628925865611804689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 174863763085950577074536459 262295644628925865611804689)
    ·
      refine ⟨196721733471694399208853517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 262295644628925865611804689 196721733471694399208853517)
      ·
        refine ⟨73770650051885399703320069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 196721733471694399208853517 73770650051885399703320069)
        ·
          refine ⟨13831996884728512444372513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 73770650051885399703320069 13831996884728512444372513)
          ·
            refine ⟨10373997663546384333279385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13831996884728512444372513 10373997663546384333279385)
            ·
              refine ⟨7780498247659788249959539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10373997663546384333279385 7780498247659788249959539)
              ·
                refine ⟨11670747371489682374939309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7780498247659788249959539 11670747371489682374939309)
                ·
                  refine ⟨4376530264308630890602241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11670747371489682374939309 4376530264308630890602241)
                  ·
                    refine ⟨3282397698231473167951681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4376530264308630890602241 3282397698231473167951681)
                    ·
                      refine ⟨2461798273673604875963761, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3282397698231473167951681 2461798273673604875963761)
                      ·
                        rfl

theorem cell23_4794335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 2, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 2, 2, 1, 3, 2, 2].length) (baseStart_4794335 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4794335 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4794335 prefixEnd_4794335 := by exact prefixLift 4794335
  have htrace : WordTrace (prefixWord ++ tailWord_4794335) baseStart_4794335 baseEnd_4794335 := by
    simpa [prefixWord, tailWord_4794335, baseEnd_4794335] using wordTrace_append hprefix tailTrace_4794335
  have hstable : (prefixWord ++ tailWord_4794335).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4794335).length < 2 ^ (prefixWord ++ tailWord_4794335).sum := by decide
  have hdescent : baseEnd_4794335 < baseStart_4794335 := by decide
  rcases family_descends (prefixWord ++ tailWord_4794335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4794364 : List Nat := [2, 2, 2, 1, 2, 2, 1, 1, 1, 4, 5]
def baseStart_4794364 : Nat := 118140960795 + 4794364 * 2 ^ 59
def prefixEnd_4794364 : Nat := 4983230072969 + 3 ^ 40 * 4794364 * 2
def baseEnd_4794364 : Nat := 2461813164612585262501127

theorem tailTrace_4794364 : CollatzResearch.WordTrace tailWord_4794364 prefixEnd_4794364 2461813164612585262501127 := by
  unfold tailWord_4794364
  simp only [CollatzResearch.WordTrace]
  refine ⟨87432410401422757513671073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116576547201897010018228097 87432410401422757513671073)
  ·
    refine ⟨65574307801067068135253305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 87432410401422757513671073 65574307801067068135253305)
    ·
      refine ⟨49180730850800301101439979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 65574307801067068135253305 49180730850800301101439979)
      ·
        refine ⟨73771096276200451652159969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49180730850800301101439979 73771096276200451652159969)
        ·
          refine ⟨55328322207150338739119977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 73771096276200451652159969 55328322207150338739119977)
          ·
            refine ⟨41496241655362754054339983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 55328322207150338739119977 41496241655362754054339983)
            ·
              refine ⟨62244362483044131081509975, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41496241655362754054339983 62244362483044131081509975)
              ·
                refine ⟨93366543724566196622264963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 62244362483044131081509975 93366543724566196622264963)
                ·
                  refine ⟨140049815586849294933397445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 93366543724566196622264963 140049815586849294933397445)
                  ·
                    refine ⟨26259340422534242800012021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 140049815586849294933397445 26259340422534242800012021)
                    ·
                      refine ⟨2461813164612585262501127, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26259340422534242800012021 2461813164612585262501127)
                      ·
                        rfl

theorem cell23_4794364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 1, 1, 1, 4, 5].length) (baseStart_4794364 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4794364 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4794364 prefixEnd_4794364 := by exact prefixLift 4794364
  have htrace : WordTrace (prefixWord ++ tailWord_4794364) baseStart_4794364 baseEnd_4794364 := by
    simpa [prefixWord, tailWord_4794364, baseEnd_4794364] using wordTrace_append hprefix tailTrace_4794364
  have hstable : (prefixWord ++ tailWord_4794364).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4794364).length < 2 ^ (prefixWord ++ tailWord_4794364).sum := by decide
  have hdescent : baseEnd_4794364 < baseStart_4794364 := by decide
  rcases family_descends (prefixWord ++ tailWord_4794364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4794425 : List Nat := [1, 2, 1, 5, 3, 1, 1, 2, 1, 4, 2]
def baseStart_4794425 : Nat := 118140960795 + 4794425 * 2 ^ 59
def prefixEnd_4794425 : Nat := 4983230072969 + 3 ^ 40 * 4794425 * 2
def baseEnd_4794425 : Nat := 2461844486932509523838347

theorem tailTrace_4794425 : CollatzResearch.WordTrace tailWord_4794425 prefixEnd_4794425 2461844486932509523838347 := by
  unfold tailWord_4794425
  simp only [CollatzResearch.WordTrace]
  refine ⟨174867045655624522445312729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116578030437083014963541819 174867045655624522445312729)
  ·
    refine ⟨131150284241718391833984547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 174867045655624522445312729 131150284241718391833984547)
    ·
      refine ⟨196725426362577587750976821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 131150284241718391833984547 196725426362577587750976821)
      ·
        refine ⟨18443008721491648851654077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 196725426362577587750976821 18443008721491648851654077)
        ·
          refine ⟨6916128270559368319370279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18443008721491648851654077 6916128270559368319370279)
          ·
            refine ⟨10374192405839052479055419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6916128270559368319370279 10374192405839052479055419)
            ·
              refine ⟨15561288608758578718583129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10374192405839052479055419 15561288608758578718583129)
              ·
                refine ⟨11670966456568934038937347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15561288608758578718583129 11670966456568934038937347)
                ·
                  refine ⟨17506449684853401058406021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11670966456568934038937347 17506449684853401058406021)
                  ·
                    refine ⟨3282459315910012698451129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17506449684853401058406021 3282459315910012698451129)
                    ·
                      refine ⟨2461844486932509523838347, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3282459315910012698451129 2461844486932509523838347)
                      ·
                        rfl

theorem cell23_4794425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 3, 1, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 3, 1, 1, 2, 1, 4, 2].length) (baseStart_4794425 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4794425 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4794425 prefixEnd_4794425 := by exact prefixLift 4794425
  have htrace : WordTrace (prefixWord ++ tailWord_4794425) baseStart_4794425 baseEnd_4794425 := by
    simpa [prefixWord, tailWord_4794425, baseEnd_4794425] using wordTrace_append hprefix tailTrace_4794425
  have hstable : (prefixWord ++ tailWord_4794425).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4794425).length < 2 ^ (prefixWord ++ tailWord_4794425).sum := by decide
  have hdescent : baseEnd_4794425 < baseStart_4794425 := by decide
  rcases family_descends (prefixWord ++ tailWord_4794425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4794441 : List Nat := [1, 2, 1, 1, 2, 2, 4, 2, 2, 3, 3]
def baseStart_4794441 : Nat := 118140960795 + 4794441 * 2 ^ 59
def prefixEnd_4794441 : Nat := 4983230072969 + 3 ^ 40 * 4794441 * 2
def baseEnd_4794441 : Nat := 2461852702622981461238273

theorem tailTrace_4794441 : CollatzResearch.WordTrace tailWord_4794441 prefixEnd_4794441 2461852702622981461238273 := by
  unfold tailWord_4794441
  simp only [CollatzResearch.WordTrace]
  refine ⟨174867629223566557177895177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116578419482377704785263451 174867629223566557177895177)
  ·
    refine ⟨131150721917674917883421383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 174867629223566557177895177 131150721917674917883421383)
    ·
      refine ⟨196726082876512376825132075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 131150721917674917883421383 196726082876512376825132075)
      ·
        refine ⟨295089124314768565237698113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 196726082876512376825132075 295089124314768565237698113)
        ·
          refine ⟨221316843236076423928273585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 295089124314768565237698113 221316843236076423928273585)
          ·
            refine ⟨165987632427057317946205189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 221316843236076423928273585 165987632427057317946205189)
            ·
              refine ⟨31122681080073247114913473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 165987632427057317946205189 31122681080073247114913473)
              ·
                refine ⟨23342010810054935336185105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31122681080073247114913473 23342010810054935336185105)
                ·
                  refine ⟨17506508107541201502138829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23342010810054935336185105 17506508107541201502138829)
                  ·
                    refine ⟨6564940540327950563302061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17506508107541201502138829 6564940540327950563302061)
                    ·
                      refine ⟨2461852702622981461238273, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6564940540327950563302061 2461852702622981461238273)
                      ·
                        rfl

theorem cell23_4794441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 4, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 4, 2, 2, 3, 3].length) (baseStart_4794441 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4794441 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4794441 prefixEnd_4794441 := by exact prefixLift 4794441
  have htrace : WordTrace (prefixWord ++ tailWord_4794441) baseStart_4794441 baseEnd_4794441 := by
    simpa [prefixWord, tailWord_4794441, baseEnd_4794441] using wordTrace_append hprefix tailTrace_4794441
  have hstable : (prefixWord ++ tailWord_4794441).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4794441).length < 2 ^ (prefixWord ++ tailWord_4794441).sum := by decide
  have hdescent : baseEnd_4794441 < baseStart_4794441 := by decide
  rcases family_descends (prefixWord ++ tailWord_4794441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4794481 : List Nat := [1, 2, 2, 2, 1, 1, 5, 1, 1, 3, 4]
def baseStart_4794481 : Nat := 118140960795 + 4794481 * 2 ^ 59
def prefixEnd_4794481 : Nat := 4983230072969 + 3 ^ 40 * 4794481 * 2
def baseEnd_4794481 : Nat := 2461873241849161304738089

theorem tailTrace_4794481 : CollatzResearch.WordTrace tailWord_4794481 prefixEnd_4794481 2461873241849161304738089 := by
  unfold tailWord_4794481
  simp only [CollatzResearch.WordTrace]
  refine ⟨174869088143421644009351297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116579392095614429339567531 174869088143421644009351297)
  ·
    refine ⟨131151816107566233007013473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 174869088143421644009351297 131151816107566233007013473)
    ·
      refine ⟨98363862080674674755260105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 131151816107566233007013473 98363862080674674755260105)
      ·
        refine ⟨73772896560506006066445079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 98363862080674674755260105 73772896560506006066445079)
        ·
          refine ⟨110659344840759009099667619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 73772896560506006066445079 110659344840759009099667619)
          ·
            refine ⟨165989017261138513649501429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 110659344840759009099667619 165989017261138513649501429)
            ·
              refine ⟨15561470368231735654640759, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 165989017261138513649501429 15561470368231735654640759)
              ·
                refine ⟨23342205552347603481961139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15561470368231735654640759 23342205552347603481961139)
                ·
                  refine ⟨35013308328521405222941709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23342205552347603481961139 35013308328521405222941709)
                  ·
                    refine ⟨13129990623195526958603141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 35013308328521405222941709 13129990623195526958603141)
                    ·
                      refine ⟨2461873241849161304738089, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13129990623195526958603141 2461873241849161304738089)
                      ·
                        rfl

theorem cell23_4794481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 5, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 5, 1, 1, 3, 4].length) (baseStart_4794481 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4794481 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4794481 prefixEnd_4794481 := by exact prefixLift 4794481
  have htrace : WordTrace (prefixWord ++ tailWord_4794481) baseStart_4794481 baseEnd_4794481 := by
    simpa [prefixWord, tailWord_4794481, baseEnd_4794481] using wordTrace_append hprefix tailTrace_4794481
  have hstable : (prefixWord ++ tailWord_4794481).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4794481).length < 2 ^ (prefixWord ++ tailWord_4794481).sum := by decide
  have hdescent : baseEnd_4794481 < baseStart_4794481 := by decide
  rcases family_descends (prefixWord ++ tailWord_4794481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4794521 : List Nat := [1, 2, 1, 2, 1, 2, 1, 7, 6]
def baseStart_4794521 : Nat := 118140960795 + 4794521 * 2 ^ 59
def prefixEnd_4794521 : Nat := 4983230072969 + 3 ^ 40 * 4794521 * 2
def baseEnd_4794521 : Nat := 273543753452815683137545

theorem tailTrace_4794521 : CollatzResearch.WordTrace tailWord_4794521 prefixEnd_4794521 273543753452815683137545 := by
  unfold tailWord_4794521
  simp only [CollatzResearch.WordTrace]
  refine ⟨174870547063276730840807417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116580364708851153893871611 174870547063276730840807417)
  ·
    refine ⟨131152910297457548130605563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 174870547063276730840807417 131152910297457548130605563)
    ·
      refine ⟨196729365446186322195908345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 131152910297457548130605563 196729365446186322195908345)
      ·
        refine ⟨147547024084639741646931259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 196729365446186322195908345 147547024084639741646931259)
        ·
          refine ⟨221320536126959612470396889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 147547024084639741646931259 221320536126959612470396889)
          ·
            refine ⟨165990402095219709352797667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 221320536126959612470396889 165990402095219709352797667)
            ·
              refine ⟨248985603142829564029196501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 165990402095219709352797667 248985603142829564029196501)
              ·
                refine ⟨5835600073660067906934293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 248985603142829564029196501 5835600073660067906934293)
                ·
                  refine ⟨273543753452815683137545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5835600073660067906934293 273543753452815683137545)
                  ·
                    rfl

theorem cell23_4794521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 7, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 7, 6].length) (baseStart_4794521 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4794521 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4794521 prefixEnd_4794521 := by exact prefixLift 4794521
  have htrace : WordTrace (prefixWord ++ tailWord_4794521) baseStart_4794521 baseEnd_4794521 := by
    simpa [prefixWord, tailWord_4794521, baseEnd_4794521] using wordTrace_append hprefix tailTrace_4794521
  have hstable : (prefixWord ++ tailWord_4794521).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4794521).length < 2 ^ (prefixWord ++ tailWord_4794521).sum := by decide
  have hdescent : baseEnd_4794521 < baseStart_4794521 := by decide
  rcases family_descends (prefixWord ++ tailWord_4794521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4794565 : List Nat := [1, 3, 1, 1, 1, 1, 7, 1, 3, 1, 3]
def baseStart_4794565 : Nat := 118140960795 + 4794565 * 2 ^ 59
def prefixEnd_4794565 : Nat := 4983230072969 + 3 ^ 40 * 4794565 * 2
def baseEnd_4794565 : Nat := 2461916374224138976087703

theorem tailTrace_4794565 : CollatzResearch.WordTrace tailWord_4794565 prefixEnd_4794565 2461916374224138976087703 := by
  unfold tailWord_4794565
  simp only [CollatzResearch.WordTrace]
  refine ⟨174872151875117326355409149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116581434583411550903606099 174872151875117326355409149)
  ·
    refine ⟨65577056953168997383278431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 174872151875117326355409149 65577056953168997383278431)
    ·
      refine ⟨98365585429753496074917647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65577056953168997383278431 98365585429753496074917647)
      ·
        refine ⟨147548378144630244112376471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 98365585429753496074917647 147548378144630244112376471)
        ·
          refine ⟨221322567216945366168564707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 147548378144630244112376471 221322567216945366168564707)
          ·
            refine ⟨331983850825418049252847061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 221322567216945366168564707 331983850825418049252847061)
            ·
              refine ⟨7780871503720735529363603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 331983850825418049252847061 7780871503720735529363603)
              ·
                refine ⟨11671307255581103294045405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7780871503720735529363603 11671307255581103294045405)
                ·
                  refine ⟨4376740220842913735267027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11671307255581103294045405 4376740220842913735267027)
                  ·
                    refine ⟨6565110331264370602900541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4376740220842913735267027 6565110331264370602900541)
                    ·
                      refine ⟨2461916374224138976087703, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6565110331264370602900541 2461916374224138976087703)
                      ·
                        rfl

theorem cell23_4794565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 7, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 7, 1, 3, 1, 3].length) (baseStart_4794565 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4794565 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4794565 prefixEnd_4794565 := by exact prefixLift 4794565
  have htrace : WordTrace (prefixWord ++ tailWord_4794565) baseStart_4794565 baseEnd_4794565 := by
    simpa [prefixWord, tailWord_4794565, baseEnd_4794565] using wordTrace_append hprefix tailTrace_4794565
  have hstable : (prefixWord ++ tailWord_4794565).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4794565).length < 2 ^ (prefixWord ++ tailWord_4794565).sum := by decide
  have hdescent : baseEnd_4794565 < baseStart_4794565 := by decide
  rcases family_descends (prefixWord ++ tailWord_4794565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4794655 : List Nat := [1, 1, 2, 4, 3, 1, 2, 2, 1, 3, 3]
def baseStart_4794655 : Nat := 118140960795 + 4794655 * 2 ^ 59
def prefixEnd_4794655 : Nat := 4983230072969 + 3 ^ 40 * 4794655 * 2
def baseEnd_4794655 : Nat := 2461962587483043623962289

theorem tailTrace_4794655 : CollatzResearch.WordTrace tailWord_4794655 prefixEnd_4794655 2461962587483043623962289 := by
  unfold tailWord_4794655
  simp only [CollatzResearch.WordTrace]
  refine ⟨174875434444791271726185419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116583622963194181150790279 174875434444791271726185419)
  ·
    refine ⟨262313151667186907589278129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 174875434444791271726185419 262313151667186907589278129)
    ·
      refine ⟨196734863750390180691958597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 262313151667186907589278129 196734863750390180691958597)
      ·
        refine ⟨36887786953198158879742237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 196734863750390180691958597 36887786953198158879742237)
        ·
          refine ⟨13832920107449309579903339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 36887786953198158879742237 13832920107449309579903339)
          ·
            refine ⟨20749380161173964369855009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13832920107449309579903339 20749380161173964369855009)
            ·
              refine ⟨15562035120880473277391257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20749380161173964369855009 15562035120880473277391257)
              ·
                refine ⟨11671526340660354958043443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15562035120880473277391257 11671526340660354958043443)
                ·
                  refine ⟨17507289510990532437065165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11671526340660354958043443 17507289510990532437065165)
                  ·
                    refine ⟨6565233566621449663899437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17507289510990532437065165 6565233566621449663899437)
                    ·
                      refine ⟨2461962587483043623962289, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6565233566621449663899437 2461962587483043623962289)
                      ·
                        rfl

theorem cell23_4794655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 2, 2, 1, 3, 3].length) (baseStart_4794655 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4794655 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4794655 prefixEnd_4794655 := by exact prefixLift 4794655
  have htrace : WordTrace (prefixWord ++ tailWord_4794655) baseStart_4794655 baseEnd_4794655 := by
    simpa [prefixWord, tailWord_4794655, baseEnd_4794655] using wordTrace_append hprefix tailTrace_4794655
  have hstable : (prefixWord ++ tailWord_4794655).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4794655).length < 2 ^ (prefixWord ++ tailWord_4794655).sum := by decide
  have hdescent : baseEnd_4794655 < baseStart_4794655 := by decide
  rcases family_descends (prefixWord ++ tailWord_4794655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4794656 : List Nat := [2, 1, 1, 5, 2, 2, 2, 3, 1, 2, 2]
def baseStart_4794656 : Nat := 118140960795 + 4794656 * 2 ^ 59
def prefixEnd_4794656 : Nat := 4983230072969 + 3 ^ 40 * 4794656 * 2
def baseEnd_4794656 : Nat := 2461963100963698120049785

theorem tailTrace_4794656 : CollatzResearch.WordTrace tailWord_4794656 prefixEnd_4794656 2461963100963698120049785 := by
  unfold tailWord_4794656
  simp only [CollatzResearch.WordTrace]
  refine ⟨87437735458893824448485911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116583647278525099264647881 87437735458893824448485911)
  ·
    refine ⟨131156603188340736672728867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87437735458893824448485911 131156603188340736672728867)
    ·
      refine ⟨196734904782511105009093301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 131156603188340736672728867 196734904782511105009093301)
      ·
        refine ⟨18443897323360416094602497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 196734904782511105009093301 18443897323360416094602497)
        ·
          refine ⟨13832922992520312070951873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18443897323360416094602497 13832922992520312070951873)
          ·
            refine ⟨10374692244390234053213905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13832922992520312070951873 10374692244390234053213905)
            ·
              refine ⟨7781019183292675539910429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10374692244390234053213905 7781019183292675539910429)
              ·
                refine ⟨2917882193734753327466411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7781019183292675539910429 2917882193734753327466411)
                ·
                  refine ⟨4376823290602129991199617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2917882193734753327466411 4376823290602129991199617)
                  ·
                    refine ⟨3282617467951597493399713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4376823290602129991199617 3282617467951597493399713)
                    ·
                      refine ⟨2461963100963698120049785, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3282617467951597493399713 2461963100963698120049785)
                      ·
                        rfl

theorem cell23_4794656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 2, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 2, 2, 3, 1, 2, 2].length) (baseStart_4794656 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4794656 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4794656 prefixEnd_4794656 := by exact prefixLift 4794656
  have htrace : WordTrace (prefixWord ++ tailWord_4794656) baseStart_4794656 baseEnd_4794656 := by
    simpa [prefixWord, tailWord_4794656, baseEnd_4794656] using wordTrace_append hprefix tailTrace_4794656
  have hstable : (prefixWord ++ tailWord_4794656).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4794656).length < 2 ^ (prefixWord ++ tailWord_4794656).sum := by decide
  have hdescent : baseEnd_4794656 < baseStart_4794656 := by decide
  rcases family_descends (prefixWord ++ tailWord_4794656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4794666 : List Nat := [3, 1, 4, 2, 3, 1, 1, 2, 2, 4]
def baseStart_4794666 : Nat := 118140960795 + 4794666 * 2 ^ 59
def prefixEnd_4794666 : Nat := 4983230072969 + 3 ^ 40 * 4794666 * 2
def baseEnd_4794666 : Nat := 820656078590081026974913

theorem tailTrace_4794666 : CollatzResearch.WordTrace tailWord_4794666 prefixEnd_4794666 820656078590081026974913 := by
  unfold tailWord_4794666
  simp only [CollatzResearch.WordTrace]
  refine ⟨43718958911937855151208963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 116583890431834280403223901 43718958911937855151208963)
  ·
    refine ⟨65578438367906782726813445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43718958911937855151208963 65578438367906782726813445)
    ·
      refine ⟨12295957193982521761277521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 65578438367906782726813445 12295957193982521761277521)
      ·
        refine ⟨9221967895486891320958141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12295957193982521761277521 9221967895486891320958141)
        ·
          refine ⟨3458237960807584245359303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9221967895486891320958141 3458237960807584245359303)
          ·
            refine ⟨5187356941211376368038955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3458237960807584245359303 5187356941211376368038955)
            ·
              refine ⟨7781035411817064552058433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5187356941211376368038955 7781035411817064552058433)
              ·
                refine ⟨5835776558862798414043825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7781035411817064552058433 5835776558862798414043825)
                ·
                  refine ⟨4376832419147098810532869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5835776558862798414043825 4376832419147098810532869)
                  ·
                    refine ⟨820656078590081026974913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4376832419147098810532869 820656078590081026974913)
                    ·
                      rfl

theorem cell23_4794666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 3, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 3, 1, 1, 2, 2, 4].length) (baseStart_4794666 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4794666 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4794666 prefixEnd_4794666 := by exact prefixLift 4794666
  have htrace : WordTrace (prefixWord ++ tailWord_4794666) baseStart_4794666 baseEnd_4794666 := by
    simpa [prefixWord, tailWord_4794666, baseEnd_4794666] using wordTrace_append hprefix tailTrace_4794666
  have hstable : (prefixWord ++ tailWord_4794666).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4794666).length < 2 ^ (prefixWord ++ tailWord_4794666).sum := by decide
  have hdescent : baseEnd_4794666 < baseStart_4794666 := by decide
  rcases family_descends (prefixWord ++ tailWord_4794666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4794689 : List Nat := [1, 2, 5, 2, 2, 2, 1, 1, 1, 3, 3]
def baseStart_4794689 : Nat := 118140960795 + 4794689 * 2 ^ 59
def prefixEnd_4794689 : Nat := 4983230072969 + 3 ^ 40 * 4794689 * 2
def baseEnd_4794689 : Nat := 2461980045825296490937133

theorem tailTrace_4794689 : CollatzResearch.WordTrace tailWord_4794689 prefixEnd_4794689 2461980045825296490937133 := by
  unfold tailWord_4794689
  simp only [CollatzResearch.WordTrace]
  refine ⟨174876674526668095532923121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116584449684445397021948747 174876674526668095532923121)
  ·
    refine ⟨131157505895001071649692341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 174876674526668095532923121 131157505895001071649692341)
    ·
      refine ⟨12296016177656350467158657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 131157505895001071649692341 12296016177656350467158657)
      ·
        refine ⟨9222012133242262850368993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12296016177656350467158657 9222012133242262850368993)
        ·
          refine ⟨6916509099931697137776745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9222012133242262850368993 6916509099931697137776745)
          ·
            refine ⟨5187381824948772853332559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6916509099931697137776745 5187381824948772853332559)
            ·
              refine ⟨7781072737423159279998839, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5187381824948772853332559 7781072737423159279998839)
              ·
                refine ⟨11671609106134738919998259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7781072737423159279998839 11671609106134738919998259)
                ·
                  refine ⟨17507413659202108379997389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11671609106134738919998259 17507413659202108379997389)
                  ·
                    refine ⟨6565280122200790642499021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17507413659202108379997389 6565280122200790642499021)
                    ·
                      refine ⟨2461980045825296490937133, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6565280122200790642499021 2461980045825296490937133)
                      ·
                        rfl

theorem cell23_4794689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 2, 2, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 2, 2, 1, 1, 1, 3, 3].length) (baseStart_4794689 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4794689 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4794689 prefixEnd_4794689 := by exact prefixLift 4794689
  have htrace : WordTrace (prefixWord ++ tailWord_4794689) baseStart_4794689 baseEnd_4794689 := by
    simpa [prefixWord, tailWord_4794689, baseEnd_4794689] using wordTrace_append hprefix tailTrace_4794689
  have hstable : (prefixWord ++ tailWord_4794689).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4794689).length < 2 ^ (prefixWord ++ tailWord_4794689).sum := by decide
  have hdescent : baseEnd_4794689 < baseStart_4794689 := by decide
  rcases family_descends (prefixWord ++ tailWord_4794689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4794748 : List Nat := [2, 2, 2, 1, 1, 1, 2, 4, 1, 7]
def baseStart_4794748 : Nat := 118140960795 + 4794748 * 2 ^ 59
def prefixEnd_4794748 : Nat := 4983230072969 + 3 ^ 40 * 4794748 * 2
def baseEnd_4794748 : Nat := 820670113727970586699787

theorem tailTrace_4794748 : CollatzResearch.WordTrace tailWord_4794748 prefixEnd_4794748 820670113727970586699787 := by
  unfold tailWord_4794748
  simp only [CollatzResearch.WordTrace]
  refine ⟨87439413216727174304660449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116585884288969565739547265 87439413216727174304660449)
  ·
    refine ⟨65579559912545380728495337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 87439413216727174304660449 65579559912545380728495337)
    ·
      refine ⟨49184669934409035546371503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 65579559912545380728495337 49184669934409035546371503)
      ·
        refine ⟨73777004901613553319557255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49184669934409035546371503 73777004901613553319557255)
        ·
          refine ⟨110665507352420329979335883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 73777004901613553319557255 110665507352420329979335883)
          ·
            refine ⟨165998261028630494969003825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 110665507352420329979335883 165998261028630494969003825)
            ·
              refine ⟨124498695771472871226752869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 165998261028630494969003825 124498695771472871226752869)
              ·
                refine ⟨23343505457151163355016163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 124498695771472871226752869 23343505457151163355016163)
                ·
                  refine ⟨35015258185726745032524245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23343505457151163355016163 35015258185726745032524245)
                  ·
                    refine ⟨820670113727970586699787, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 35015258185726745032524245 820670113727970586699787)
                    ·
                      rfl

theorem cell23_4794748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 2, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 2, 4, 1, 7].length) (baseStart_4794748 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4794748 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4794748 prefixEnd_4794748 := by exact prefixLift 4794748
  have htrace : WordTrace (prefixWord ++ tailWord_4794748) baseStart_4794748 baseEnd_4794748 := by
    simpa [prefixWord, tailWord_4794748, baseEnd_4794748] using wordTrace_append hprefix tailTrace_4794748
  have hstable : (prefixWord ++ tailWord_4794748).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4794748).length < 2 ^ (prefixWord ++ tailWord_4794748).sum := by decide
  have hdescent : baseEnd_4794748 < baseStart_4794748 := by decide
  rcases family_descends (prefixWord ++ tailWord_4794748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4794792 : List Nat := [2, 1, 6, 1, 1, 1, 2, 1, 1, 2, 5]
def baseStart_4794792 : Nat := 118140960795 + 4794792 * 2 ^ 59
def prefixEnd_4794792 : Nat := 4983230072969 + 3 ^ 40 * 4794792 * 2
def baseEnd_4794792 : Nat := 2462032934332709587949159

theorem tailTrace_4794792 : CollatzResearch.WordTrace tailWord_4794792 prefixEnd_4794792 2462032934332709587949159 := by
  unfold tailWord_4794792
  simp only [CollatzResearch.WordTrace]
  refine ⟨87440215622647472061961315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116586954163529962749281753 87440215622647472061961315)
  ·
    refine ⟨131160323433971208092941973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87440215622647472061961315 131160323433971208092941973)
    ·
      refine ⟨6148140160967400379356655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 131160323433971208092941973 6148140160967400379356655)
      ·
        refine ⟨9222210241451100569034983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6148140160967400379356655 9222210241451100569034983)
        ·
          refine ⟨13833315362176650853552475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9222210241451100569034983 13833315362176650853552475)
          ·
            refine ⟨20749973043264976280328713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13833315362176650853552475 20749973043264976280328713)
            ·
              refine ⟨15562479782448732210246535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20749973043264976280328713 15562479782448732210246535)
              ·
                refine ⟨23343719673673098315369803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15562479782448732210246535 23343719673673098315369803)
                ·
                  refine ⟨35015579510509647473054705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23343719673673098315369803 35015579510509647473054705)
                  ·
                    refine ⟨26261684632882235604791029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 35015579510509647473054705 26261684632882235604791029)
                    ·
                      refine ⟨2462032934332709587949159, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26261684632882235604791029 2462032934332709587949159)
                      ·
                        rfl

theorem cell23_4794792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 2, 1, 1, 2, 5].length) (baseStart_4794792 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4794792 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4794792 prefixEnd_4794792 := by exact prefixLift 4794792
  have htrace : WordTrace (prefixWord ++ tailWord_4794792) baseStart_4794792 baseEnd_4794792 := by
    simpa [prefixWord, tailWord_4794792, baseEnd_4794792] using wordTrace_append hprefix tailTrace_4794792
  have hstable : (prefixWord ++ tailWord_4794792).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4794792).length < 2 ^ (prefixWord ++ tailWord_4794792).sum := by decide
  have hdescent : baseEnd_4794792 < baseStart_4794792 := by decide
  rcases family_descends (prefixWord ++ tailWord_4794792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4794802 : List Nat := [3, 2, 1, 1, 1, 1, 5, 1, 2, 4, 2]
def baseStart_4794802 : Nat := 118140960795 + 4794802 * 2 ^ 59
def prefixEnd_4794802 : Nat := 4983230072969 + 3 ^ 40 * 4794802 * 2
def baseEnd_4794802 : Nat := 2462038069139254548824113

theorem tailTrace_4794802 : CollatzResearch.WordTrace tailWord_4794802 prefixEnd_4794802 2462038069139254548824113 := by
  unfold tailWord_4794802
  simp only [CollatzResearch.WordTrace]
  refine ⟨43720198993814678957946665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 116587197316839143887857773 43720198993814678957946665)
  ·
    refine ⟨32790149245361009218459999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43720198993814678957946665 32790149245361009218459999)
    ·
      refine ⟨49185223868041513827689999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32790149245361009218459999 49185223868041513827689999)
      ·
        refine ⟨73777835802062270741534999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49185223868041513827689999 73777835802062270741534999)
        ·
          refine ⟨110666753703093406112302499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 73777835802062270741534999 110666753703093406112302499)
          ·
            refine ⟨166000130554640109168453749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 110666753703093406112302499 166000130554640109168453749)
            ·
              refine ⟨15562512239497510234542539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 166000130554640109168453749 15562512239497510234542539)
              ·
                refine ⟨23343768359246265351813809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15562512239497510234542539 23343768359246265351813809)
                ·
                  refine ⟨17507826269434699013860357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23343768359246265351813809 17507826269434699013860357)
                  ·
                    refine ⟨3282717425519006065098817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17507826269434699013860357 3282717425519006065098817)
                    ·
                      refine ⟨2462038069139254548824113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3282717425519006065098817 2462038069139254548824113)
                      ·
                        rfl

theorem cell23_4794802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 5, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 5, 1, 2, 4, 2].length) (baseStart_4794802 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4794802 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4794802 prefixEnd_4794802 := by exact prefixLift 4794802
  have htrace : WordTrace (prefixWord ++ tailWord_4794802) baseStart_4794802 baseEnd_4794802 := by
    simpa [prefixWord, tailWord_4794802, baseEnd_4794802] using wordTrace_append hprefix tailTrace_4794802
  have hstable : (prefixWord ++ tailWord_4794802).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4794802).length < 2 ^ (prefixWord ++ tailWord_4794802).sum := by decide
  have hdescent : baseEnd_4794802 < baseStart_4794802 := by decide
  rcases family_descends (prefixWord ++ tailWord_4794802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4794808 : List Nat := [2, 1, 2, 1, 2, 2, 1, 2, 10]
def baseStart_4794808 : Nat := 118140960795 + 4794808 * 2 ^ 59
def prefixEnd_4794808 : Nat := 4983230072969 + 3 ^ 40 * 4794808 * 2
def baseEnd_4794808 : Nat := 273560127780353502816565

theorem tailTrace_4794808 : CollatzResearch.WordTrace tailWord_4794808 prefixEnd_4794808 273560127780353502816565 := by
  unfold tailWord_4794808
  simp only [CollatzResearch.WordTrace]
  refine ⟨87440507406618489428252539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116587343208824652571003385 87440507406618489428252539)
  ·
    refine ⟨131160761109927734142378809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87440507406618489428252539 131160761109927734142378809)
    ·
      refine ⟨98370570832445800606784107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 131160761109927734142378809 98370570832445800606784107)
      ·
        refine ⟨147555856248668700910176161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 98370570832445800606784107 147555856248668700910176161)
        ·
          refine ⟨110666892186501525682632121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 147555856248668700910176161 110666892186501525682632121)
          ·
            refine ⟨83000169139876144261974091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 110666892186501525682632121 83000169139876144261974091)
            ·
              refine ⟨124500253709814216392961137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 83000169139876144261974091 124500253709814216392961137)
              ·
                refine ⟨93375190282360662294720853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 124500253709814216392961137 93375190282360662294720853)
                ·
                  refine ⟨273560127780353502816565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 93375190282360662294720853 273560127780353502816565)
                  ·
                    rfl

theorem cell23_4794808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 1, 2, 10].length) (baseStart_4794808 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4794808 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4794808 prefixEnd_4794808 := by exact prefixLift 4794808
  have htrace : WordTrace (prefixWord ++ tailWord_4794808) baseStart_4794808 baseEnd_4794808 := by
    simpa [prefixWord, tailWord_4794808, baseEnd_4794808] using wordTrace_append hprefix tailTrace_4794808
  have hstable : (prefixWord ++ tailWord_4794808).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4794808).length < 2 ^ (prefixWord ++ tailWord_4794808).sum := by decide
  have hdescent : baseEnd_4794808 < baseStart_4794808 := by decide
  rcases family_descends (prefixWord ++ tailWord_4794808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4794812 : List Nat := [2, 2, 2, 4, 1, 1, 1, 1, 5, 4]
def baseStart_4794812 : Nat := 118140960795 + 4794812 * 2 ^ 59
def prefixEnd_4794812 : Nat := 4983230072969 + 3 ^ 40 * 4794812 * 2
def baseEnd_4794812 : Nat := 820681067981933169899689

theorem tailTrace_4794812 : CollatzResearch.WordTrace tailWord_4794812 prefixEnd_4794812 820681067981933169899689 := by
  unfold tailWord_4794812
  simp only [CollatzResearch.WordTrace]
  refine ⟨87440580352611243769825345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116587440470148325026433793 87440580352611243769825345)
  ·
    refine ⟨65580435264458432827369009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 87440580352611243769825345 65580435264458432827369009)
    ·
      refine ⟨49185326448343824620526757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 65580435264458432827369009 49185326448343824620526757)
      ·
        refine ⟨9222248709064467116348767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 49185326448343824620526757 9222248709064467116348767)
        ·
          refine ⟨13833373063596700674523151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9222248709064467116348767 13833373063596700674523151)
          ·
            refine ⟨20750059595395051011784727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13833373063596700674523151 20750059595395051011784727)
            ·
              refine ⟨31125089393092576517677091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20750059595395051011784727 31125089393092576517677091)
              ·
                refine ⟨46687634089638864776515637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31125089393092576517677091 46687634089638864776515637)
                ·
                  refine ⟨4376965695903643572798341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 46687634089638864776515637 4376965695903643572798341)
                  ·
                    refine ⟨820681067981933169899689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4376965695903643572798341 820681067981933169899689)
                    ·
                      rfl

theorem cell23_4794812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 1, 1, 5, 4].length) (baseStart_4794812 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4794812 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4794812 prefixEnd_4794812 := by exact prefixLift 4794812
  have htrace : WordTrace (prefixWord ++ tailWord_4794812) baseStart_4794812 baseEnd_4794812 := by
    simpa [prefixWord, tailWord_4794812, baseEnd_4794812] using wordTrace_append hprefix tailTrace_4794812
  have hstable : (prefixWord ++ tailWord_4794812).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4794812).length < 2 ^ (prefixWord ++ tailWord_4794812).sum := by decide
  have hdescent : baseEnd_4794812 < baseStart_4794812 := by decide
  rcases family_descends (prefixWord ++ tailWord_4794812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4794845 : List Nat := [1, 4, 3, 1, 1, 1, 1, 1, 1, 1, 8]
def baseStart_4794845 : Nat := 118140960795 + 4794845 * 2 ^ 59
def prefixEnd_4794845 : Nat := 4983230072969 + 3 ^ 40 * 4794845 * 2
def baseEnd_4794845 : Nat := 2462060148807397880586415

theorem tailTrace_4794845 : CollatzResearch.WordTrace tailWord_4794845 prefixEnd_4794845 2462060148807397880586415 := by
  unfold tailWord_4794845
  simp only [CollatzResearch.WordTrace]
  refine ⟨174882364314102934175601989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116588242876068622783734659 174882364314102934175601989)
  ·
    refine ⟨32790443308894300157925373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 174882364314102934175601989 32790443308894300157925373)
    ·
      refine ⟨12296416240835362559222015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32790443308894300157925373 12296416240835362559222015)
      ·
        refine ⟨18444624361253043838833023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12296416240835362559222015 18444624361253043838833023)
        ·
          refine ⟨27666936541879565758249535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18444624361253043838833023 27666936541879565758249535)
          ·
            refine ⟨41500404812819348637374303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27666936541879565758249535 41500404812819348637374303)
            ·
              refine ⟨62250607219229022956061455, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41500404812819348637374303 62250607219229022956061455)
              ·
                refine ⟨93375910828843534434092183, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 62250607219229022956061455 93375910828843534434092183)
                ·
                  refine ⟨140063866243265301651138275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 93375910828843534434092183 140063866243265301651138275)
                  ·
                    refine ⟨210095799364897952476707413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 140063866243265301651138275 210095799364897952476707413)
                    ·
                      refine ⟨2462060148807397880586415, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 210095799364897952476707413 2462060148807397880586415)
                      ·
                        rfl

theorem cell23_4794845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 1, 1, 1, 1, 8].length) (baseStart_4794845 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4794845 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4794845 prefixEnd_4794845 := by exact prefixLift 4794845
  have htrace : WordTrace (prefixWord ++ tailWord_4794845) baseStart_4794845 baseEnd_4794845 := by
    simpa [prefixWord, tailWord_4794845, baseEnd_4794845] using wordTrace_append hprefix tailTrace_4794845
  have hstable : (prefixWord ++ tailWord_4794845).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4794845).length < 2 ^ (prefixWord ++ tailWord_4794845).sum := by decide
  have hdescent : baseEnd_4794845 < baseStart_4794845 := by decide
  rcases family_descends (prefixWord ++ tailWord_4794845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4794872 : List Nat := [2, 1, 2, 1, 1, 4, 4, 2, 1, 5]
def baseStart_4794872 : Nat := 118140960795 + 4794872 * 2 ^ 59
def prefixEnd_4794872 : Nat := 4983230072969 + 3 ^ 40 * 4794872 * 2
def baseEnd_4794872 : Nat := 820691337595023091649597

theorem tailTrace_4794872 : CollatzResearch.WordTrace tailWord_4794872 prefixEnd_4794872 820691337595023091649597 := by
  unfold tailWord_4794872
  simp only [CollatzResearch.WordTrace]
  refine ⟨87441674542502558893417435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116588899390003411857889913 87441674542502558893417435)
  ·
    refine ⟨131162511813753838340126153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87441674542502558893417435 131162511813753838340126153)
    ·
      refine ⟨98371883860315378755094615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 131162511813753838340126153 98371883860315378755094615)
      ·
        refine ⟨147557825790473068132641923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 98371883860315378755094615 147557825790473068132641923)
        ·
          refine ⟨221336738685709602198962885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 147557825790473068132641923 221336738685709602198962885)
          ·
            refine ⟨41500638503570550412305541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 221336738685709602198962885 41500638503570550412305541)
            ·
              refine ⟨7781369719419478202307289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 41500638503570550412305541 7781369719419478202307289)
              ·
                refine ⟨5836027289564608651730467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7781369719419478202307289 5836027289564608651730467)
                ·
                  refine ⟨8754040934346912977595701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5836027289564608651730467 8754040934346912977595701)
                  ·
                    refine ⟨820691337595023091649597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8754040934346912977595701 820691337595023091649597)
                    ·
                      rfl

theorem cell23_4794872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 4, 2, 1, 5].length) (baseStart_4794872 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4794872 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4794872 prefixEnd_4794872 := by exact prefixLift 4794872
  have htrace : WordTrace (prefixWord ++ tailWord_4794872) baseStart_4794872 baseEnd_4794872 := by
    simpa [prefixWord, tailWord_4794872, baseEnd_4794872] using wordTrace_append hprefix tailTrace_4794872
  have hstable : (prefixWord ++ tailWord_4794872).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4794872).length < 2 ^ (prefixWord ++ tailWord_4794872).sum := by decide
  have hdescent : baseEnd_4794872 < baseStart_4794872 := by decide
  rcases family_descends (prefixWord ++ tailWord_4794872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4794885 : List Nat := [1, 3, 1, 1, 2, 2, 2, 4, 1, 6]
def baseStart_4794885 : Nat := 118140960795 + 4794885 * 2 ^ 59
def prefixEnd_4794885 : Nat := 4983230072969 + 3 ^ 40 * 4794885 * 2
def baseEnd_4794885 : Nat := 820693562677859241362077

theorem tailTrace_4794885 : CollatzResearch.WordTrace tailWord_4794885 prefixEnd_4794885 820693562677859241362077 := by
  unfold tailWord_4794885
  simp only [CollatzResearch.WordTrace]
  refine ⟨174883823233958021007058109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116589215489305347338038739 174883823233958021007058109)
  ·
    refine ⟨65581433712734257877646791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 174883823233958021007058109 65581433712734257877646791)
    ·
      refine ⟨98372150569101386816470187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65581433712734257877646791 98372150569101386816470187)
      ·
        refine ⟨147558225853652080224705281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 98372150569101386816470187 147558225853652080224705281)
        ·
          refine ⟨110668669390239060168528961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 147558225853652080224705281 110668669390239060168528961)
          ·
            refine ⟨83001502042679295126396721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 110668669390239060168528961 83001502042679295126396721)
            ·
              refine ⟨62251126532009471344797541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 83001502042679295126396721 62251126532009471344797541)
              ·
                refine ⟨11672086224751775877149539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 62251126532009471344797541 11672086224751775877149539)
                ·
                  refine ⟨17508129337127663815724309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11672086224751775877149539 17508129337127663815724309)
                  ·
                    refine ⟨820693562677859241362077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17508129337127663815724309 820693562677859241362077)
                    ·
                      rfl

theorem cell23_4794885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 2, 4, 1, 6].length) (baseStart_4794885 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4794885 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4794885 prefixEnd_4794885 := by exact prefixLift 4794885
  have htrace : WordTrace (prefixWord ++ tailWord_4794885) baseStart_4794885 baseEnd_4794885 := by
    simpa [prefixWord, tailWord_4794885, baseEnd_4794885] using wordTrace_append hprefix tailTrace_4794885
  have hstable : (prefixWord ++ tailWord_4794885).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4794885).length < 2 ^ (prefixWord ++ tailWord_4794885).sum := by decide
  have hdescent : baseEnd_4794885 < baseStart_4794885 := by decide
  rcases family_descends (prefixWord ++ tailWord_4794885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4794895 : List Nat := [1, 1, 2, 1, 1, 1, 2, 7, 1, 1, 5]
def baseStart_4794895 : Nat := 118140960795 + 4794895 * 2 ^ 59
def prefixEnd_4794895 : Nat := 4983230072969 + 3 ^ 40 * 4794895 * 2
def baseEnd_4794895 : Nat := 2462085822840122684961185

theorem tailTrace_4794895 : CollatzResearch.WordTrace tailWord_4794895 prefixEnd_4794895 2462085822840122684961185 := by
  unfold tailWord_4794895
  simp only [CollatzResearch.WordTrace]
  refine ⟨174884187963921792714922139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116589458642614528476614759 174884187963921792714922139)
  ·
    refine ⟨262326281945882689072383209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 174884187963921792714922139 262326281945882689072383209)
    ·
      refine ⟨196744711459412016804287407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 262326281945882689072383209 196744711459412016804287407)
      ·
        refine ⟨295117067189118025206431111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 196744711459412016804287407 295117067189118025206431111)
        ·
          refine ⟨442675600783677037809646667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 295117067189118025206431111 442675600783677037809646667)
          ·
            refine ⟨664013401175515556714470001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 442675600783677037809646667 664013401175515556714470001)
            ·
              refine ⟨498010050881636667535852501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 664013401175515556714470001 498010050881636667535852501)
              ·
                refine ⟨11672110567538359395371543, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 498010050881636667535852501 11672110567538359395371543)
                ·
                  refine ⟨17508165851307539093057315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11672110567538359395371543 17508165851307539093057315)
                  ·
                    refine ⟨26262248776961308639585973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17508165851307539093057315 26262248776961308639585973)
                    ·
                      refine ⟨2462085822840122684961185, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26262248776961308639585973 2462085822840122684961185)
                      ·
                        rfl

theorem cell23_4794895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 7, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 7, 1, 1, 5].length) (baseStart_4794895 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4794895 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4794895 prefixEnd_4794895 := by exact prefixLift 4794895
  have htrace : WordTrace (prefixWord ++ tailWord_4794895) baseStart_4794895 baseEnd_4794895 := by
    simpa [prefixWord, tailWord_4794895, baseEnd_4794895] using wordTrace_append hprefix tailTrace_4794895
  have hstable : (prefixWord ++ tailWord_4794895).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4794895).length < 2 ^ (prefixWord ++ tailWord_4794895).sum := by decide
  have hdescent : baseEnd_4794895 < baseStart_4794895 := by decide
  rcases family_descends (prefixWord ++ tailWord_4794895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4794903 : List Nat := [1, 1, 3, 6, 1, 2, 1, 1, 3, 1, 3]
def baseStart_4794903 : Nat := 118140960795 + 4794903 * 2 ^ 59
def prefixEnd_4794903 : Nat := 4983230072969 + 3 ^ 40 * 4794903 * 2
def baseEnd_4794903 : Nat := 2462089930685358653661149

theorem tailTrace_4794903 : CollatzResearch.WordTrace tailWord_4794903 prefixEnd_4794903 2462089930685358653661149 := by
  unfold tailWord_4794903
  simp only [CollatzResearch.WordTrace]
  refine ⟨174884479747892810081213363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116589653165261873387475575 174884479747892810081213363)
  ·
    refine ⟨262326719621839215121820045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 174884479747892810081213363 262326719621839215121820045)
    ·
      refine ⟨98372519858189705670682517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 262326719621839215121820045 98372519858189705670682517)
      ·
        refine ⟨4611211868352642453313243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 98372519858189705670682517 4611211868352642453313243)
        ·
          refine ⟨6916817802528963679969865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4611211868352642453313243 6916817802528963679969865)
          ·
            refine ⟨5187613351896722759977399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6916817802528963679969865 5187613351896722759977399)
            ·
              refine ⟨7781420027845084139966099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5187613351896722759977399 7781420027845084139966099)
              ·
                refine ⟨11672130041767626209949149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7781420027845084139966099 11672130041767626209949149)
                ·
                  refine ⟨4377048765662859828730931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11672130041767626209949149 4377048765662859828730931)
                  ·
                    refine ⟨6565573148494289743096397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4377048765662859828730931 6565573148494289743096397)
                    ·
                      refine ⟨2462089930685358653661149, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6565573148494289743096397 2462089930685358653661149)
                      ·
                        rfl

theorem cell23_4794903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 1, 2, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 1, 2, 1, 1, 3, 1, 3].length) (baseStart_4794903 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4794903 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4794903 prefixEnd_4794903 := by exact prefixLift 4794903
  have htrace : WordTrace (prefixWord ++ tailWord_4794903) baseStart_4794903 baseEnd_4794903 := by
    simpa [prefixWord, tailWord_4794903, baseEnd_4794903] using wordTrace_append hprefix tailTrace_4794903
  have hstable : (prefixWord ++ tailWord_4794903).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4794903).length < 2 ^ (prefixWord ++ tailWord_4794903).sum := by decide
  have hdescent : baseEnd_4794903 < baseStart_4794903 := by decide
  rcases family_descends (prefixWord ++ tailWord_4794903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4794905 : List Nat := [1, 2, 1, 2, 1, 1, 2, 4, 3, 2, 4]
def baseStart_4794905 : Nat := 118140960795 + 4794905 * 2 ^ 59
def prefixEnd_4794905 : Nat := 4983230072969 + 3 ^ 40 * 4794905 * 2
def baseEnd_4794905 : Nat := 2462090957646667645836139

theorem tailTrace_4794905 : CollatzResearch.WordTrace tailWord_4794905 prefixEnd_4794905 2462090957646667645836139 := by
  unfold tailWord_4794905
  simp only [CollatzResearch.WordTrace]
  refine ⟨174884552693885564422786169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116589701795923709615190779 174884552693885564422786169)
  ·
    refine ⟨131163414520414173317089627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 174884552693885564422786169 131163414520414173317089627)
    ·
      refine ⟨196745121780621259975634441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 131163414520414173317089627 196745121780621259975634441)
      ·
        refine ⟨147558841335465944981725831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 196745121780621259975634441 147558841335465944981725831)
        ·
          refine ⟨221338262003198917472588747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 147558841335465944981725831 221338262003198917472588747)
          ·
            refine ⟨332007393004798376208883121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 221338262003198917472588747 332007393004798376208883121)
            ·
              refine ⟨249005544753598782156662341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 332007393004798376208883121 249005544753598782156662341)
              ·
                refine ⟨46688539641299771654374189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 249005544753598782156662341 46688539641299771654374189)
                ·
                  refine ⟨17508202365487414370390321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 46688539641299771654374189 17508202365487414370390321)
                  ·
                    refine ⟨13131151774115560777792741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17508202365487414370390321 13131151774115560777792741)
                    ·
                      refine ⟨2462090957646667645836139, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13131151774115560777792741 2462090957646667645836139)
                      ·
                        rfl

theorem cell23_4794905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 4, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 4, 3, 2, 4].length) (baseStart_4794905 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4794905 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4794905 prefixEnd_4794905 := by exact prefixLift 4794905
  have htrace : WordTrace (prefixWord ++ tailWord_4794905) baseStart_4794905 baseEnd_4794905 := by
    simpa [prefixWord, tailWord_4794905, baseEnd_4794905] using wordTrace_append hprefix tailTrace_4794905
  have hstable : (prefixWord ++ tailWord_4794905).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4794905).length < 2 ^ (prefixWord ++ tailWord_4794905).sum := by decide
  have hdescent : baseEnd_4794905 < baseStart_4794905 := by decide
  rcases family_descends (prefixWord ++ tailWord_4794905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4794915 : List Nat := [1, 1, 1, 4, 4, 1, 1, 10]
def baseStart_4794915 : Nat := 118140960795 + 4794915 * 2 ^ 59
def prefixEnd_4794915 : Nat := 4983230072969 + 3 ^ 40 * 4794915 * 2
def baseEnd_4794915 : Nat := 91188744164933800248559

theorem tailTrace_4794915 : CollatzResearch.WordTrace tailWord_4794915 prefixEnd_4794915 91188744164933800248559 := by
  unfold tailWord_4794915
  simp only [CollatzResearch.WordTrace]
  refine ⟨174884917423849336130650199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116589944949232890753766799 174884917423849336130650199)
  ·
    refine ⟨262327376135774004195975299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 174884917423849336130650199 262327376135774004195975299)
    ·
      refine ⟨393491064203661006293962949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 262327376135774004195975299 393491064203661006293962949)
      ·
        refine ⟨73779574538186438680118053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 393491064203661006293962949 73779574538186438680118053)
        ·
          refine ⟨13833670225909957252522135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 73779574538186438680118053 13833670225909957252522135)
          ·
            refine ⟨20750505338864935878783203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13833670225909957252522135 20750505338864935878783203)
            ·
              refine ⟨31125758008297403818174805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20750505338864935878783203 31125758008297403818174805)
              ·
                refine ⟨91188744164933800248559, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 31125758008297403818174805 91188744164933800248559)
                ·
                  rfl

theorem cell23_4794915_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 1, 10].length) (baseStart_4794915 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4794915 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4794915 prefixEnd_4794915 := by exact prefixLift 4794915
  have htrace : WordTrace (prefixWord ++ tailWord_4794915) baseStart_4794915 baseEnd_4794915 := by
    simpa [prefixWord, tailWord_4794915, baseEnd_4794915] using wordTrace_append hprefix tailTrace_4794915
  have hstable : (prefixWord ++ tailWord_4794915).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4794915).length < 2 ^ (prefixWord ++ tailWord_4794915).sum := by decide
  have hdescent : baseEnd_4794915 < baseStart_4794915 := by decide
  rcases family_descends (prefixWord ++ tailWord_4794915) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4794922 : List Nat := [3, 1, 4, 1, 1, 2, 2, 1, 1, 1, 6]
def baseStart_4794922 : Nat := 118140960795 + 4794922 * 2 ^ 59
def prefixEnd_4794922 : Nat := 4983230072969 + 3 ^ 40 * 4794922 * 2
def baseEnd_4794922 : Nat := 2462099686817794079323561

theorem tailTrace_4794922 : CollatzResearch.WordTrace tailWord_4794922 prefixEnd_4794922 2462099686817794079323561 := by
  unfold tailWord_4794922
  simp only [CollatzResearch.WordTrace]
  refine ⟨43721293183705994081538755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 116590115156549317550770013 43721293183705994081538755)
  ·
    refine ⟨65581939775558991122308133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43721293183705994081538755 65581939775558991122308133)
    ·
      refine ⟨12296613707917310835432775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 65581939775558991122308133 12296613707917310835432775)
      ·
        refine ⟨18444920561875966253149163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12296613707917310835432775 18444920561875966253149163)
        ·
          refine ⟨27667380842813949379723745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18444920561875966253149163 27667380842813949379723745)
          ·
            refine ⟨20750535632110462034792809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27667380842813949379723745 20750535632110462034792809)
            ·
              refine ⟨15562901724082846526094607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20750535632110462034792809 15562901724082846526094607)
              ·
                refine ⟨23344352586124269789141911, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15562901724082846526094607 23344352586124269789141911)
                ·
                  refine ⟨35016528879186404683712867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23344352586124269789141911 35016528879186404683712867)
                  ·
                    refine ⟨52524793318779607025569301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 35016528879186404683712867 52524793318779607025569301)
                    ·
                      refine ⟨2462099686817794079323561, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 52524793318779607025569301 2462099686817794079323561)
                      ·
                        rfl

theorem cell23_4794922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 2, 1, 1, 1, 6].length) (baseStart_4794922 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4794922 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4794922 prefixEnd_4794922 := by exact prefixLift 4794922
  have htrace : WordTrace (prefixWord ++ tailWord_4794922) baseStart_4794922 baseEnd_4794922 := by
    simpa [prefixWord, tailWord_4794922, baseEnd_4794922] using wordTrace_append hprefix tailTrace_4794922
  have hstable : (prefixWord ++ tailWord_4794922).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4794922).length < 2 ^ (prefixWord ++ tailWord_4794922).sum := by decide
  have hdescent : baseEnd_4794922 < baseStart_4794922 := by decide
  rcases family_descends (prefixWord ++ tailWord_4794922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4794929 : List Nat := [1, 2, 2, 3, 1, 1, 5, 2, 1, 2, 3]
def baseStart_4794929 : Nat := 118140960795 + 4794929 * 2 ^ 59
def prefixEnd_4794929 : Nat := 4983230072969 + 3 ^ 40 * 4794929 * 2
def baseEnd_4794929 : Nat := 2462103281182375551936029

theorem tailTrace_4794929 : CollatzResearch.WordTrace tailWord_4794929 prefixEnd_4794929 2462103281182375551936029 := by
  unfold tailWord_4794929
  simp only [CollatzResearch.WordTrace]
  refine ⟨174885428045798616521659841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116590285363865744347773227 174885428045798616521659841)
  ·
    refine ⟨131164071034348962391244881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 174885428045798616521659841 131164071034348962391244881)
    ·
      refine ⟨98373053275761721793433661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 131164071034348962391244881 98373053275761721793433661)
      ·
        refine ⟨36889894978410645672537623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 98373053275761721793433661 36889894978410645672537623)
        ·
          refine ⟨55334842467615968508806435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36889894978410645672537623 55334842467615968508806435)
          ·
            refine ⟨83002263701423952763209653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55334842467615968508806435 83002263701423952763209653)
            ·
              refine ⟨7781462222008495571550905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 83002263701423952763209653 7781462222008495571550905)
              ·
                refine ⟨5836096666506371678663179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7781462222008495571550905 5836096666506371678663179)
                ·
                  refine ⟨8754144999759557517994769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5836096666506371678663179 8754144999759557517994769)
                  ·
                    refine ⟨6565608749819668138496077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8754144999759557517994769 6565608749819668138496077)
                    ·
                      refine ⟨2462103281182375551936029, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6565608749819668138496077 2462103281182375551936029)
                      ·
                        rfl

theorem cell23_4794929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 5, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 5, 2, 1, 2, 3].length) (baseStart_4794929 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4794929 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4794929 prefixEnd_4794929 := by exact prefixLift 4794929
  have htrace : WordTrace (prefixWord ++ tailWord_4794929) baseStart_4794929 baseEnd_4794929 := by
    simpa [prefixWord, tailWord_4794929, baseEnd_4794929] using wordTrace_append hprefix tailTrace_4794929
  have hstable : (prefixWord ++ tailWord_4794929).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4794929).length < 2 ^ (prefixWord ++ tailWord_4794929).sum := by decide
  have hdescent : baseEnd_4794929 < baseStart_4794929 := by decide
  rcases family_descends (prefixWord ++ tailWord_4794929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4794955 : List Nat := [1, 1, 1, 1, 3, 1, 4, 2, 2, 2, 5]
def baseStart_4794955 : Nat := 118140960795 + 4794955 * 2 ^ 59
def prefixEnd_4794955 : Nat := 4983230072969 + 3 ^ 40 * 4794955 * 2
def baseEnd_4794955 : Nat := 2462116631679392450210909

theorem tailTrace_4794955 : CollatzResearch.WordTrace tailWord_4794955 prefixEnd_4794955 2462116631679392450210909 := by
  unfold tailWord_4794955
  simp only [CollatzResearch.WordTrace]
  refine ⟨174886376343704422962106319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116590917562469615308070879 174886376343704422962106319)
  ·
    refine ⟨262329564515556634443159479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 174886376343704422962106319 262329564515556634443159479)
    ·
      refine ⟨393494346773334951664739219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 262329564515556634443159479 393494346773334951664739219)
      ·
        refine ⟨590241520160002427497108829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 393494346773334951664739219 590241520160002427497108829)
        ·
          refine ⟨221340570060000910311415811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 590241520160002427497108829 221340570060000910311415811)
          ·
            refine ⟨332010855090001365467123717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 221340570060000910311415811 332010855090001365467123717)
            ·
              refine ⟨62252035329375256025085697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 332010855090001365467123717 62252035329375256025085697)
              ·
                refine ⟨46689026497031442018814273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 62252035329375256025085697 46689026497031442018814273)
                ·
                  refine ⟨35016769872773581514110705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 46689026497031442018814273 35016769872773581514110705)
                  ·
                    refine ⟨26262577404580186135583029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 35016769872773581514110705 26262577404580186135583029)
                    ·
                      refine ⟨2462116631679392450210909, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26262577404580186135583029 2462116631679392450210909)
                      ·
                        rfl

theorem cell23_4794955_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 4, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 4, 2, 2, 2, 5].length) (baseStart_4794955 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4794955 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4794955 prefixEnd_4794955 := by exact prefixLift 4794955
  have htrace : WordTrace (prefixWord ++ tailWord_4794955) baseStart_4794955 baseEnd_4794955 := by
    simpa [prefixWord, tailWord_4794955, baseEnd_4794955] using wordTrace_append hprefix tailTrace_4794955
  have hstable : (prefixWord ++ tailWord_4794955).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4794955).length < 2 ^ (prefixWord ++ tailWord_4794955).sum := by decide
  have hdescent : baseEnd_4794955 < baseStart_4794955 := by decide
  rcases family_descends (prefixWord ++ tailWord_4794955) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4794959 : List Nat := [1, 1, 2, 1, 1, 2, 5, 4, 2, 1, 3]
def baseStart_4794959 : Nat := 118140960795 + 4794959 * 2 ^ 59
def prefixEnd_4794959 : Nat := 4983230072969 + 3 ^ 40 * 4794959 * 2
def baseEnd_4794959 : Nat := 2462118685602010434560891

theorem tailTrace_4794959 : CollatzResearch.WordTrace tailWord_4794959 prefixEnd_4794959 2462118685602010434560891 := by
  unfold tailWord_4794959
  simp only [CollatzResearch.WordTrace]
  refine ⟨174886522235689931645251931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116591014823793287763501287 174886522235689931645251931)
  ·
    refine ⟨262329783353534897467877897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 174886522235689931645251931 262329783353534897467877897)
    ·
      refine ⟨196747337515151173100908423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 262329783353534897467877897 196747337515151173100908423)
      ·
        refine ⟨295121006272726759651362635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 196747337515151173100908423 295121006272726759651362635)
        ·
          refine ⟨442681509409090139477043953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 295121006272726759651362635 442681509409090139477043953)
          ·
            refine ⟨332011132056817604607782965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 442681509409090139477043953 332011132056817604607782965)
            ·
              refine ⟨31126043630326650431979653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 332011132056817604607782965 31126043630326650431979653)
              ·
                refine ⟨5836133180686246955996185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 31126043630326650431979653 5836133180686246955996185)
                ·
                  refine ⟨4377099885514685216997139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5836133180686246955996185 4377099885514685216997139)
                  ·
                    refine ⟨6565649828272027825495709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4377099885514685216997139 6565649828272027825495709)
                    ·
                      refine ⟨2462118685602010434560891, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6565649828272027825495709 2462118685602010434560891)
                      ·
                        rfl

theorem cell23_4794959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 5, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 5, 4, 2, 1, 3].length) (baseStart_4794959 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4794959 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4794959 prefixEnd_4794959 := by exact prefixLift 4794959
  have htrace : WordTrace (prefixWord ++ tailWord_4794959) baseStart_4794959 baseEnd_4794959 := by
    simpa [prefixWord, tailWord_4794959, baseEnd_4794959] using wordTrace_append hprefix tailTrace_4794959
  have hstable : (prefixWord ++ tailWord_4794959).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4794959).length < 2 ^ (prefixWord ++ tailWord_4794959).sum := by decide
  have hdescent : baseEnd_4794959 < baseStart_4794959 := by decide
  rcases family_descends (prefixWord ++ tailWord_4794959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4794986 : List Nat := [3, 1, 3, 2, 1, 1, 2, 4, 1, 3, 2]
def baseStart_4794986 : Nat := 118140960795 + 4794986 * 2 ^ 59
def prefixEnd_4794986 : Nat := 4983230072969 + 3 ^ 40 * 4794986 * 2
def baseEnd_4794986 : Nat := 2462132549579681828923267

theorem tailTrace_4794986 : CollatzResearch.WordTrace tailWord_4794986 prefixEnd_4794986 2462132549579681828923267 := by
  unfold tailWord_4794986
  simp only [CollatzResearch.WordTrace]
  refine ⟨43721876751648028814121203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 116591671337728076837656541 43721876751648028814121203)
  ·
    refine ⟨65582815127472043221181805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43721876751648028814121203 65582815127472043221181805)
    ·
      refine ⟨24593555672802016207943177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 65582815127472043221181805 24593555672802016207943177)
      ·
        refine ⟨18445166754601512155957383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24593555672802016207943177 18445166754601512155957383)
        ·
          refine ⟨27667750131902268233936075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18445166754601512155957383 27667750131902268233936075)
          ·
            refine ⟨41501625197853402350904113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27667750131902268233936075 41501625197853402350904113)
            ·
              refine ⟨31126218898390051763178085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 41501625197853402350904113 31126218898390051763178085)
              ·
                refine ⟨5836166043448134705595891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 31126218898390051763178085 5836166043448134705595891)
                ·
                  refine ⟨8754249065172202058393837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5836166043448134705595891 8754249065172202058393837)
                  ·
                    refine ⟨3282843399439575771897689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8754249065172202058393837 3282843399439575771897689)
                    ·
                      refine ⟨2462132549579681828923267, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3282843399439575771897689 2462132549579681828923267)
                      ·
                        rfl

theorem cell23_4794986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 2, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 2, 4, 1, 3, 2].length) (baseStart_4794986 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4794986 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4794986 prefixEnd_4794986 := by exact prefixLift 4794986
  have htrace : WordTrace (prefixWord ++ tailWord_4794986) baseStart_4794986 baseEnd_4794986 := by
    simpa [prefixWord, tailWord_4794986, baseEnd_4794986] using wordTrace_append hprefix tailTrace_4794986
  have hstable : (prefixWord ++ tailWord_4794986).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4794986).length < 2 ^ (prefixWord ++ tailWord_4794986).sum := by decide
  have hdescent : baseEnd_4794986 < baseStart_4794986 := by decide
  rcases family_descends (prefixWord ++ tailWord_4794986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4794999 : List Nat := [1, 1, 3, 1, 1, 3, 4, 2, 1, 4, 2]
def baseStart_4794999 : Nat := 118140960795 + 4794999 * 2 ^ 59
def prefixEnd_4794999 : Nat := 4983230072969 + 3 ^ 40 * 4794999 * 2
def baseEnd_4794999 : Nat := 2462139224828190278060707

theorem tailTrace_4794999 : CollatzResearch.WordTrace tailWord_4794999 prefixEnd_4794999 2462139224828190278060707 := by
  unfold tailWord_4794999
  simp only [CollatzResearch.WordTrace]
  refine ⟨174887981155545018476708051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116591987437030012317805367 174887981155545018476708051)
  ·
    refine ⟨262331971733317527715062077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 174887981155545018476708051 262331971733317527715062077)
    ·
      refine ⟨98374489399994072893148279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 262331971733317527715062077 98374489399994072893148279)
      ·
        refine ⟨147561734099991109339722419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 98374489399994072893148279 147561734099991109339722419)
        ·
          refine ⟨221342601149986664009583629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 147561734099991109339722419 221342601149986664009583629)
          ·
            refine ⟨83003475431244999003593861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 221342601149986664009583629 83003475431244999003593861)
            ·
              refine ⟨15563151643358437313173849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 83003475431244999003593861 15563151643358437313173849)
              ·
                refine ⟨11672363732518827984880387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15563151643358437313173849 11672363732518827984880387)
                ·
                  refine ⟨17508545598778241977320581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11672363732518827984880387 17508545598778241977320581)
                  ·
                    refine ⟨3282852299770920370747609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17508545598778241977320581 3282852299770920370747609)
                    ·
                      refine ⟨2462139224828190278060707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3282852299770920370747609 2462139224828190278060707)
                      ·
                        rfl

theorem cell23_4794999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 4, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 4, 2, 1, 4, 2].length) (baseStart_4794999 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4794999 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4794999 prefixEnd_4794999 := by exact prefixLift 4794999
  have htrace : WordTrace (prefixWord ++ tailWord_4794999) baseStart_4794999 baseEnd_4794999 := by
    simpa [prefixWord, tailWord_4794999, baseEnd_4794999] using wordTrace_append hprefix tailTrace_4794999
  have hstable : (prefixWord ++ tailWord_4794999).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4794999).length < 2 ^ (prefixWord ++ tailWord_4794999).sum := by decide
  have hdescent : baseEnd_4794999 < baseStart_4794999 := by decide
  rcases family_descends (prefixWord ++ tailWord_4794999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4795033 : List Nat := [1, 2, 1, 2, 1, 2, 7, 1, 2, 2, 2]
def baseStart_4795033 : Nat := 118140960795 + 4795033 * 2 ^ 59
def prefixEnd_4795033 : Nat := 4983230072969 + 3 ^ 40 * 4795033 * 2
def baseEnd_4795033 : Nat := 2462156683170443145035551

theorem tailTrace_4795033 : CollatzResearch.WordTrace tailWord_4795033 prefixEnd_4795033 2462156683170443145035551 := by
  unfold tailWord_4795033
  simp only [CollatzResearch.WordTrace]
  refine ⟨174889221237421842283445753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116592814158281228188963835 174889221237421842283445753)
  ·
    refine ⟨131166915928066381712584315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 174889221237421842283445753 131166915928066381712584315)
    ·
      refine ⟨196750373892099572568876473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 131166915928066381712584315 196750373892099572568876473)
      ·
        refine ⟨147562780419074679426657355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 196750373892099572568876473 147562780419074679426657355)
        ·
          refine ⟨221344170628612019139986033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 147562780419074679426657355 221344170628612019139986033)
          ·
            refine ⟨166008127971459014354989525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 221344170628612019139986033 166008127971459014354989525)
            ·
              refine ⟨3890815499331070648945067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 166008127971459014354989525 3890815499331070648945067)
              ·
                refine ⟨5836223248996605973417601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3890815499331070648945067 5836223248996605973417601)
                ·
                  refine ⟨4377167436747454480063201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5836223248996605973417601 4377167436747454480063201)
                  ·
                    refine ⟨3282875577560590860047401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4377167436747454480063201 3282875577560590860047401)
                    ·
                      refine ⟨2462156683170443145035551, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3282875577560590860047401 2462156683170443145035551)
                      ·
                        rfl

theorem cell23_4795033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 7, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 7, 1, 2, 2, 2].length) (baseStart_4795033 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4795033 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4795033 prefixEnd_4795033 := by exact prefixLift 4795033
  have htrace : WordTrace (prefixWord ++ tailWord_4795033) baseStart_4795033 baseEnd_4795033 := by
    simpa [prefixWord, tailWord_4795033, baseEnd_4795033] using wordTrace_append hprefix tailTrace_4795033
  have hstable : (prefixWord ++ tailWord_4795033).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4795033).length < 2 ^ (prefixWord ++ tailWord_4795033).sum := by decide
  have hdescent : baseEnd_4795033 < baseStart_4795033 := by decide
  rcases family_descends (prefixWord ++ tailWord_4795033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4795035 : List Nat := [1, 1, 1, 1, 1, 1, 2, 2, 2, 11]
def baseStart_4795035 : Nat := 118140960795 + 4795035 * 2 ^ 59
def prefixEnd_4795035 : Nat := 4983230072969 + 3 ^ 40 * 4795035 * 2
def baseEnd_4795035 : Nat := 820719236710584045736847

theorem tailTrace_4795035 : CollatzResearch.WordTrace tailWord_4795035 prefixEnd_4795035 820719236710584045736847 := by
  unfold tailWord_4795035
  simp only [CollatzResearch.WordTrace]
  refine ⟨174889294183414596625018559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116592862788943064416679039 174889294183414596625018559)
  ·
    refine ⟨262333941275121894937527839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 174889294183414596625018559 262333941275121894937527839)
    ·
      refine ⟨393500911912682842406291759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 262333941275121894937527839 393500911912682842406291759)
      ·
        refine ⟨590251367869024263609437639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 393500911912682842406291759 590251367869024263609437639)
        ·
          refine ⟨885377051803536395414156459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 590251367869024263609437639 885377051803536395414156459)
          ·
            refine ⟨1328065577705304593121234689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 885377051803536395414156459 1328065577705304593121234689)
            ·
              refine ⟨996049183278978444840926017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1328065577705304593121234689 996049183278978444840926017)
              ·
                refine ⟨747036887459233833630694513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 996049183278978444840926017 747036887459233833630694513)
                ·
                  refine ⟨560277665594425375223020885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 747036887459233833630694513 560277665594425375223020885)
                  ·
                    refine ⟨820719236710584045736847, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 11 560277665594425375223020885 820719236710584045736847)
                    ·
                      rfl

theorem cell23_4795035_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 11].length) (baseStart_4795035 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4795035 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4795035 prefixEnd_4795035 := by exact prefixLift 4795035
  have htrace : WordTrace (prefixWord ++ tailWord_4795035) baseStart_4795035 baseEnd_4795035 := by
    simpa [prefixWord, tailWord_4795035, baseEnd_4795035] using wordTrace_append hprefix tailTrace_4795035
  have hstable : (prefixWord ++ tailWord_4795035).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4795035).length < 2 ^ (prefixWord ++ tailWord_4795035).sum := by decide
  have hdescent : baseEnd_4795035 < baseStart_4795035 := by decide
  rcases family_descends (prefixWord ++ tailWord_4795035) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4795069 : List Nat := [1, 4, 1, 2, 1, 4, 1, 2, 2, 5]
def baseStart_4795069 : Nat := 118140960795 + 4795069 * 2 ^ 59
def prefixEnd_4795069 : Nat := 4983230072969 + 3 ^ 40 * 4795069 * 2
def baseEnd_4795069 : Nat := 820725056158001668061795

theorem tailTrace_4795069 : CollatzResearch.WordTrace tailWord_4795069 prefixEnd_4795069 820725056158001668061795 := by
  unfold tailWord_4795069
  simp only [CollatzResearch.WordTrace]
  refine ⟨174890534265291420431756261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116593689510194280287837507 174890534265291420431756261)
  ·
    refine ⟨32791975174742141330954299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 174890534265291420431756261 32791975174742141330954299)
    ·
      refine ⟨49187962762113211996431449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32791975174742141330954299 49187962762113211996431449)
      ·
        refine ⟨36890972071584908997323587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49187962762113211996431449 36890972071584908997323587)
        ·
          refine ⟨55336458107377363495985381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36890972071584908997323587 55336458107377363495985381)
          ·
            refine ⟨10375585895133255655497259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 55336458107377363495985381 10375585895133255655497259)
            ·
              refine ⟨15563378842699883483245889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10375585895133255655497259 15563378842699883483245889)
              ·
                refine ⟨11672534132024912612434417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15563378842699883483245889 11672534132024912612434417)
                ·
                  refine ⟨8754400599018684459325813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11672534132024912612434417 8754400599018684459325813)
                  ·
                    refine ⟨820725056158001668061795, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8754400599018684459325813 820725056158001668061795)
                    ·
                      rfl

theorem cell23_4795069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 4, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 4, 1, 2, 2, 5].length) (baseStart_4795069 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4795069 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4795069 prefixEnd_4795069 := by exact prefixLift 4795069
  have htrace : WordTrace (prefixWord ++ tailWord_4795069) baseStart_4795069 baseEnd_4795069 := by
    simpa [prefixWord, tailWord_4795069, baseEnd_4795069] using wordTrace_append hprefix tailTrace_4795069
  have hstable : (prefixWord ++ tailWord_4795069).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4795069).length < 2 ^ (prefixWord ++ tailWord_4795069).sum := by decide
  have hdescent : baseEnd_4795069 < baseStart_4795069 := by decide
  rcases family_descends (prefixWord ++ tailWord_4795069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4795073 : List Nat := [1, 2, 6, 2, 1, 2, 1, 1, 7]
def baseStart_4795073 : Nat := 118140960795 + 4795073 * 2 ^ 59
def prefixEnd_4795073 : Nat := 4983230072969 + 3 ^ 40 * 4795073 * 2
def baseEnd_4795073 : Nat := 273575246932958109837263

theorem tailTrace_4795073 : CollatzResearch.WordTrace tailWord_4795073 prefixEnd_4795073 273575246932958109837263 := by
  unfold tailWord_4795073
  simp only [CollatzResearch.WordTrace]
  refine ⟨174890680157276929114901873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116593786771517952743267915 174890680157276929114901873)
  ·
    refine ⟨131168010117957696836176405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 174890680157276929114901873 131168010117957696836176405)
    ·
      refine ⟨6148500474279267039195769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 131168010117957696836176405 6148500474279267039195769)
      ·
        refine ⟨4611375355709450279396827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6148500474279267039195769 4611375355709450279396827)
        ·
          refine ⟨6917063033564175419095241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4611375355709450279396827 6917063033564175419095241)
          ·
            refine ⟨5187797275173131564321431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6917063033564175419095241 5187797275173131564321431)
            ·
              refine ⟨7781695912759697346482147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5187797275173131564321431 7781695912759697346482147)
              ·
                refine ⟨11672543869139546019723221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7781695912759697346482147 11672543869139546019723221)
                ·
                  refine ⟨273575246932958109837263, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11672543869139546019723221 273575246932958109837263)
                  ·
                    rfl

theorem cell23_4795073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 1, 2, 1, 1, 7].length) (baseStart_4795073 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4795073 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4795073 prefixEnd_4795073 := by exact prefixLift 4795073
  have htrace : WordTrace (prefixWord ++ tailWord_4795073) baseStart_4795073 baseEnd_4795073 := by
    simpa [prefixWord, tailWord_4795073, baseEnd_4795073] using wordTrace_append hprefix tailTrace_4795073
  have hstable : (prefixWord ++ tailWord_4795073).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4795073).length < 2 ^ (prefixWord ++ tailWord_4795073).sum := by decide
  have hdescent : baseEnd_4795073 < baseStart_4795073 := by decide
  rcases family_descends (prefixWord ++ tailWord_4795073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4795089 : List Nat := [1, 2, 2, 1, 2, 3, 2, 1, 1, 6, 2]
def baseStart_4795089 : Nat := 118140960795 + 4795089 * 2 ^ 59
def prefixEnd_4795089 : Nat := 4983230072969 + 3 ^ 40 * 4795089 * 2
def baseEnd_4795089 : Nat := 2462185438087094925935293

theorem tailTrace_4795089 : CollatzResearch.WordTrace tailWord_4795089 prefixEnd_4795089 2462185438087094925935293 := by
  unfold tailWord_4795089
  simp only [CollatzResearch.WordTrace]
  refine ⟨174891263725218963847484321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116594175816812642564989547 174891263725218963847484321)
  ·
    refine ⟨131168447793914222885613241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 174891263725218963847484321 131168447793914222885613241)
    ·
      refine ⟨98376335845435667164209931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 131168447793914222885613241 98376335845435667164209931)
      ·
        refine ⟨147564503768153500746314897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 98376335845435667164209931 147564503768153500746314897)
        ·
          refine ⟨110673377826115125559736173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 147564503768153500746314897 110673377826115125559736173)
          ·
            refine ⟨41502516684793172084901065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 110673377826115125559736173 41502516684793172084901065)
            ·
              refine ⟨31126887513594879063675799, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 41502516684793172084901065 31126887513594879063675799)
              ·
                refine ⟨46690331270392318595513699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31126887513594879063675799 46690331270392318595513699)
                ·
                  refine ⟨70035496905588477893270549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 46690331270392318595513699 70035496905588477893270549)
                  ·
                    refine ⟨3282913917449459901247057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 70035496905588477893270549 3282913917449459901247057)
                    ·
                      refine ⟨2462185438087094925935293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3282913917449459901247057 2462185438087094925935293)
                      ·
                        rfl

theorem cell23_4795089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 2, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 2, 1, 1, 6, 2].length) (baseStart_4795089 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4795089 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4795089 prefixEnd_4795089 := by exact prefixLift 4795089
  have htrace : WordTrace (prefixWord ++ tailWord_4795089) baseStart_4795089 baseEnd_4795089 := by
    simpa [prefixWord, tailWord_4795089, baseEnd_4795089] using wordTrace_append hprefix tailTrace_4795089
  have hstable : (prefixWord ++ tailWord_4795089).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4795089).length < 2 ^ (prefixWord ++ tailWord_4795089).sum := by decide
  have hdescent : baseEnd_4795089 < baseStart_4795089 := by decide
  rcases family_descends (prefixWord ++ tailWord_4795089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4795116 : List Nat := [2, 2, 1, 1, 2, 2, 1, 7, 1, 4]
def baseStart_4795116 : Nat := 118140960795 + 4795116 * 2 ^ 59
def prefixEnd_4795116 : Nat := 4983230072969 + 3 ^ 40 * 4795116 * 2
def baseEnd_4795116 : Nat := 820733100688255440099223

theorem tailTrace_4795116 : CollatzResearch.WordTrace tailWord_4795116 prefixEnd_4795116 820733100688255440099223 := by
  unfold tailWord_4795116
  simp only [CollatzResearch.WordTrace]
  refine ⟨87446124248060573729358601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116594832330747431639144801 87446124248060573729358601)
  ·
    refine ⟨65584593186045430297018951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 87446124248060573729358601 65584593186045430297018951)
    ·
      refine ⟨98376889779068145445528427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65584593186045430297018951 98376889779068145445528427)
      ·
        refine ⟨147565334668602218168292641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 98376889779068145445528427 147565334668602218168292641)
        ·
          refine ⟨110674001001451663626219481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 147565334668602218168292641 110674001001451663626219481)
          ·
            refine ⟨83005500751088747719664611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 110674001001451663626219481 83005500751088747719664611)
            ·
              refine ⟨124508251126633121579496917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 83005500751088747719664611 124508251126633121579496917)
              ·
                refine ⟨2918162135780463787019459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 124508251126633121579496917 2918162135780463787019459)
                ·
                  refine ⟨4377243203670695680529189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2918162135780463787019459 4377243203670695680529189)
                  ·
                    refine ⟨820733100688255440099223, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4377243203670695680529189 820733100688255440099223)
                    ·
                      rfl

theorem cell23_4795116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 1, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 1, 7, 1, 4].length) (baseStart_4795116 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4795116 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4795116 prefixEnd_4795116 := by exact prefixLift 4795116
  have htrace : WordTrace (prefixWord ++ tailWord_4795116) baseStart_4795116 baseEnd_4795116 := by
    simpa [prefixWord, tailWord_4795116, baseEnd_4795116] using wordTrace_append hprefix tailTrace_4795116
  have hstable : (prefixWord ++ tailWord_4795116).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4795116).length < 2 ^ (prefixWord ++ tailWord_4795116).sum := by decide
  have hdescent : baseEnd_4795116 < baseStart_4795116 := by decide
  rcases family_descends (prefixWord ++ tailWord_4795116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4795124 : List Nat := [2, 6, 1, 1, 3, 1, 2, 2, 5]
def baseStart_4795124 : Nat := 118140960795 + 4795124 * 2 ^ 59
def prefixEnd_4795124 : Nat := 4983230072969 + 3 ^ 40 * 4795124 * 2
def baseEnd_4795124 : Nat := 273578156656666920999737

theorem tailTrace_4795124 : CollatzResearch.WordTrace tailWord_4795124 prefixEnd_4795124 273578156656666920999737 := by
  unfold tailWord_4795124
  simp only [CollatzResearch.WordTrace]
  refine ⟨87446270140046082412504213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116595026853394776550005617 87446270140046082412504213)
  ·
    refine ⟨4099043912814660113086135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 87446270140046082412504213 4099043912814660113086135)
    ·
      refine ⟨6148565869221990169629203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4099043912814660113086135 6148565869221990169629203)
      ·
        refine ⟨9222848803832985254443805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6148565869221990169629203 9222848803832985254443805)
        ·
          refine ⟨3458568301437369470416427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9222848803832985254443805 3458568301437369470416427)
          ·
            refine ⟨5187852452156054205624641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3458568301437369470416427 5187852452156054205624641)
            ·
              refine ⟨3890889339117040654218481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5187852452156054205624641 3890889339117040654218481)
              ·
                refine ⟨2918167004337780490663861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3890889339117040654218481 2918167004337780490663861)
                ·
                  refine ⟨273578156656666920999737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2918167004337780490663861 273578156656666920999737)
                  ·
                    rfl

theorem cell23_4795124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 3, 1, 2, 2, 5].length) (baseStart_4795124 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4795124 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4795124 prefixEnd_4795124 := by exact prefixLift 4795124
  have htrace : WordTrace (prefixWord ++ tailWord_4795124) baseStart_4795124 baseEnd_4795124 := by
    simpa [prefixWord, tailWord_4795124, baseEnd_4795124] using wordTrace_append hprefix tailTrace_4795124
  have hstable : (prefixWord ++ tailWord_4795124).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4795124).length < 2 ^ (prefixWord ++ tailWord_4795124).sum := by decide
  have hdescent : baseEnd_4795124 < baseStart_4795124 := by decide
  rcases family_descends (prefixWord ++ tailWord_4795124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4795126 : List Nat := [5, 1, 1, 1, 1, 2, 1, 4, 2, 2, 3]
def baseStart_4795126 : Nat := 118140960795 + 4795126 * 2 ^ 59
def prefixEnd_4795126 : Nat := 4983230072969 + 3 ^ 40 * 4795126 * 2
def baseEnd_4795126 : Nat := 2462204436871311281172623

theorem tailTrace_4795126 : CollatzResearch.WordTrace tailWord_4795126 prefixEnd_4795126 2462204436871311281172623 := by
  unfold tailWord_4795126
  simp only [CollatzResearch.WordTrace]
  refine ⟨10930788326630307447911327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 116595075484056612777720821 10930788326630307447911327)
  ·
    refine ⟨16396182489945461171866991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10930788326630307447911327 16396182489945461171866991)
    ·
      refine ⟨24594273734918191757800487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16396182489945461171866991 24594273734918191757800487)
      ·
        refine ⟨36891410602377287636700731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24594273734918191757800487 36891410602377287636700731)
        ·
          refine ⟨55337115903565931455051097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36891410602377287636700731 55337115903565931455051097)
          ·
            refine ⟨41502836927674448591288323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 55337115903565931455051097 41502836927674448591288323)
            ·
              refine ⟨62254255391511672886932485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41502836927674448591288323 62254255391511672886932485)
              ·
                refine ⟨11672672885908438666299841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 62254255391511672886932485 11672672885908438666299841)
                ·
                  refine ⟨8754504664431328999724881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11672672885908438666299841 8754504664431328999724881)
                  ·
                    refine ⟨6565878498323496749793661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8754504664431328999724881 6565878498323496749793661)
                    ·
                      refine ⟨2462204436871311281172623, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6565878498323496749793661 2462204436871311281172623)
                      ·
                        rfl

theorem cell23_4795126_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 1, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 1, 4, 2, 2, 3].length) (baseStart_4795126 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4795126 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4795126 prefixEnd_4795126 := by exact prefixLift 4795126
  have htrace : WordTrace (prefixWord ++ tailWord_4795126) baseStart_4795126 baseEnd_4795126 := by
    simpa [prefixWord, tailWord_4795126, baseEnd_4795126] using wordTrace_append hprefix tailTrace_4795126
  have hstable : (prefixWord ++ tailWord_4795126).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4795126).length < 2 ^ (prefixWord ++ tailWord_4795126).sum := by decide
  have hdescent : baseEnd_4795126 < baseStart_4795126 := by decide
  rcases family_descends (prefixWord ++ tailWord_4795126) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4795176 : List Nat := [2, 1, 5, 1, 1, 1, 3, 3, 1, 5]
def baseStart_4795176 : Nat := 118140960795 + 4795176 * 2 ^ 59
def prefixEnd_4795176 : Nat := 4983230072969 + 3 ^ 40 * 4795176 * 2
def baseEnd_4795176 : Nat := 820743370301345361849131

theorem tailTrace_4795176 : CollatzResearch.WordTrace tailWord_4795176 prefixEnd_4795176 820743370301345361849131 := by
  unfold tailWord_4795176
  simp only [CollatzResearch.WordTrace]
  refine ⟨87447218437951888852950691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116596291250602518470600921 87447218437951888852950691)
  ·
    refine ⟨131170827656927833279426037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87447218437951888852950691 131170827656927833279426037)
    ·
      refine ⟨12297265092836984369946191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 131170827656927833279426037 12297265092836984369946191)
      ·
        refine ⟨18445897639255476554919287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12297265092836984369946191 18445897639255476554919287)
        ·
          refine ⟨27668846458883214832378931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18445897639255476554919287 27668846458883214832378931)
          ·
            refine ⟨41503269688324822248568397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27668846458883214832378931 41503269688324822248568397)
            ·
              refine ⟨15563726133121808343213149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 41503269688324822248568397 15563726133121808343213149)
              ·
                refine ⟨5836397299920678128704931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15563726133121808343213149 5836397299920678128704931)
                ·
                  refine ⟨8754595949881017193057397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5836397299920678128704931 8754595949881017193057397)
                  ·
                    refine ⟨820743370301345361849131, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8754595949881017193057397 820743370301345361849131)
                    ·
                      rfl

theorem cell23_4795176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 3, 3, 1, 5].length) (baseStart_4795176 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4795176 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4795176 prefixEnd_4795176 := by exact prefixLift 4795176
  have htrace : WordTrace (prefixWord ++ tailWord_4795176) baseStart_4795176 baseEnd_4795176 := by
    simpa [prefixWord, tailWord_4795176, baseEnd_4795176] using wordTrace_append hprefix tailTrace_4795176
  have hstable : (prefixWord ++ tailWord_4795176).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4795176).length < 2 ^ (prefixWord ++ tailWord_4795176).sum := by decide
  have hdescent : baseEnd_4795176 < baseStart_4795176 := by decide
  rcases family_descends (prefixWord ++ tailWord_4795176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4795199 : List Nat := [1, 1, 2, 2, 5, 1, 1, 1, 3, 1, 5]
def baseStart_4795199 : Nat := 118140960795 + 4795199 * 2 ^ 59
def prefixEnd_4795199 : Nat := 4983230072969 + 3 ^ 40 * 4795199 * 2
def baseEnd_4795199 : Nat := 2462241920959089495559787

theorem tailTrace_4795199 : CollatzResearch.WordTrace tailWord_4795199 prefixEnd_4795199 2462241920959089495559787 := by
  unfold tailWord_4795199
  simp only [CollatzResearch.WordTrace]
  refine ⟨174895275754820452633988651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116596850503213635089325767 174895275754820452633988651)
  ·
    refine ⟨262342913632230678950982977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 174895275754820452633988651 262342913632230678950982977)
    ·
      refine ⟨196757185224173009213237233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 262342913632230678950982977 196757185224173009213237233)
      ·
        refine ⟨147567888918129756909927925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 196757185224173009213237233 147567888918129756909927925)
        ·
          refine ⟨13834489586074664710305743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 147567888918129756909927925 13834489586074664710305743)
          ·
            refine ⟨20751734379111997065458615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13834489586074664710305743 20751734379111997065458615)
            ·
              refine ⟨31127601568667995598187923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20751734379111997065458615 31127601568667995598187923)
              ·
                refine ⟨46691402353001993397281885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31127601568667995598187923 46691402353001993397281885)
                ·
                  refine ⟨17509275882375747523980707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 46691402353001993397281885 17509275882375747523980707)
                  ·
                    refine ⟨26263913823563621285971061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17509275882375747523980707 26263913823563621285971061)
                    ·
                      refine ⟨2462241920959089495559787, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26263913823563621285971061 2462241920959089495559787)
                      ·
                        rfl

theorem cell23_4795199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 1, 1, 3, 1, 5].length) (baseStart_4795199 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4795199 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4795199 prefixEnd_4795199 := by exact prefixLift 4795199
  have htrace : WordTrace (prefixWord ++ tailWord_4795199) baseStart_4795199 baseEnd_4795199 := by
    simpa [prefixWord, tailWord_4795199, baseEnd_4795199] using wordTrace_append hprefix tailTrace_4795199
  have hstable : (prefixWord ++ tailWord_4795199).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4795199).length < 2 ^ (prefixWord ++ tailWord_4795199).sum := by decide
  have hdescent : baseEnd_4795199 < baseStart_4795199 := by decide
  rcases family_descends (prefixWord ++ tailWord_4795199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4795209 : List Nat := [1, 2, 1, 1, 2, 6, 1, 1, 1, 1, 6]
def baseStart_4795209 : Nat := 118140960795 + 4795209 * 2 ^ 59
def prefixEnd_4795209 : Nat := 4983230072969 + 3 ^ 40 * 4795209 * 2
def baseEnd_4795209 : Nat := 2462247055765634456434741

theorem tailTrace_4795209 : CollatzResearch.WordTrace tailWord_4795209 prefixEnd_4795209 2462247055765634456434741 := by
  unfold tailWord_4795209
  simp only [CollatzResearch.WordTrace]
  refine ⟨174895640484784224341852681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116597093656522816227901787 174895640484784224341852681)
  ·
    refine ⟨131171730363588168256389511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 174895640484784224341852681 131171730363588168256389511)
    ·
      refine ⟨196757595545382252384584267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 131171730363588168256389511 196757595545382252384584267)
      ·
        refine ⟨295136393318073378576876401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 196757595545382252384584267 295136393318073378576876401)
        ·
          refine ⟨221352294988555033932657301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 295136393318073378576876401 221352294988555033932657301)
          ·
            refine ⟨10375888827588517215593311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 221352294988555033932657301 10375888827588517215593311)
            ·
              refine ⟨15563833241382775823389967, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10375888827588517215593311 15563833241382775823389967)
              ·
                refine ⟨23345749862074163735084951, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15563833241382775823389967 23345749862074163735084951)
                ·
                  refine ⟨35018624793111245602627427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23345749862074163735084951 35018624793111245602627427)
                  ·
                    refine ⟨52527937189666868403941141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 35018624793111245602627427 52527937189666868403941141)
                    ·
                      refine ⟨2462247055765634456434741, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 52527937189666868403941141 2462247055765634456434741)
                      ·
                        rfl

theorem cell23_4795209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 6, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 6, 1, 1, 1, 1, 6].length) (baseStart_4795209 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4795209 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4795209 prefixEnd_4795209 := by exact prefixLift 4795209
  have htrace : WordTrace (prefixWord ++ tailWord_4795209) baseStart_4795209 baseEnd_4795209 := by
    simpa [prefixWord, tailWord_4795209, baseEnd_4795209] using wordTrace_append hprefix tailTrace_4795209
  have hstable : (prefixWord ++ tailWord_4795209).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4795209).length < 2 ^ (prefixWord ++ tailWord_4795209).sum := by decide
  have hdescent : baseEnd_4795209 < baseStart_4795209 := by decide
  rcases family_descends (prefixWord ++ tailWord_4795209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4795216 : List Nat := [2, 1, 1, 1, 1, 4, 3, 4, 1, 2, 3]
def baseStart_4795216 : Nat := 118140960795 + 4795216 * 2 ^ 59
def prefixEnd_4795216 : Nat := 4983230072969 + 3 ^ 40 * 4795216 * 2
def baseEnd_4795216 : Nat := 2462250650130215929047209

theorem tailTrace_4795216 : CollatzResearch.WordTrace tailWord_4795216 prefixEnd_4795216 2462250650130215929047209 := by
  unfold tailWord_4795216
  simp only [CollatzResearch.WordTrace]
  refine ⟨87447947897879432268678751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116597263863839243024905001 87447947897879432268678751)
  ·
    refine ⟨131171921846819148403018127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87447947897879432268678751 131171921846819148403018127)
    ·
      refine ⟨196757882770228722604527191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 131171921846819148403018127 196757882770228722604527191)
      ·
        refine ⟨295136824155343083906790787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 196757882770228722604527191 295136824155343083906790787)
        ·
          refine ⟨442705236233014625860186181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 295136824155343083906790787 442705236233014625860186181)
          ·
            refine ⟨83007231793690242348784909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 442705236233014625860186181 83007231793690242348784909)
            ·
              refine ⟨31127711922633840880794341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 83007231793690242348784909 31127711922633840880794341)
              ·
                refine ⟨5836445985493845165148939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 31127711922633840880794341 5836445985493845165148939)
                ·
                  refine ⟨8754668978240767747723409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5836445985493845165148939 8754668978240767747723409)
                  ·
                    refine ⟨6566001733680575810792557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8754668978240767747723409 6566001733680575810792557)
                    ·
                      refine ⟨2462250650130215929047209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6566001733680575810792557 2462250650130215929047209)
                      ·
                        rfl

theorem cell23_4795216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 3, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 3, 4, 1, 2, 3].length) (baseStart_4795216 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4795216 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4795216 prefixEnd_4795216 := by exact prefixLift 4795216
  have htrace : WordTrace (prefixWord ++ tailWord_4795216) baseStart_4795216 baseEnd_4795216 := by
    simpa [prefixWord, tailWord_4795216, baseEnd_4795216] using wordTrace_append hprefix tailTrace_4795216
  have hstable : (prefixWord ++ tailWord_4795216).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4795216).length < 2 ^ (prefixWord ++ tailWord_4795216).sum := by decide
  have hdescent : baseEnd_4795216 < baseStart_4795216 := by decide
  rcases family_descends (prefixWord ++ tailWord_4795216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4795273 : List Nat := [1, 2, 1, 1, 5, 3, 1, 1, 3, 3, 2]
def baseStart_4795273 : Nat := 118140960795 + 4795273 * 2 ^ 59
def prefixEnd_4795273 : Nat := 4983230072969 + 3 ^ 40 * 4795273 * 2
def baseEnd_4795273 : Nat := 2462279918527522206034447

theorem tailTrace_4795273 : CollatzResearch.WordTrace tailWord_4795273 prefixEnd_4795273 2462279918527522206034447 := by
  unfold tailWord_4795273
  simp only [CollatzResearch.WordTrace]
  refine ⟨174897974756552363272182473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116598649837701575514788315 174897974756552363272182473)
  ·
    refine ⟨131173481067414272454136855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 174897974756552363272182473 131173481067414272454136855)
    ·
      refine ⟨196760221601121408681205283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 131173481067414272454136855 196760221601121408681205283)
      ·
        refine ⟨295140332401682113021807925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 196760221601121408681205283 295140332401682113021807925)
        ·
          refine ⟨27669406162657698095794493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 295140332401682113021807925 27669406162657698095794493)
          ·
            refine ⟨10376027310996636785922935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27669406162657698095794493 10376027310996636785922935)
            ·
              refine ⟨15564040966494955178884403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10376027310996636785922935 15564040966494955178884403)
              ·
                refine ⟨23346061449742432768326605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15564040966494955178884403 23346061449742432768326605)
                ·
                  refine ⟨8754773043653412288122477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23346061449742432768326605 8754773043653412288122477)
                  ·
                    refine ⟨3283039891370029608045929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8754773043653412288122477 3283039891370029608045929)
                    ·
                      refine ⟨2462279918527522206034447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3283039891370029608045929 2462279918527522206034447)
                      ·
                        rfl

theorem cell23_4795273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 3, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 3, 1, 1, 3, 3, 2].length) (baseStart_4795273 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4795273 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4795273 prefixEnd_4795273 := by exact prefixLift 4795273
  have htrace : WordTrace (prefixWord ++ tailWord_4795273) baseStart_4795273 baseEnd_4795273 := by
    simpa [prefixWord, tailWord_4795273, baseEnd_4795273] using wordTrace_append hprefix tailTrace_4795273
  have hstable : (prefixWord ++ tailWord_4795273).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4795273).length < 2 ^ (prefixWord ++ tailWord_4795273).sum := by decide
  have hdescent : baseEnd_4795273 < baseStart_4795273 := by decide
  rcases family_descends (prefixWord ++ tailWord_4795273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4795320 : List Nat := [2, 1, 2, 1, 2, 4, 2, 3, 2, 2, 2]
def baseStart_4795320 : Nat := 118140960795 + 4795320 * 2 ^ 59
def prefixEnd_4795320 : Nat := 4983230072969 + 3 ^ 40 * 4795320 * 2
def baseEnd_4795320 : Nat := 2462304052118283522146731

theorem tailTrace_4795320 : CollatzResearch.WordTrace tailWord_4795320 prefixEnd_4795320 2462304052118283522146731 := by
  unfold tailWord_4795320
  simp only [CollatzResearch.WordTrace]
  refine ⟨87449844493691045149571707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116599792658254726866095609 87449844493691045149571707)
  ·
    refine ⟨131174766740536567724357561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87449844493691045149571707 131174766740536567724357561)
    ·
      refine ⟨98381075055402425793268171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 131174766740536567724357561 98381075055402425793268171)
      ·
        refine ⟨147571612583103638689902257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 98381075055402425793268171 147571612583103638689902257)
        ·
          refine ⟨110678709437327729017426693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 147571612583103638689902257 110678709437327729017426693)
          ·
            refine ⟨20752258019498949190767505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 110678709437327729017426693 20752258019498949190767505)
            ·
              refine ⟨15564193514624211893075629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20752258019498949190767505 15564193514624211893075629)
              ·
                refine ⟨5836572567984079459903361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15564193514624211893075629 5836572567984079459903361)
                ·
                  refine ⟨4377429425988059594927521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5836572567984079459903361 4377429425988059594927521)
                  ·
                    refine ⟨3283072069491044696195641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4377429425988059594927521 3283072069491044696195641)
                    ·
                      refine ⟨2462304052118283522146731, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3283072069491044696195641 2462304052118283522146731)
                      ·
                        rfl

theorem cell23_4795320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 2, 3, 2, 2, 2].length) (baseStart_4795320 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4795320 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4795320 prefixEnd_4795320 := by exact prefixLift 4795320
  have htrace : WordTrace (prefixWord ++ tailWord_4795320) baseStart_4795320 baseEnd_4795320 := by
    simpa [prefixWord, tailWord_4795320, baseEnd_4795320] using wordTrace_append hprefix tailTrace_4795320
  have hstable : (prefixWord ++ tailWord_4795320).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4795320).length < 2 ^ (prefixWord ++ tailWord_4795320).sum := by decide
  have hdescent : baseEnd_4795320 < baseStart_4795320 := by decide
  rcases family_descends (prefixWord ++ tailWord_4795320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4795326 : List Nat := [4, 2, 1, 1, 1, 2, 3, 2, 7]
def baseStart_4795326 : Nat := 118140960795 + 4795326 * 2 ^ 59
def prefixEnd_4795326 : Nat := 4983230072969 + 3 ^ 40 * 4795326 * 2
def baseEnd_4795326 : Nat := 273589681444690055407967

theorem tailTrace_4795326 : CollatzResearch.WordTrace tailWord_4795326 prefixEnd_4795326 273589681444690055407967 := by
  unfold tailWord_4795326
  simp only [CollatzResearch.WordTrace]
  refine ⟨21862488478170044165482729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 116599938550240235549241221 21862488478170044165482729)
  ·
    refine ⟨16396866358627533124112047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21862488478170044165482729 16396866358627533124112047)
    ·
      refine ⟨24595299537941299686168071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16396866358627533124112047 24595299537941299686168071)
      ·
        refine ⟨36892949306911949529252107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24595299537941299686168071 36892949306911949529252107)
        ·
          refine ⟨55339423960367924293878161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36892949306911949529252107 55339423960367924293878161)
          ·
            refine ⟨41504567970275943220408621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 55339423960367924293878161 41504567970275943220408621)
            ·
              refine ⟨15564212988853478707653233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 41504567970275943220408621 15564212988853478707653233)
              ·
                refine ⟨11673159741640109030739925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15564212988853478707653233 11673159741640109030739925)
                ·
                  refine ⟨273589681444690055407967, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11673159741640109030739925 273589681444690055407967)
                  ·
                    rfl

theorem cell23_4795326_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 3, 2, 7].length) (baseStart_4795326 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4795326 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4795326 prefixEnd_4795326 := by exact prefixLift 4795326
  have htrace : WordTrace (prefixWord ++ tailWord_4795326) baseStart_4795326 baseEnd_4795326 := by
    simpa [prefixWord, tailWord_4795326, baseEnd_4795326] using wordTrace_append hprefix tailTrace_4795326
  have hstable : (prefixWord ++ tailWord_4795326).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4795326).length < 2 ^ (prefixWord ++ tailWord_4795326).sum := by decide
  have hdescent : baseEnd_4795326 < baseStart_4795326 := by decide
  rcases family_descends (prefixWord ++ tailWord_4795326) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4795341 : List Nat := [1, 6, 3, 1, 1, 1, 1, 3, 1, 3, 2]
def baseStart_4795341 : Nat := 118140960795 + 4795341 * 2 ^ 59
def prefixEnd_4795341 : Nat := 4983230072969 + 3 ^ 40 * 4795341 * 2
def baseEnd_4795341 : Nat := 2462314835212027939984135

theorem tailTrace_4795341 : CollatzResearch.WordTrace tailWord_4795341 prefixEnd_4795341 2462314835212027939984135 := by
  unfold tailWord_4795341
  simp only [CollatzResearch.WordTrace]
  refine ⟨174900454920306010885657877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116600303280204007257105251 174900454920306010885657877)
  ·
    refine ⟨8198458824389344260265213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 174900454920306010885657877 8198458824389344260265213)
    ·
      refine ⟨3074422059146004097599455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8198458824389344260265213 3074422059146004097599455)
      ·
        refine ⟨4611633088719006146399183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3074422059146004097599455 4611633088719006146399183)
        ·
          refine ⟨6917449633078509219598775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4611633088719006146399183 6917449633078509219598775)
          ·
            refine ⟨10376174449617763829398163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6917449633078509219598775 10376174449617763829398163)
            ·
              refine ⟨15564261674426645744097245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10376174449617763829398163 15564261674426645744097245)
              ·
                refine ⟨5836598127909992154036467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15564261674426645744097245 5836598127909992154036467)
                ·
                  refine ⟨8754897191864988231054701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5836598127909992154036467 8754897191864988231054701)
                  ·
                    refine ⟨3283086446949370586645513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8754897191864988231054701 3283086446949370586645513)
                    ·
                      refine ⟨2462314835212027939984135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3283086446949370586645513 2462314835212027939984135)
                      ·
                        rfl

theorem cell23_4795341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 1, 1, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 1, 1, 1, 3, 1, 3, 2].length) (baseStart_4795341 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4795341 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4795341 prefixEnd_4795341 := by exact prefixLift 4795341
  have htrace : WordTrace (prefixWord ++ tailWord_4795341) baseStart_4795341 baseEnd_4795341 := by
    simpa [prefixWord, tailWord_4795341, baseEnd_4795341] using wordTrace_append hprefix tailTrace_4795341
  have hstable : (prefixWord ++ tailWord_4795341).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4795341).length < 2 ^ (prefixWord ++ tailWord_4795341).sum := by decide
  have hdescent : baseEnd_4795341 < baseStart_4795341 := by decide
  rcases family_descends (prefixWord ++ tailWord_4795341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4795343 : List Nat := [1, 1, 2, 1, 1, 7, 2, 3, 5]
def baseStart_4795343 : Nat := 118140960795 + 4795343 * 2 ^ 59
def prefixEnd_4795343 : Nat := 4983230072969 + 3 ^ 40 * 4795343 * 2
def baseEnd_4795343 : Nat := 273590651352592992462125

theorem tailTrace_4795343 : CollatzResearch.WordTrace tailWord_4795343 prefixEnd_4795343 273590651352592992462125 := by
  unfold tailWord_4795343
  simp only [CollatzResearch.WordTrace]
  refine ⟨174900527866298765227230683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116600351910865843484820455 174900527866298765227230683)
  ·
    refine ⟨262350791799448147840846025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 174900527866298765227230683 262350791799448147840846025)
    ·
      refine ⟨196763093849586110880634519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 262350791799448147840846025 196763093849586110880634519)
      ·
        refine ⟨295144640774379166320951779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 196763093849586110880634519 295144640774379166320951779)
        ·
          refine ⟨442716961161568749481427669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 295144640774379166320951779 442716961161568749481427669)
          ·
            refine ⟨10376178777224267565970961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 442716961161568749481427669 10376178777224267565970961)
            ·
              refine ⟨7782134082918200674478221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10376178777224267565970961 7782134082918200674478221)
              ·
                refine ⟨2918300281094325252929333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7782134082918200674478221 2918300281094325252929333)
                ·
                  refine ⟨273590651352592992462125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2918300281094325252929333 273590651352592992462125)
                  ·
                    rfl

theorem cell23_4795343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 7, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 7, 2, 3, 5].length) (baseStart_4795343 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4795343 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4795343 prefixEnd_4795343 := by exact prefixLift 4795343
  have htrace : WordTrace (prefixWord ++ tailWord_4795343) baseStart_4795343 baseEnd_4795343 := by
    simpa [prefixWord, tailWord_4795343, baseEnd_4795343] using wordTrace_append hprefix tailTrace_4795343
  have hstable : (prefixWord ++ tailWord_4795343).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4795343).length < 2 ^ (prefixWord ++ tailWord_4795343).sum := by decide
  have hdescent : baseEnd_4795343 < baseStart_4795343 := by decide
  rcases family_descends (prefixWord ++ tailWord_4795343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4795394 : List Nat := [3, 4, 1, 3, 1, 2, 1, 3, 5]
def baseStart_4795394 : Nat := 118140960795 + 4795394 * 2 ^ 59
def prefixEnd_4795394 : Nat := 4983230072969 + 3 ^ 40 * 4795394 * 2
def baseEnd_4795394 : Nat := 273593561076301803624599

theorem tailTrace_4795394 : CollatzResearch.WordTrace tailWord_4795394 prefixEnd_4795394 273593561076301803624599 := by
  unfold tailWord_4795394
  simp only [CollatzResearch.WordTrace]
  refine ⟨43725596997278500234334309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 116601591992742667291558157 43725596997278500234334309)
  ·
    refine ⟨8198549436989718793937683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 43725596997278500234334309 8198549436989718793937683)
    ·
      refine ⟨12297824155484578190906525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8198549436989718793937683 12297824155484578190906525)
      ·
        refine ⟨4611684058306716821589947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12297824155484578190906525 4611684058306716821589947)
        ·
          refine ⟨6917526087460075232384921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4611684058306716821589947 6917526087460075232384921)
          ·
            refine ⟨5188144565595056424288691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6917526087460075232384921 5188144565595056424288691)
            ·
              refine ⟨7782216848392584636433037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5188144565595056424288691 7782216848392584636433037)
              ·
                refine ⟨2918331318147219238662389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7782216848392584636433037 2918331318147219238662389)
                ·
                  refine ⟨273593561076301803624599, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2918331318147219238662389 273593561076301803624599)
                  ·
                    rfl

theorem cell23_4795394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 1, 2, 1, 3, 5].length) (baseStart_4795394 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4795394 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4795394 prefixEnd_4795394 := by exact prefixLift 4795394
  have htrace : WordTrace (prefixWord ++ tailWord_4795394) baseStart_4795394 baseEnd_4795394 := by
    simpa [prefixWord, tailWord_4795394, baseEnd_4795394] using wordTrace_append hprefix tailTrace_4795394
  have hstable : (prefixWord ++ tailWord_4795394).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4795394).length < 2 ^ (prefixWord ++ tailWord_4795394).sum := by decide
  have hdescent : baseEnd_4795394 < baseStart_4795394 := by decide
  rcases family_descends (prefixWord ++ tailWord_4795394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4795413 : List Nat := [1, 3, 2, 1, 4, 1, 1, 1, 4, 2, 3]
def baseStart_4795413 : Nat := 118140960795 + 4795413 * 2 ^ 59
def prefixEnd_4795413 : Nat := 4983230072969 + 3 ^ 40 * 4795413 * 2
def baseEnd_4795413 : Nat := 2462351805819151658283803

theorem tailTrace_4795413 : CollatzResearch.WordTrace tailWord_4795413 prefixEnd_4795413 2462351805819151658283803 := by
  unfold tailWord_4795413
  simp only [CollatzResearch.WordTrace]
  refine ⟨174903080976045167182278893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116602053984030111454852595 174903080976045167182278893)
  ·
    refine ⟨65588655366016937693354585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 174903080976045167182278893 65588655366016937693354585)
    ·
      refine ⟨49191491524512703270015939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 65588655366016937693354585 49191491524512703270015939)
      ·
        refine ⟨73787237286769054905023909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49191491524512703270015939 73787237286769054905023909)
        ·
          refine ⟨13835106991269197794691983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 73787237286769054905023909 13835106991269197794691983)
          ·
            refine ⟨20752660486903796692037975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13835106991269197794691983 20752660486903796692037975)
            ·
              refine ⟨31128990730355695038056963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20752660486903796692037975 31128990730355695038056963)
              ·
                refine ⟨46693486095533542557085445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31128990730355695038056963 46693486095533542557085445)
                ·
                  refine ⟨8755028642912539229453521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 46693486095533542557085445 8755028642912539229453521)
                  ·
                    refine ⟨6566271482184404422090141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8755028642912539229453521 6566271482184404422090141)
                    ·
                      refine ⟨2462351805819151658283803, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6566271482184404422090141 2462351805819151658283803)
                      ·
                        rfl

theorem cell23_4795413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 1, 1, 4, 2, 3].length) (baseStart_4795413 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4795413 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4795413 prefixEnd_4795413 := by exact prefixLift 4795413
  have htrace : WordTrace (prefixWord ++ tailWord_4795413) baseStart_4795413 baseEnd_4795413 := by
    simpa [prefixWord, tailWord_4795413, baseEnd_4795413] using wordTrace_append hprefix tailTrace_4795413
  have hstable : (prefixWord ++ tailWord_4795413).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4795413).length < 2 ^ (prefixWord ++ tailWord_4795413).sum := by decide
  have hdescent : baseEnd_4795413 < baseStart_4795413 := by decide
  rcases family_descends (prefixWord ++ tailWord_4795413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4795416 : List Nat := [2, 1, 2, 3, 2, 2, 2, 1, 8]
def baseStart_4795416 : Nat := 118140960795 + 4795416 * 2 ^ 59
def prefixEnd_4795416 : Nat := 4983230072969 + 3 ^ 40 * 4795416 * 2
def baseEnd_4795416 : Nat := 273594816251235016282921

theorem tailTrace_4795416 : CollatzResearch.WordTrace tailWord_4795416 prefixEnd_4795416 273594816251235016282921 := by
  unfold tailWord_4795416
  simp only [CollatzResearch.WordTrace]
  refine ⟨87451595197517149347319051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116602126930022865796425401 87451595197517149347319051)
  ·
    refine ⟨131177392796275724020978577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87451595197517149347319051 131177392796275724020978577)
    ·
      refine ⟨98383044597206793015733933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 131177392796275724020978577 98383044597206793015733933)
      ·
        refine ⟨36893641723952547380900225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 98383044597206793015733933 36893641723952547380900225)
        ·
          refine ⟨27670231292964410535675169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36893641723952547380900225 27670231292964410535675169)
          ·
            refine ⟨20752673469723307901756377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27670231292964410535675169 20752673469723307901756377)
            ·
              refine ⟨15564505102292480926317283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20752673469723307901756377 15564505102292480926317283)
              ·
                refine ⟨23346757653438721389475925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15564505102292480926317283 23346757653438721389475925)
                ·
                  refine ⟨273594816251235016282921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 23346757653438721389475925 273594816251235016282921)
                  ·
                    rfl

theorem cell23_4795416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 2, 1, 8].length) (baseStart_4795416 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4795416 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4795416 prefixEnd_4795416 := by exact prefixLift 4795416
  have htrace : WordTrace (prefixWord ++ tailWord_4795416) baseStart_4795416 baseEnd_4795416 := by
    simpa [prefixWord, tailWord_4795416, baseEnd_4795416] using wordTrace_append hprefix tailTrace_4795416
  have hstable : (prefixWord ++ tailWord_4795416).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4795416).length < 2 ^ (prefixWord ++ tailWord_4795416).sum := by decide
  have hdescent : baseEnd_4795416 < baseStart_4795416 := by decide
  rcases family_descends (prefixWord ++ tailWord_4795416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4795443 : List Nat := [1, 1, 1, 2, 4, 1, 1, 3, 5, 1, 3]
def baseStart_4795443 : Nat := 118140960795 + 4795443 * 2 ^ 59
def prefixEnd_4795443 : Nat := 4983230072969 + 3 ^ 40 * 4795443 * 2
def baseEnd_4795443 : Nat := 2462367210238786540908665

theorem tailTrace_4795443 : CollatzResearch.WordTrace tailWord_4795443 prefixEnd_4795443 2462367210238786540908665 := by
  unfold tailWord_4795443
  simp only [CollatzResearch.WordTrace]
  refine ⟨174904175165936482305870983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116602783443957654870580655 174904175165936482305870983)
  ·
    refine ⟨262356262748904723458806475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 174904175165936482305870983 262356262748904723458806475)
    ·
      refine ⟨393534394123357085188209713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 262356262748904723458806475 393534394123357085188209713)
      ·
        refine ⟨295150795592517813891157285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 393534394123357085188209713 295150795592517813891157285)
        ·
          refine ⟨55340774173597090104591991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 295150795592517813891157285 55340774173597090104591991)
          ·
            refine ⟨83011161260395635156887987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55340774173597090104591991 83011161260395635156887987)
            ·
              refine ⟨124516741890593452735331981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 83011161260395635156887987 124516741890593452735331981)
              ·
                refine ⟨46693778208972544775749493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 124516741890593452735331981 46693778208972544775749493)
                ·
                  refine ⟨4377541707091176072726515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 46693778208972544775749493 4377541707091176072726515)
                  ·
                    refine ⟨6566312560636764109089773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4377541707091176072726515 6566312560636764109089773)
                    ·
                      refine ⟨2462367210238786540908665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6566312560636764109089773 2462367210238786540908665)
                      ·
                        rfl

theorem cell23_4795443_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 1, 3, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 1, 3, 5, 1, 3].length) (baseStart_4795443 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4795443 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4795443 prefixEnd_4795443 := by exact prefixLift 4795443
  have htrace : WordTrace (prefixWord ++ tailWord_4795443) baseStart_4795443 baseEnd_4795443 := by
    simpa [prefixWord, tailWord_4795443, baseEnd_4795443] using wordTrace_append hprefix tailTrace_4795443
  have hstable : (prefixWord ++ tailWord_4795443).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4795443).length < 2 ^ (prefixWord ++ tailWord_4795443).sum := by decide
  have hdescent : baseEnd_4795443 < baseStart_4795443 := by decide
  rcases family_descends (prefixWord ++ tailWord_4795443) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4795470 : List Nat := [4, 1, 1, 1, 1, 3, 1, 4, 2, 3, 2]
def baseStart_4795470 : Nat := 118140960795 + 4795470 * 2 ^ 59
def prefixEnd_4795470 : Nat := 4983230072969 + 3 ^ 40 * 4795470 * 2
def baseEnd_4795470 : Nat := 2462381074216457935271041

theorem tailTrace_4795470 : CollatzResearch.WordTrace tailWord_4795470 prefixEnd_4795470 2462381074216457935271041 := by
  unfold tailWord_4795470
  simp only [CollatzResearch.WordTrace]
  refine ⟨21863144992104833239637983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 116603439957892443944735909 21863144992104833239637983)
  ·
    refine ⟨32794717488157249859456975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21863144992104833239637983 32794717488157249859456975)
    ·
      refine ⟨49192076232235874789185463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32794717488157249859456975 49192076232235874789185463)
      ·
        refine ⟨73788114348353812183778195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49192076232235874789185463 73788114348353812183778195)
        ·
          refine ⟨110682171522530718275667293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 73788114348353812183778195 110682171522530718275667293)
          ·
            refine ⟨41505814320949019353375235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 110682171522530718275667293 41505814320949019353375235)
            ·
              refine ⟨62258721481423529030062853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41505814320949019353375235 62258721481423529030062853)
              ·
                refine ⟨11673510277766911693136785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 62258721481423529030062853 11673510277766911693136785)
                ·
                  refine ⟨8755132708325183769852589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11673510277766911693136785 8755132708325183769852589)
                  ·
                    refine ⟨3283174765621943913694721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8755132708325183769852589 3283174765621943913694721)
                    ·
                      refine ⟨2462381074216457935271041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3283174765621943913694721 2462381074216457935271041)
                      ·
                        rfl

theorem cell23_4795470_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 1, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 1, 4, 2, 3, 2].length) (baseStart_4795470 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4795470 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4795470 prefixEnd_4795470 := by exact prefixLift 4795470
  have htrace : WordTrace (prefixWord ++ tailWord_4795470) baseStart_4795470 baseEnd_4795470 := by
    simpa [prefixWord, tailWord_4795470, baseEnd_4795470] using wordTrace_append hprefix tailTrace_4795470
  have hstable : (prefixWord ++ tailWord_4795470).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4795470).length < 2 ^ (prefixWord ++ tailWord_4795470).sum := by decide
  have hdescent : baseEnd_4795470 < baseStart_4795470 := by decide
  rcases family_descends (prefixWord ++ tailWord_4795470) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4795477 : List Nat := [1, 3, 2, 2, 1, 2, 3, 4, 1, 1, 3]
def baseStart_4795477 : Nat := 118140960795 + 4795477 * 2 ^ 59
def prefixEnd_4795477 : Nat := 4983230072969 + 3 ^ 40 * 4795477 * 2
def baseEnd_4795477 : Nat := 2462384668581039407883509

theorem tailTrace_4795477 : CollatzResearch.WordTrace tailWord_4795477 prefixEnd_4795477 2462384668581039407883509 := by
  unfold tailWord_4795477
  simp only [CollatzResearch.WordTrace]
  refine ⟨174905415247813306112608685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116603610165208870741739123 174905415247813306112608685)
  ·
    refine ⟨65589530717929989792228257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 174905415247813306112608685 65589530717929989792228257)
    ·
      refine ⟨49192148038447492344171193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 65589530717929989792228257 49192148038447492344171193)
      ·
        refine ⟨36894111028835619258128395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49192148038447492344171193 36894111028835619258128395)
        ·
          refine ⟨55341166543253428887192593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36894111028835619258128395 55341166543253428887192593)
          ·
            refine ⟨41505874907440071665394445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 55341166543253428887192593 41505874907440071665394445)
            ·
              refine ⟨15564703090290026874522917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 41505874907440071665394445 15564703090290026874522917)
              ·
                refine ⟨2918381829429380038973047, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15564703090290026874522917 2918381829429380038973047)
                ·
                  refine ⟨4377572744144070058459571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2918381829429380038973047 4377572744144070058459571)
                  ·
                    refine ⟨6566359116216105087689357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4377572744144070058459571 6566359116216105087689357)
                    ·
                      refine ⟨2462384668581039407883509, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6566359116216105087689357 2462384668581039407883509)
                      ·
                        rfl

theorem cell23_4795477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 3, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 3, 4, 1, 1, 3].length) (baseStart_4795477 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4795477 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4795477 prefixEnd_4795477 := by exact prefixLift 4795477
  have htrace : WordTrace (prefixWord ++ tailWord_4795477) baseStart_4795477 baseEnd_4795477 := by
    simpa [prefixWord, tailWord_4795477, baseEnd_4795477] using wordTrace_append hprefix tailTrace_4795477
  have hstable : (prefixWord ++ tailWord_4795477).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4795477).length < 2 ^ (prefixWord ++ tailWord_4795477).sum := by decide
  have hdescent : baseEnd_4795477 < baseStart_4795477 := by decide
  rcases family_descends (prefixWord ++ tailWord_4795477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4795493 : List Nat := [1, 3, 1, 3, 2, 1, 4, 1, 1, 6]
def baseStart_4795493 : Nat := 118140960795 + 4795493 * 2 ^ 59
def prefixEnd_4795493 : Nat := 4983230072969 + 3 ^ 40 * 4795493 * 2
def baseEnd_4795493 : Nat := 820797628090503781761145

theorem tailTrace_4795493 : CollatzResearch.WordTrace tailWord_4795493 prefixEnd_4795493 820797628090503781761145 := by
  unfold tailWord_4795493
  simp only [CollatzResearch.WordTrace]
  refine ⟨174905998815755340845191133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116603999210503560563460755 174905998815755340845191133)
  ·
    refine ⟨65589749555908252816946675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 174905998815755340845191133 65589749555908252816946675)
    ·
      refine ⟨98384624333862379225420013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65589749555908252816946675 98384624333862379225420013)
      ·
        refine ⟨36894234125198392209532505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 98384624333862379225420013 36894234125198392209532505)
        ·
          refine ⟨27670675593898794157149379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36894234125198392209532505 27670675593898794157149379)
          ·
            refine ⟨41506013390848191235724069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27670675593898794157149379 41506013390848191235724069)
            ·
              refine ⟨7782377510784035856698263, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 41506013390848191235724069 7782377510784035856698263)
              ·
                refine ⟨11673566266176053785047395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7782377510784035856698263 11673566266176053785047395)
                ·
                  refine ⟨17510349399264080677571093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11673566266176053785047395 17510349399264080677571093)
                  ·
                    refine ⟨820797628090503781761145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17510349399264080677571093 820797628090503781761145)
                    ·
                      rfl

theorem cell23_4795493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 4, 1, 1, 6].length) (baseStart_4795493 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4795493 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4795493 prefixEnd_4795493 := by exact prefixLift 4795493
  have htrace : WordTrace (prefixWord ++ tailWord_4795493) baseStart_4795493 baseEnd_4795493 := by
    simpa [prefixWord, tailWord_4795493, baseEnd_4795493] using wordTrace_append hprefix tailTrace_4795493
  have hstable : (prefixWord ++ tailWord_4795493).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4795493).length < 2 ^ (prefixWord ++ tailWord_4795493).sum := by decide
  have hdescent : baseEnd_4795493 < baseStart_4795493 := by decide
  rcases family_descends (prefixWord ++ tailWord_4795493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4795503 : List Nat := [1, 1, 2, 1, 3, 3, 1, 3, 3, 2, 3]
def baseStart_4795503 : Nat := 118140960795 + 4795503 * 2 ^ 59
def prefixEnd_4795503 : Nat := 4983230072969 + 3 ^ 40 * 4795503 * 2
def baseEnd_4795503 : Nat := 2462398019078056306158389

theorem tailTrace_4795503 : CollatzResearch.WordTrace tailWord_4795503 prefixEnd_4795503 2462398019078056306158389 := by
  unfold tailWord_4795503
  simp only [CollatzResearch.WordTrace]
  refine ⟨174906363545719112553055163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116604242363812741702036775 174906363545719112553055163)
  ·
    refine ⟨262359545318578668829582745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 174906363545719112553055163 262359545318578668829582745)
    ·
      refine ⟨196769658988934001622187059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 262359545318578668829582745 196769658988934001622187059)
      ·
        refine ⟨295154488483401002433280589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 196769658988934001622187059 295154488483401002433280589)
        ·
          refine ⟨110682933181275375912480221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 295154488483401002433280589 110682933181275375912480221)
          ·
            refine ⟨41506099942978265967180083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 110682933181275375912480221 41506099942978265967180083)
            ·
              refine ⟨62259149914467398950770125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41506099942978265967180083 62259149914467398950770125)
              ·
                refine ⟨23347181217925274606538797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 62259149914467398950770125 23347181217925274606538797)
                ·
                  refine ⟨8755192956721977977452049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23347181217925274606538797 8755192956721977977452049)
                  ·
                    refine ⟨6566394717541483483089037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8755192956721977977452049 6566394717541483483089037)
                    ·
                      refine ⟨2462398019078056306158389, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6566394717541483483089037 2462398019078056306158389)
                      ·
                        rfl

theorem cell23_4795503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 1, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 1, 3, 3, 2, 3].length) (baseStart_4795503 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4795503 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4795503 prefixEnd_4795503 := by exact prefixLift 4795503
  have htrace : WordTrace (prefixWord ++ tailWord_4795503) baseStart_4795503 baseEnd_4795503 := by
    simpa [prefixWord, tailWord_4795503, baseEnd_4795503] using wordTrace_append hprefix tailTrace_4795503
  have hstable : (prefixWord ++ tailWord_4795503).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4795503).length < 2 ^ (prefixWord ++ tailWord_4795503).sum := by decide
  have hdescent : baseEnd_4795503 < baseStart_4795503 := by decide
  rcases family_descends (prefixWord ++ tailWord_4795503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4795510 : List Nat := [5, 1, 1, 2, 1, 1, 2, 2, 4, 4]
def baseStart_4795510 : Nat := 118140960795 + 4795510 * 2 ^ 59
def prefixEnd_4795510 : Nat := 4983230072969 + 3 ^ 40 * 4795510 * 2
def baseEnd_4795510 : Nat := 820800537814212592923619

theorem tailTrace_4795510 : CollatzResearch.WordTrace tailWord_4795510 prefixEnd_4795510 820800537814212592923619 := by
  unfold tailWord_4795510
  simp only [CollatzResearch.WordTrace]
  refine ⟨10931663678543359546784999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 116604412571129168499039989 10931663678543359546784999)
  ·
    refine ⟨16397495517815039320177499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10931663678543359546784999 16397495517815039320177499)
    ·
      refine ⟨24596243276722558980266249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16397495517815039320177499 24596243276722558980266249)
      ·
        refine ⟨18447182457541919235199687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24596243276722558980266249 18447182457541919235199687)
        ·
          refine ⟨27670773686312878852799531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18447182457541919235199687 27670773686312878852799531)
          ·
            refine ⟨41506160529469318279199297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27670773686312878852799531 41506160529469318279199297)
            ·
              refine ⟨31129620397101988709399473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 41506160529469318279199297 31129620397101988709399473)
              ·
                refine ⟨23347215297826491532049605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31129620397101988709399473 23347215297826491532049605)
                ·
                  refine ⟨4377602868342467162259301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 23347215297826491532049605 4377602868342467162259301)
                  ·
                    refine ⟨820800537814212592923619, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4377602868342467162259301 820800537814212592923619)
                    ·
                      rfl

theorem cell23_4795510_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 2, 2, 4, 4].length) (baseStart_4795510 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4795510 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4795510 prefixEnd_4795510 := by exact prefixLift 4795510
  have htrace : WordTrace (prefixWord ++ tailWord_4795510) baseStart_4795510 baseEnd_4795510 := by
    simpa [prefixWord, tailWord_4795510, baseEnd_4795510] using wordTrace_append hprefix tailTrace_4795510
  have hstable : (prefixWord ++ tailWord_4795510).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4795510).length < 2 ^ (prefixWord ++ tailWord_4795510).sum := by decide
  have hdescent : baseEnd_4795510 < baseStart_4795510 := by decide
  rcases family_descends (prefixWord ++ tailWord_4795510) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4795534 : List Nat := [4, 1, 1, 3, 2, 2, 2, 1, 3, 2, 2]
def baseStart_4795534 : Nat := 118140960795 + 4795534 * 2 ^ 59
def prefixEnd_4795534 : Nat := 4983230072969 + 3 ^ 40 * 4795534 * 2
def baseEnd_4795534 : Nat := 2462413936978345684870747

theorem tailTrace_4795534 : CollatzResearch.WordTrace tailWord_4795534 prefixEnd_4795534 2462413936978345684870747 := by
  unfold tailWord_4795534
  simp only [CollatzResearch.WordTrace]
  refine ⟨21863436776075850605929207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 116604996139071203231622437 21863436776075850605929207)
  ·
    refine ⟨32795155164113775908893811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21863436776075850605929207 32795155164113775908893811)
    ·
      refine ⟨49192732746170663863340717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32795155164113775908893811 49192732746170663863340717)
      ·
        refine ⟨18447274779813998948752769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 49192732746170663863340717 18447274779813998948752769)
        ·
          refine ⟨13835456084860499211564577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18447274779813998948752769 13835456084860499211564577)
          ·
            refine ⟨10376592063645374408673433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13835456084860499211564577 10376592063645374408673433)
            ·
              refine ⟨7782444047734030806505075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10376592063645374408673433 7782444047734030806505075)
              ·
                refine ⟨11673666071601046209757613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7782444047734030806505075 11673666071601046209757613)
                ·
                  refine ⟨4377624776850392328659105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11673666071601046209757613 4377624776850392328659105)
                  ·
                    refine ⟨3283218582637794246494329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4377624776850392328659105 3283218582637794246494329)
                    ·
                      refine ⟨2462413936978345684870747, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3283218582637794246494329 2462413936978345684870747)
                      ·
                        rfl

theorem cell23_4795534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 2, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 2, 2, 1, 3, 2, 2].length) (baseStart_4795534 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4795534 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4795534 prefixEnd_4795534 := by exact prefixLift 4795534
  have htrace : WordTrace (prefixWord ++ tailWord_4795534) baseStart_4795534 baseEnd_4795534 := by
    simpa [prefixWord, tailWord_4795534, baseEnd_4795534] using wordTrace_append hprefix tailTrace_4795534
  have hstable : (prefixWord ++ tailWord_4795534).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4795534).length < 2 ^ (prefixWord ++ tailWord_4795534).sum := by decide
  have hdescent : baseEnd_4795534 < baseStart_4795534 := by decide
  rcases family_descends (prefixWord ++ tailWord_4795534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4795536 : List Nat := [2, 1, 1, 1, 1, 1, 4, 3, 2, 7]
def baseStart_4795536 : Nat := 118140960795 + 4795536 * 2 ^ 59
def prefixEnd_4795536 : Nat := 4983230072969 + 3 ^ 40 * 4795536 * 2
def baseEnd_4795536 : Nat := 820804987979884892348579

theorem tailTrace_4795536 : CollatzResearch.WordTrace tailWord_4795536 prefixEnd_4795536 820804987979884892348579 := by
  unfold tailWord_4795536
  simp only [CollatzResearch.WordTrace]
  refine ⟨87453783577299779594503231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116605044769733039459337641 87453783577299779594503231)
  ·
    refine ⟨131180675365949669391754847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87453783577299779594503231 131180675365949669391754847)
    ·
      refine ⟨196771013048924504087632271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 131180675365949669391754847 196771013048924504087632271)
      ·
        refine ⟨295156519573386756131448407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 196771013048924504087632271 295156519573386756131448407)
        ·
          refine ⟨442734779360080134197172611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 295156519573386756131448407 442734779360080134197172611)
          ·
            refine ⟨664102169040120201295758917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 442734779360080134197172611 664102169040120201295758917)
            ·
              refine ⟨124519156695022537742954797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 664102169040120201295758917 124519156695022537742954797)
              ·
                refine ⟨46694683760633451653608049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 124519156695022537742954797 46694683760633451653608049)
                ·
                  refine ⟨35021012820475088740206037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 46694683760633451653608049 35021012820475088740206037)
                  ·
                    refine ⟨820804987979884892348579, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 35021012820475088740206037 820804987979884892348579)
                    ·
                      rfl

theorem cell23_4795536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 4, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 4, 3, 2, 7].length) (baseStart_4795536 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4795536 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4795536 prefixEnd_4795536 := by exact prefixLift 4795536
  have htrace : WordTrace (prefixWord ++ tailWord_4795536) baseStart_4795536 baseEnd_4795536 := by
    simpa [prefixWord, tailWord_4795536, baseEnd_4795536] using wordTrace_append hprefix tailTrace_4795536
  have hstable : (prefixWord ++ tailWord_4795536).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4795536).length < 2 ^ (prefixWord ++ tailWord_4795536).sum := by decide
  have hdescent : baseEnd_4795536 < baseStart_4795536 := by decide
  rcases family_descends (prefixWord ++ tailWord_4795536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4795554 : List Nat := [3, 3, 1, 3, 2, 1, 2, 2, 1, 2, 3]
def baseStart_4795554 : Nat := 118140960795 + 4795554 * 2 ^ 59
def prefixEnd_4795554 : Nat := 4983230072969 + 3 ^ 40 * 4795554 * 2
def baseEnd_4795554 : Nat := 2462424206591435606620655

theorem tailTrace_4795554 : CollatzResearch.WordTrace tailWord_4795554 prefixEnd_4795554 2462424206591435606620655 := by
  unfold tailWord_4795554
  simp only [CollatzResearch.WordTrace]
  refine ⟨43727055917133587065790429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 116605482445689565508774477 43727055917133587065790429)
  ·
    refine ⟨16397645968925095149671411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 43727055917133587065790429 16397645968925095149671411)
    ·
      refine ⟨24596468953387642724507117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16397645968925095149671411 24596468953387642724507117)
      ·
        refine ⟨9223675857520366021690169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24596468953387642724507117 9223675857520366021690169)
        ·
          refine ⟨6917756893140274516267627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9223675857520366021690169 6917756893140274516267627)
          ·
            refine ⟨10376635339710411774401441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6917756893140274516267627 10376635339710411774401441)
            ·
              refine ⟨7782476504782808830801081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10376635339710411774401441 7782476504782808830801081)
              ·
                refine ⟨5836857378587106623100811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7782476504782808830801081 5836857378587106623100811)
                ·
                  refine ⟨8755286067880659934651217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5836857378587106623100811 8755286067880659934651217)
                  ·
                    refine ⟨6566464550910494950988413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8755286067880659934651217 6566464550910494950988413)
                    ·
                      refine ⟨2462424206591435606620655, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6566464550910494950988413 2462424206591435606620655)
                      ·
                        rfl

theorem cell23_4795554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 2, 1, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 2, 1, 2, 2, 1, 2, 3].length) (baseStart_4795554 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4795554 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4795554 prefixEnd_4795554 := by exact prefixLift 4795554
  have htrace : WordTrace (prefixWord ++ tailWord_4795554) baseStart_4795554 baseEnd_4795554 := by
    simpa [prefixWord, tailWord_4795554, baseEnd_4795554] using wordTrace_append hprefix tailTrace_4795554
  have hstable : (prefixWord ++ tailWord_4795554).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4795554).length < 2 ^ (prefixWord ++ tailWord_4795554).sum := by decide
  have hdescent : baseEnd_4795554 < baseStart_4795554 := by decide
  rcases family_descends (prefixWord ++ tailWord_4795554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4795574 : List Nat := [5, 1, 3, 2, 2, 1, 9]
def baseStart_4795574 : Nat := 118140960795 + 4795574 * 2 ^ 59
def prefixEnd_4795574 : Nat := 4983230072969 + 3 ^ 40 * 4795574 * 2
def baseEnd_4795574 : Nat := 30400425632154636152723

theorem tailTrace_4795574 : CollatzResearch.WordTrace tailWord_4795574 prefixEnd_4795574 30400425632154636152723 := by
  unfold tailWord_4795574
  simp only [CollatzResearch.WordTrace]
  refine ⟨10931809570528868229930611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 116605968752307927785926517 10931809570528868229930611)
  ·
    refine ⟨16397714355793302344895917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10931809570528868229930611 16397714355793302344895917)
    ·
      refine ⟨6149142883422488379335969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16397714355793302344895917 6149142883422488379335969)
      ·
        refine ⟨4611857162566866284501977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6149142883422488379335969 4611857162566866284501977)
        ·
          refine ⟨3458892871925149713376483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4611857162566866284501977 3458892871925149713376483)
          ·
            refine ⟨5188339307887724570064725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3458892871925149713376483 5188339307887724570064725)
            ·
              refine ⟨30400425632154636152723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 5188339307887724570064725 30400425632154636152723)
              ·
                rfl

theorem cell23_4795574_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 2, 1, 9].length) (baseStart_4795574 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4795574 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4795574 prefixEnd_4795574 := by exact prefixLift 4795574
  have htrace : WordTrace (prefixWord ++ tailWord_4795574) baseStart_4795574 baseEnd_4795574 := by
    simpa [prefixWord, tailWord_4795574, baseEnd_4795574] using wordTrace_append hprefix tailTrace_4795574
  have hstable : (prefixWord ++ tailWord_4795574).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4795574).length < 2 ^ (prefixWord ++ tailWord_4795574).sum := by decide
  have hdescent : baseEnd_4795574 < baseStart_4795574 := by decide
  rcases family_descends (prefixWord ++ tailWord_4795574) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4795577 : List Nat := [1, 2, 1, 4, 1, 3, 2, 3, 1, 3, 2]
def baseStart_4795577 : Nat := 118140960795 + 4795577 * 2 ^ 59
def prefixEnd_4795577 : Nat := 4983230072969 + 3 ^ 40 * 4795577 * 2
def baseEnd_4795577 : Nat := 2462436016646489016633049

theorem tailTrace_4795577 : CollatzResearch.WordTrace tailWord_4795577 prefixEnd_4795577 2462436016646489016633049 := by
  unfold tailWord_4795577
  simp only [CollatzResearch.WordTrace]
  refine ⟨174909062547451023191248985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116606041698300682127499323 174909062547451023191248985)
  ·
    refine ⟨131181796910588267393436739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 174909062547451023191248985 131181796910588267393436739)
    ·
      refine ⟨196772695365882401090155109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 131181796910588267393436739 196772695365882401090155109)
      ·
        refine ⟨36894880381102950204404083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 196772695365882401090155109 36894880381102950204404083)
        ·
          refine ⟨55342320571654425306606125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36894880381102950204404083 55342320571654425306606125)
          ·
            refine ⟨20753370214370409489977297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 55342320571654425306606125 20753370214370409489977297)
            ·
              refine ⟨15565027660777807117482973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20753370214370409489977297 15565027660777807117482973)
              ·
                refine ⟨5836885372791677669056115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15565027660777807117482973 5836885372791677669056115)
                ·
                  refine ⟨8755328059187516503584173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5836885372791677669056115 8755328059187516503584173)
                  ·
                    refine ⟨3283248022195318688844065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8755328059187516503584173 3283248022195318688844065)
                    ·
                      refine ⟨2462436016646489016633049, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3283248022195318688844065 2462436016646489016633049)
                      ·
                        rfl

theorem cell23_4795577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 2, 3, 1, 3, 2].length) (baseStart_4795577 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4795577 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4795577 prefixEnd_4795577 := by exact prefixLift 4795577
  have htrace : WordTrace (prefixWord ++ tailWord_4795577) baseStart_4795577 baseEnd_4795577 := by
    simpa [prefixWord, tailWord_4795577, baseEnd_4795577] using wordTrace_append hprefix tailTrace_4795577
  have hstable : (prefixWord ++ tailWord_4795577).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4795577).length < 2 ^ (prefixWord ++ tailWord_4795577).sum := by decide
  have hdescent : baseEnd_4795577 < baseStart_4795577 := by decide
  rcases family_descends (prefixWord ++ tailWord_4795577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4795647 : List Nat := [1, 1, 2, 2, 1, 5, 4, 2, 5]
def baseStart_4795647 : Nat := 118140960795 + 4795647 * 2 ^ 59
def prefixEnd_4795647 : Nat := 4983230072969 + 3 ^ 40 * 4795647 * 2
def baseEnd_4795647 : Nat := 273607995588033749195303

theorem tailTrace_4795647 : CollatzResearch.WordTrace tailWord_4795647 prefixEnd_4795647 273607995588033749195303 := by
  unfold tailWord_4795647
  simp only [CollatzResearch.WordTrace]
  refine ⟨174911615657197425146297195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116607743771464950097531463 174911615657197425146297195)
  ·
    refine ⟨262367423485796137719445793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 174911615657197425146297195 262367423485796137719445793)
    ·
      refine ⟨196775567614347103289584345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 262367423485796137719445793 196775567614347103289584345)
      ·
        refine ⟨147581675710760327467188259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 196775567614347103289584345 147581675710760327467188259)
        ·
          refine ⟨221372513566140491200782389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 147581675710760327467188259 221372513566140491200782389)
          ·
            refine ⟨20753673146825671050073349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 221372513566140491200782389 20753673146825671050073349)
            ·
              refine ⟨3891313715029813321888753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 20753673146825671050073349 3891313715029813321888753)
              ·
                refine ⟨2918485286272359991416565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3891313715029813321888753 2918485286272359991416565)
                ·
                  refine ⟨273607995588033749195303, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2918485286272359991416565 273607995588033749195303)
                  ·
                    rfl

theorem cell23_4795647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 4, 2, 5].length) (baseStart_4795647 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4795647 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4795647 prefixEnd_4795647 := by exact prefixLift 4795647
  have htrace : WordTrace (prefixWord ++ tailWord_4795647) baseStart_4795647 baseEnd_4795647 := by
    simpa [prefixWord, tailWord_4795647, baseEnd_4795647] using wordTrace_append hprefix tailTrace_4795647
  have hstable : (prefixWord ++ tailWord_4795647).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4795647).length < 2 ^ (prefixWord ++ tailWord_4795647).sum := by decide
  have hdescent : baseEnd_4795647 < baseStart_4795647 := by decide
  rcases family_descends (prefixWord ++ tailWord_4795647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4795653 : List Nat := [1, 3, 1, 1, 2, 1, 3, 3, 1, 2, 5]
def baseStart_4795653 : Nat := 118140960795 + 4795653 * 2 ^ 59
def prefixEnd_4795653 : Nat := 4983230072969 + 3 ^ 40 * 4795653 * 2
def baseEnd_4795653 : Nat := 2462475041176230719282699

theorem tailTrace_4795653 : CollatzResearch.WordTrace tailWord_4795653 prefixEnd_4795653 2462475041176230719282699 := by
  unfold tailWord_4795653
  simp only [CollatzResearch.WordTrace]
  refine ⟨174911834495175688171015613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116607889663450458780677075 174911834495175688171015613)
  ·
    refine ⟨65591937935690883064130855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 174911834495175688171015613 65591937935690883064130855)
    ·
      refine ⟨98387906903536324596196283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65591937935690883064130855 98387906903536324596196283)
      ·
        refine ⟨147581860355304486894294425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 98387906903536324596196283 147581860355304486894294425)
        ·
          refine ⟨110686395266478365170720819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 147581860355304486894294425 110686395266478365170720819)
          ·
            refine ⟨166029592899717547756081229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 110686395266478365170720819 166029592899717547756081229)
            ·
              refine ⟨62261097337394080408530461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 166029592899717547756081229 62261097337394080408530461)
              ·
                refine ⟨23347911501522780153198923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 62261097337394080408530461 23347911501522780153198923)
                ·
                  refine ⟨35021867252284170229798385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23347911501522780153198923 35021867252284170229798385)
                  ·
                    refine ⟨26266400439213127672348789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 35021867252284170229798385 26266400439213127672348789)
                    ·
                      refine ⟨2462475041176230719282699, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26266400439213127672348789 2462475041176230719282699)
                      ·
                        rfl

theorem cell23_4795653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 3, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 3, 3, 1, 2, 5].length) (baseStart_4795653 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4795653 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4795653 prefixEnd_4795653 := by exact prefixLift 4795653
  have htrace : WordTrace (prefixWord ++ tailWord_4795653) baseStart_4795653 baseEnd_4795653 := by
    simpa [prefixWord, tailWord_4795653, baseEnd_4795653] using wordTrace_append hprefix tailTrace_4795653
  have hstable : (prefixWord ++ tailWord_4795653).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4795653).length < 2 ^ (prefixWord ++ tailWord_4795653).sum := by decide
  have hdescent : baseEnd_4795653 < baseStart_4795653 := by decide
  rcases family_descends (prefixWord ++ tailWord_4795653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4795677 : List Nat := [1, 4, 2, 3, 1, 1, 3, 1, 2, 5]
def baseStart_4795677 : Nat := 118140960795 + 4795677 * 2 ^ 59
def prefixEnd_4795677 : Nat := 4983230072969 + 3 ^ 40 * 4795677 * 2
def baseEnd_4795677 : Nat := 820829121570646208460863

theorem tailTrace_4795677 : CollatzResearch.WordTrace tailWord_4795677 prefixEnd_4795677 820829121570646208460863 := by
  unfold tailWord_4795677
  simp only [CollatzResearch.WordTrace]
  refine ⟨174912709847088740269889285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116608473231392493513259523 174912709847088740269889285)
  ·
    refine ⟨32796133096329138800604241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 174912709847088740269889285 32796133096329138800604241)
    ·
      refine ⟨24597099822246854100453181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32796133096329138800604241 24597099822246854100453181)
      ·
        refine ⟨9223912433342570287669943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24597099822246854100453181 9223912433342570287669943)
        ·
          refine ⟨13835868650013855431504915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9223912433342570287669943 13835868650013855431504915)
          ·
            refine ⟨20753802975020783147257373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13835868650013855431504915 20753802975020783147257373)
            ·
              refine ⟨7782676115632793680221515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20753802975020783147257373 7782676115632793680221515)
              ·
                refine ⟨11674014173449190520332273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7782676115632793680221515 11674014173449190520332273)
                ·
                  refine ⟨8755510630086892890249205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11674014173449190520332273 8755510630086892890249205)
                  ·
                    refine ⟨820829121570646208460863, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8755510630086892890249205 820829121570646208460863)
                    ·
                      rfl

theorem cell23_4795677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 3, 1, 2, 5].length) (baseStart_4795677 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4795677 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4795677 prefixEnd_4795677 := by exact prefixLift 4795677
  have htrace : WordTrace (prefixWord ++ tailWord_4795677) baseStart_4795677 baseEnd_4795677 := by
    simpa [prefixWord, tailWord_4795677, baseEnd_4795677] using wordTrace_append hprefix tailTrace_4795677
  have hstable : (prefixWord ++ tailWord_4795677).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4795677).length < 2 ^ (prefixWord ++ tailWord_4795677).sum := by decide
  have hdescent : baseEnd_4795677 < baseStart_4795677 := by decide
  rcases family_descends (prefixWord ++ tailWord_4795677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4795697 : List Nat := [1, 2, 2, 3, 3, 1, 1, 2, 2, 4, 2]
def baseStart_4795697 : Nat := 118140960795 + 4795697 * 2 ^ 59
def prefixEnd_4795697 : Nat := 4983230072969 + 3 ^ 40 * 4795697 * 2
def baseEnd_4795697 : Nat := 2462497634325028547132497

theorem tailTrace_4795697 : CollatzResearch.WordTrace tailWord_4795697 prefixEnd_4795697 2462497634325028547132497 := by
  unfold tailWord_4795697
  simp only [CollatzResearch.WordTrace]
  refine ⟨174913439307016283685617345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116608959538010855790411563 174913439307016283685617345)
  ·
    refine ⟨131185079480262212764213009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 174913439307016283685617345 131185079480262212764213009)
    ·
      refine ⟨98388809610196659573159757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 131185079480262212764213009 98388809610196659573159757)
      ·
        refine ⟨36895803603823747339934909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 98388809610196659573159757 36895803603823747339934909)
        ·
          refine ⟨13835926351433905252475591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 36895803603823747339934909 13835926351433905252475591)
          ·
            refine ⟨20753889527150857878713387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13835926351433905252475591 20753889527150857878713387)
            ·
              refine ⟨31130834290726286818070081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20753889527150857878713387 31130834290726286818070081)
              ·
                refine ⟨23348125718044715113552561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31130834290726286818070081 23348125718044715113552561)
                ·
                  refine ⟨17511094288533536335164421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23348125718044715113552561 17511094288533536335164421)
                  ·
                    refine ⟨3283330179100038062843329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17511094288533536335164421 3283330179100038062843329)
                    ·
                      refine ⟨2462497634325028547132497, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3283330179100038062843329 2462497634325028547132497)
                      ·
                        rfl

theorem cell23_4795697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 1, 2, 2, 4, 2].length) (baseStart_4795697 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4795697 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4795697 prefixEnd_4795697 := by exact prefixLift 4795697
  have htrace : WordTrace (prefixWord ++ tailWord_4795697) baseStart_4795697 baseEnd_4795697 := by
    simpa [prefixWord, tailWord_4795697, baseEnd_4795697] using wordTrace_append hprefix tailTrace_4795697
  have hstable : (prefixWord ++ tailWord_4795697).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4795697).length < 2 ^ (prefixWord ++ tailWord_4795697).sum := by decide
  have hdescent : baseEnd_4795697 < baseStart_4795697 := by decide
  rcases family_descends (prefixWord ++ tailWord_4795697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4795710 : List Nat := [4, 2, 1, 2, 1, 1, 1, 2, 2, 1, 6]
def baseStart_4795710 : Nat := 118140960795 + 4795710 * 2 ^ 59
def prefixEnd_4795710 : Nat := 4983230072969 + 3 ^ 40 * 4795710 * 2
def baseEnd_4795710 : Nat := 2462504309573536996269937

theorem tailTrace_4795710 : CollatzResearch.WordTrace tailWord_4795710 prefixEnd_4795710 2462504309573536996269937 := by
  unfold tailWord_4795710
  simp only [CollatzResearch.WordTrace]
  refine ⟨21864239181996148363230073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 116609275637312791270560389 21864239181996148363230073)
  ·
    refine ⟨16398179386497111272422555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21864239181996148363230073 16398179386497111272422555)
    ·
      refine ⟨24597269079745666908633833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16398179386497111272422555 24597269079745666908633833)
      ·
        refine ⟨18447951809809250181475375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24597269079745666908633833 18447951809809250181475375)
        ·
          refine ⟨27671927714713875272213063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18447951809809250181475375 27671927714713875272213063)
          ·
            refine ⟨41507891572070812908319595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27671927714713875272213063 41507891572070812908319595)
            ·
              refine ⟨62261837358106219362479393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41507891572070812908319595 62261837358106219362479393)
              ·
                refine ⟨46696378018579664521859545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 62261837358106219362479393 46696378018579664521859545)
                ·
                  refine ⟨35022283513934748391394659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 46696378018579664521859545 35022283513934748391394659)
                  ·
                    refine ⟨52533425270902122587091989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 35022283513934748391394659 52533425270902122587091989)
                    ·
                      refine ⟨2462504309573536996269937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 52533425270902122587091989 2462504309573536996269937)
                      ·
                        rfl

theorem cell23_4795710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 1, 2, 2, 1, 6].length) (baseStart_4795710 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4795710 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4795710 prefixEnd_4795710 := by exact prefixLift 4795710
  have htrace : WordTrace (prefixWord ++ tailWord_4795710) baseStart_4795710 baseEnd_4795710 := by
    simpa [prefixWord, tailWord_4795710, baseEnd_4795710] using wordTrace_append hprefix tailTrace_4795710
  have hstable : (prefixWord ++ tailWord_4795710).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4795710).length < 2 ^ (prefixWord ++ tailWord_4795710).sum := by decide
  have hdescent : baseEnd_4795710 < baseStart_4795710 := by decide
  rcases family_descends (prefixWord ++ tailWord_4795710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4795730 : List Nat := [3, 2, 2, 1, 1, 1, 1, 1, 1, 7, 3]
def baseStart_4795730 : Nat := 118140960795 + 4795730 * 2 ^ 59
def prefixEnd_4795730 : Nat := 4983230072969 + 3 ^ 40 * 4795730 * 2
def baseEnd_4795730 : Nat := 2462514579186626918019845

theorem tailTrace_4795730 : CollatzResearch.WordTrace tailWord_4795730 prefixEnd_4795730 2462514579186626918019845 := by
  unfold tailWord_4795730
  simp only [CollatzResearch.WordTrace]
  refine ⟨43728660728974182580392161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 116609761943931153547712429 43728660728974182580392161)
  ·
    refine ⟨32796495546730636935294121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43728660728974182580392161 32796495546730636935294121)
    ·
      refine ⟨24597371660047977701470591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32796495546730636935294121 24597371660047977701470591)
      ·
        refine ⟨36896057490071966552205887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24597371660047977701470591 36896057490071966552205887)
        ·
          refine ⟨55344086235107949828308831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36896057490071966552205887 55344086235107949828308831)
          ·
            refine ⟨83016129352661924742463247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55344086235107949828308831 83016129352661924742463247)
            ·
              refine ⟨124524194028992887113694871, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 83016129352661924742463247 124524194028992887113694871)
              ·
                refine ⟨186786291043489330670542307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 124524194028992887113694871 186786291043489330670542307)
                ·
                  refine ⟨280179436565233996005813461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 186786291043489330670542307 280179436565233996005813461)
                  ·
                    refine ⟨6566705544497671781386253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 280179436565233996005813461 6566705544497671781386253)
                    ·
                      refine ⟨2462514579186626918019845, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6566705544497671781386253 2462514579186626918019845)
                      ·
                        rfl

theorem cell23_4795730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 1, 1, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 1, 1, 1, 7, 3].length) (baseStart_4795730 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4795730 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4795730 prefixEnd_4795730 := by exact prefixLift 4795730
  have htrace : WordTrace (prefixWord ++ tailWord_4795730) baseStart_4795730 baseEnd_4795730 := by
    simpa [prefixWord, tailWord_4795730, baseEnd_4795730] using wordTrace_append hprefix tailTrace_4795730
  have hstable : (prefixWord ++ tailWord_4795730).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4795730).length < 2 ^ (prefixWord ++ tailWord_4795730).sum := by decide
  have hdescent : baseEnd_4795730 < baseStart_4795730 := by decide
  rcases family_descends (prefixWord ++ tailWord_4795730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4795758 : List Nat := [4, 1, 2, 4, 2, 1, 1, 1, 3, 4]
def baseStart_4795758 : Nat := 118140960795 + 4795758 * 2 ^ 59
def prefixEnd_4795758 : Nat := 4983230072969 + 3 ^ 40 * 4795758 * 2
def baseEnd_4795758 : Nat := 820842985548317602823239

theorem tailTrace_4795758 : CollatzResearch.WordTrace tailWord_4795758 prefixEnd_4795758 820842985548317602823239 := by
  unfold tailWord_4795758
  simp only [CollatzResearch.WordTrace]
  refine ⟨21864458019974411387948491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 116610442773196860735725285 21864458019974411387948491)
  ·
    refine ⟨32796687029961617081922737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21864458019974411387948491 32796687029961617081922737)
    ·
      refine ⟨24597515272471212811442053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32796687029961617081922737 24597515272471212811442053)
      ·
        refine ⟨4612034113588352402145385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 24597515272471212811442053 4612034113588352402145385)
        ·
          refine ⟨3459025585191264301609039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4612034113588352402145385 3459025585191264301609039)
          ·
            refine ⟨5188538377786896452413559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3459025585191264301609039 5188538377786896452413559)
            ·
              refine ⟨7782807566680344678620339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5188538377786896452413559 7782807566680344678620339)
              ·
                refine ⟨11674211350020517017930509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7782807566680344678620339 11674211350020517017930509)
                ·
                  refine ⟨4377829256257693881723941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11674211350020517017930509 4377829256257693881723941)
                  ·
                    refine ⟨820842985548317602823239, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4377829256257693881723941 820842985548317602823239)
                    ·
                      rfl

theorem cell23_4795758_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 2, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 2, 1, 1, 1, 3, 4].length) (baseStart_4795758 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4795758 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4795758 prefixEnd_4795758 := by exact prefixLift 4795758
  have htrace : WordTrace (prefixWord ++ tailWord_4795758) baseStart_4795758 baseEnd_4795758 := by
    simpa [prefixWord, tailWord_4795758, baseEnd_4795758] using wordTrace_append hprefix tailTrace_4795758
  have hstable : (prefixWord ++ tailWord_4795758).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4795758).length < 2 ^ (prefixWord ++ tailWord_4795758).sum := by decide
  have hdescent : baseEnd_4795758 < baseStart_4795758 := by decide
  rcases family_descends (prefixWord ++ tailWord_4795758) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4795763 : List Nat := [1, 1, 1, 2, 2, 1, 2, 1, 2, 10]
def baseStart_4795763 : Nat := 118140960795 + 4795763 * 2 ^ 59
def prefixEnd_4795763 : Nat := 4983230072969 + 3 ^ 40 * 4795763 * 2
def baseEnd_4795763 : Nat := 820843841349408429635731

theorem tailTrace_4795763 : CollatzResearch.WordTrace tailWord_4795763 prefixEnd_4795763 820843841349408429635731 := by
  unfold tailWord_4795763
  simp only [CollatzResearch.WordTrace]
  refine ⟨174915846524777176957519943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116610564349851451305013295 174915846524777176957519943)
  ·
    refine ⟨262373769787165765436279915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 174915846524777176957519943 262373769787165765436279915)
    ·
      refine ⟨393560654680748648154419873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 262373769787165765436279915 393560654680748648154419873)
      ·
        refine ⟨295170491010561486115814905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 393560654680748648154419873 295170491010561486115814905)
        ·
          refine ⟨221377868257921114586861179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 295170491010561486115814905 221377868257921114586861179)
          ·
            refine ⟨332066802386881671880291769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 221377868257921114586861179 332066802386881671880291769)
            ·
              refine ⟨249050101790161253910218827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 332066802386881671880291769 249050101790161253910218827)
              ·
                refine ⟨373575152685241880865328241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 249050101790161253910218827 373575152685241880865328241)
                ·
                  refine ⟨280181364513931410648996181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 373575152685241880865328241 280181364513931410648996181)
                  ·
                    refine ⟨820843841349408429635731, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 280181364513931410648996181 820843841349408429635731)
                    ·
                      rfl

theorem cell23_4795763_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 1, 2, 10].length) (baseStart_4795763 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4795763 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4795763 prefixEnd_4795763 := by exact prefixLift 4795763
  have htrace : WordTrace (prefixWord ++ tailWord_4795763) baseStart_4795763 baseEnd_4795763 := by
    simpa [prefixWord, tailWord_4795763, baseEnd_4795763] using wordTrace_append hprefix tailTrace_4795763
  have hstable : (prefixWord ++ tailWord_4795763).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4795763).length < 2 ^ (prefixWord ++ tailWord_4795763).sum := by decide
  have hdescent : baseEnd_4795763 < baseStart_4795763 := by decide
  rcases family_descends (prefixWord ++ tailWord_4795763) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4795770 : List Nat := [3, 1, 1, 1, 1, 1, 2, 3, 5, 1, 4]
def baseStart_4795770 : Nat := 118140960795 + 4795770 * 2 ^ 59
def prefixEnd_4795770 : Nat := 4983230072969 + 3 ^ 40 * 4795770 * 2
def baseEnd_4795770 : Nat := 2462535118412806761519661

theorem tailTrace_4795770 : CollatzResearch.WordTrace tailWord_4795770 prefixEnd_4795770 2462535118412806761519661 := by
  unfold tailWord_4795770
  simp only [CollatzResearch.WordTrace]
  refine ⟨43729025458937954288256191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 116610734557167878102016509 43729025458937954288256191)
  ·
    refine ⟨65593538188406931432384287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43729025458937954288256191 65593538188406931432384287)
    ·
      refine ⟨98390307282610397148576431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65593538188406931432384287 98390307282610397148576431)
      ·
        refine ⟨147585460923915595722864647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 98390307282610397148576431 147585460923915595722864647)
        ·
          refine ⟨221378191385873393584296971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 147585460923915595722864647 221378191385873393584296971)
          ·
            refine ⟨332067287078810090376445457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 221378191385873393584296971 332067287078810090376445457)
            ·
              refine ⟨249050465309107567782334093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 332067287078810090376445457 249050465309107567782334093)
              ·
                refine ⟨93393924490915337918375285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 249050465309107567782334093 93393924490915337918375285)
                ·
                  refine ⟨8755680421023312929847683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 93393924490915337918375285 8755680421023312929847683)
                  ·
                    refine ⟨13133520631534969394771525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8755680421023312929847683 13133520631534969394771525)
                    ·
                      refine ⟨2462535118412806761519661, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13133520631534969394771525 2462535118412806761519661)
                      ·
                        rfl

theorem cell23_4795770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 3, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 3, 5, 1, 4].length) (baseStart_4795770 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4795770 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4795770 prefixEnd_4795770 := by exact prefixLift 4795770
  have htrace : WordTrace (prefixWord ++ tailWord_4795770) baseStart_4795770 baseEnd_4795770 := by
    simpa [prefixWord, tailWord_4795770, baseEnd_4795770] using wordTrace_append hprefix tailTrace_4795770
  have hstable : (prefixWord ++ tailWord_4795770).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4795770).length < 2 ^ (prefixWord ++ tailWord_4795770).sum := by decide
  have hdescent : baseEnd_4795770 < baseStart_4795770 := by decide
  rcases family_descends (prefixWord ++ tailWord_4795770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4795784 : List Nat := [2, 1, 3, 3, 1, 4, 1, 2, 1, 5]
def baseStart_4795784 : Nat := 118140960795 + 4795784 * 2 ^ 59
def prefixEnd_4795784 : Nat := 4983230072969 + 3 ^ 40 * 4795784 * 2
def baseEnd_4795784 : Nat := 820847435713989902248199

theorem tailTrace_4795784 : CollatzResearch.WordTrace tailWord_4795784 prefixEnd_4795784 820847435713989902248199 := by
  unfold tailWord_4795784
  simp only [CollatzResearch.WordTrace]
  refine ⟨87458306228850548772017203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116611074971800731696022937 87458306228850548772017203)
  ·
    refine ⟨131187459343275823158025805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87458306228850548772017203 131187459343275823158025805)
    ·
      refine ⟨49195297253728433684259677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 131187459343275823158025805 49195297253728433684259677)
      ·
        refine ⟨18448236470148162631597379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 49195297253728433684259677 18448236470148162631597379)
        ·
          refine ⟨27672354705222243947396069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18448236470148162631597379 27672354705222243947396069)
          ·
            refine ⟨5188566507229170740136763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 27672354705222243947396069 5188566507229170740136763)
            ·
              refine ⟨7782849760843756110205145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5188566507229170740136763 7782849760843756110205145)
              ·
                refine ⟨5837137320632817082653859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7782849760843756110205145 5837137320632817082653859)
                ·
                  refine ⟨8755705980949225623980789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5837137320632817082653859 8755705980949225623980789)
                  ·
                    refine ⟨820847435713989902248199, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8755705980949225623980789 820847435713989902248199)
                    ·
                      rfl

theorem cell23_4795784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 4, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 4, 1, 2, 1, 5].length) (baseStart_4795784 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4795784 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4795784 prefixEnd_4795784 := by exact prefixLift 4795784
  have htrace : WordTrace (prefixWord ++ tailWord_4795784) baseStart_4795784 baseEnd_4795784 := by
    simpa [prefixWord, tailWord_4795784, baseEnd_4795784] using wordTrace_append hprefix tailTrace_4795784
  have hstable : (prefixWord ++ tailWord_4795784).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4795784).length < 2 ^ (prefixWord ++ tailWord_4795784).sum := by decide
  have hdescent : baseEnd_4795784 < baseStart_4795784 := by decide
  rcases family_descends (prefixWord ++ tailWord_4795784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4795807 : List Nat := [1, 1, 2, 5, 1, 2, 3, 1, 1, 1, 5]
def baseStart_4795807 : Nat := 118140960795 + 4795807 * 2 ^ 59
def prefixEnd_4795807 : Nat := 4983230072969 + 3 ^ 40 * 4795807 * 2
def baseEnd_4795807 : Nat := 2462554117197023116756991

theorem tailTrace_4795807 : CollatzResearch.WordTrace tailWord_4795807 prefixEnd_4795807 2462554117197023116756991 := by
  unfold tailWord_4795807
  simp only [CollatzResearch.WordTrace]
  refine ⟨174917451336617772472121675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116611634224411848314747783 174917451336617772472121675)
  ·
    refine ⟨262376177004926658708182513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 174917451336617772472121675 262376177004926658708182513)
    ·
      refine ⟨196782132753694994031136885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 262376177004926658708182513 196782132753694994031136885)
      ·
        refine ⟨18448324945658905690419083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 196782132753694994031136885 18448324945658905690419083)
        ·
          refine ⟨27672487418488358535628625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18448324945658905690419083 27672487418488358535628625)
          ·
            refine ⟨20754365563866268901721469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27672487418488358535628625 20754365563866268901721469)
            ·
              refine ⟨7782887086449850838145551, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20754365563866268901721469 7782887086449850838145551)
              ·
                refine ⟨11674330629674776257218327, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7782887086449850838145551 11674330629674776257218327)
                ·
                  refine ⟨17511495944512164385827491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11674330629674776257218327 17511495944512164385827491)
                  ·
                    refine ⟨26267243916768246578741237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17511495944512164385827491 26267243916768246578741237)
                    ·
                      refine ⟨2462554117197023116756991, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26267243916768246578741237 2462554117197023116756991)
                      ·
                        rfl

theorem cell23_4795807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 3, 1, 1, 1, 5].length) (baseStart_4795807 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4795807 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4795807 prefixEnd_4795807 := by exact prefixLift 4795807
  have htrace : WordTrace (prefixWord ++ tailWord_4795807) baseStart_4795807 baseEnd_4795807 := by
    simpa [prefixWord, tailWord_4795807, baseEnd_4795807] using wordTrace_append hprefix tailTrace_4795807
  have hstable : (prefixWord ++ tailWord_4795807).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4795807).length < 2 ^ (prefixWord ++ tailWord_4795807).sum := by decide
  have hdescent : baseEnd_4795807 < baseStart_4795807 := by decide
  rcases family_descends (prefixWord ++ tailWord_4795807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4795810 : List Nat := [3, 3, 1, 2, 1, 13]
def baseStart_4795810 : Nat := 118140960795 + 4795810 * 2 ^ 59
def prefixEnd_4795810 : Nat := 4983230072969 + 3 ^ 40 * 4795810 * 2
def baseEnd_4795810 : Nat := 10133973899748916070039

theorem tailTrace_4795810 : CollatzResearch.WordTrace tailWord_4795810 prefixEnd_4795810 10133973899748916070039 := by
  unfold tailWord_4795810
  simp only [CollatzResearch.WordTrace]
  refine ⟨43729390188901725996120221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 116611707170404602656320589 43729390188901725996120221)
  ·
    refine ⟨16398521320838147248545083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 43729390188901725996120221 16398521320838147248545083)
    ·
      refine ⟨24597781981257220872817625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16398521320838147248545083 24597781981257220872817625)
      ·
        refine ⟨18448336485942915654613219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24597781981257220872817625 18448336485942915654613219)
        ·
          refine ⟨27672504728914373481919829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18448336485942915654613219 27672504728914373481919829)
          ·
            refine ⟨10133973899748916070039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 13 27672504728914373481919829 10133973899748916070039)
            ·
              rfl

theorem cell23_4795810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 13].length) (baseStart_4795810 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4795810 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4795810 prefixEnd_4795810 := by exact prefixLift 4795810
  have htrace : WordTrace (prefixWord ++ tailWord_4795810) baseStart_4795810 baseEnd_4795810 := by
    simpa [prefixWord, tailWord_4795810, baseEnd_4795810] using wordTrace_append hprefix tailTrace_4795810
  have hstable : (prefixWord ++ tailWord_4795810).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4795810).length < 2 ^ (prefixWord ++ tailWord_4795810).sum := by decide
  have hdescent : baseEnd_4795810 < baseStart_4795810 := by decide
  rcases family_descends (prefixWord ++ tailWord_4795810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4795844 : List Nat := [2, 3, 3, 2, 1, 2, 3, 7]
def baseStart_4795844 : Nat := 118140960795 + 4795844 * 2 ^ 59
def prefixEnd_4795844 : Nat := 4983230072969 + 3 ^ 40 * 4795844 * 2
def baseEnd_4795844 : Nat := 91206411703008869333123

theorem tailTrace_4795844 : CollatzResearch.WordTrace tailWord_4795844 prefixEnd_4795844 91206411703008869333123 := by
  unfold tailWord_4795844
  simp only [CollatzResearch.WordTrace]
  refine ⟨87459400418741863895609293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116612533891655818527479057 87459400418741863895609293)
  ·
    refine ⟨32797275157028198960853485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 87459400418741863895609293 32797275157028198960853485)
    ·
      refine ⟨12298978183885574610320057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32797275157028198960853485 12298978183885574610320057)
      ·
        refine ⟨9224233637914180957740043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12298978183885574610320057 9224233637914180957740043)
        ·
          refine ⟨13836350456871271436610065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9224233637914180957740043 13836350456871271436610065)
          ·
            refine ⟨10377262842653453577457549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13836350456871271436610065 10377262842653453577457549)
            ·
              refine ⟨3891473565995045091546581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10377262842653453577457549 3891473565995045091546581)
              ·
                refine ⟨91206411703008869333123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3891473565995045091546581 91206411703008869333123)
                ·
                  rfl

theorem cell23_4795844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 2, 3, 7].length) (baseStart_4795844 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4795844 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4795844 prefixEnd_4795844 := by exact prefixLift 4795844
  have htrace : WordTrace (prefixWord ++ tailWord_4795844) baseStart_4795844 baseEnd_4795844 := by
    simpa [prefixWord, tailWord_4795844, baseEnd_4795844] using wordTrace_append hprefix tailTrace_4795844
  have hstable : (prefixWord ++ tailWord_4795844).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4795844).length < 2 ^ (prefixWord ++ tailWord_4795844).sum := by decide
  have hdescent : baseEnd_4795844 < baseStart_4795844 := by decide
  rcases family_descends (prefixWord ++ tailWord_4795844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4795911 : List Nat := [1, 1, 4, 3, 2, 1, 1, 2, 4, 2, 2]
def baseStart_4795911 : Nat := 118140960795 + 4795911 * 2 ^ 59
def prefixEnd_4795911 : Nat := 4983230072969 + 3 ^ 40 * 4795911 * 2
def baseEnd_4795911 : Nat := 2462607519185090709856513

theorem tailTrace_4795911 : CollatzResearch.WordTrace tailWord_4795911 prefixEnd_4795911 2462607519185090709856513 := by
  unfold tailWord_4795911
  simp only [CollatzResearch.WordTrace]
  refine ⟨174921244528240998233907587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116614163018827332155938391 174921244528240998233907587)
  ·
    refine ⟨262381866792361497350861381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 174921244528240998233907587 262381866792361497350861381)
    ·
      refine ⟨49196600023567780753286509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 262381866792361497350861381 49196600023567780753286509)
      ·
        refine ⟨18448725008837917782482441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 49196600023567780753286509 18448725008837917782482441)
        ·
          refine ⟨13836543756628438336861831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18448725008837917782482441 13836543756628438336861831)
          ·
            refine ⟨20754815634942657505292747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13836543756628438336861831 20754815634942657505292747)
            ·
              refine ⟨31132223452413986257939121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20754815634942657505292747 31132223452413986257939121)
              ·
                refine ⟨23349167589310489693454341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31132223452413986257939121 23349167589310489693454341)
                ·
                  refine ⟨4377968922995716817522689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 23349167589310489693454341 4377968922995716817522689)
                  ·
                    refine ⟨3283476692246787613142017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4377968922995716817522689 3283476692246787613142017)
                    ·
                      refine ⟨2462607519185090709856513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3283476692246787613142017 2462607519185090709856513)
                      ·
                        rfl

theorem cell23_4795911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 1, 2, 4, 2, 2].length) (baseStart_4795911 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4795911 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4795911 prefixEnd_4795911 := by exact prefixLift 4795911
  have htrace : WordTrace (prefixWord ++ tailWord_4795911) baseStart_4795911 baseEnd_4795911 := by
    simpa [prefixWord, tailWord_4795911, baseEnd_4795911] using wordTrace_append hprefix tailTrace_4795911
  have hstable : (prefixWord ++ tailWord_4795911).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4795911).length < 2 ^ (prefixWord ++ tailWord_4795911).sum := by decide
  have hdescent : baseEnd_4795911 < baseStart_4795911 := by decide
  rcases family_descends (prefixWord ++ tailWord_4795911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4795984 : List Nat := [2, 1, 1, 1, 1, 3, 4, 2, 2, 4, 2]
def baseStart_4795984 : Nat := 118140960795 + 4795984 * 2 ^ 59
def prefixEnd_4795984 : Nat := 4983230072969 + 3 ^ 40 * 4795984 * 2
def baseEnd_4795984 : Nat := 2462645003272868924243677

theorem tailTrace_4795984 : CollatzResearch.WordTrace tailWord_4795984 prefixEnd_4795984 2462645003272868924243677 := by
  unfold tailWord_4795984
  simp only [CollatzResearch.WordTrace]
  refine ⟨87461953528488265850657503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116615938037984354467543337 87461953528488265850657503)
  ·
    refine ⟨131192930292732398775986255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87461953528488265850657503 131192930292732398775986255)
    ·
      refine ⟨196789395439098598163979383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 131192930292732398775986255 196789395439098598163979383)
      ·
        refine ⟨295184093158647897245969075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 196789395439098598163979383 295184093158647897245969075)
        ·
          refine ⟨442776139737971845868953613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 295184093158647897245969075 442776139737971845868953613)
          ·
            refine ⟨166041052401739442200857605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 442776139737971845868953613 166041052401739442200857605)
            ·
              refine ⟨31132697325326145412660801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 166041052401739442200857605 31132697325326145412660801)
              ·
                refine ⟨23349522993994609059495601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31132697325326145412660801 23349522993994609059495601)
                ·
                  refine ⟨17512142245495956794621701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23349522993994609059495601 17512142245495956794621701)
                  ·
                    refine ⟨3283526671030491898991569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17512142245495956794621701 3283526671030491898991569)
                    ·
                      refine ⟨2462645003272868924243677, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3283526671030491898991569 2462645003272868924243677)
                      ·
                        rfl

theorem cell23_4795984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 4, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 4, 2, 2, 4, 2].length) (baseStart_4795984 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4795984 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4795984 prefixEnd_4795984 := by exact prefixLift 4795984
  have htrace : WordTrace (prefixWord ++ tailWord_4795984) baseStart_4795984 baseEnd_4795984 := by
    simpa [prefixWord, tailWord_4795984, baseEnd_4795984] using wordTrace_append hprefix tailTrace_4795984
  have hstable : (prefixWord ++ tailWord_4795984).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4795984).length < 2 ^ (prefixWord ++ tailWord_4795984).sum := by decide
  have hdescent : baseEnd_4795984 < baseStart_4795984 := by decide
  rcases family_descends (prefixWord ++ tailWord_4795984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4796021 : List Nat := [1, 3, 4, 2, 1, 2, 1, 1, 1, 4, 3]
def baseStart_4796021 : Nat := 118140960795 + 4796021 * 2 ^ 59
def prefixEnd_4796021 : Nat := 4983230072969 + 3 ^ 40 * 4796021 * 2
def baseEnd_4796021 : Nat := 2462664002057085279481007

theorem tailTrace_4796021 : CollatzResearch.WordTrace tailWord_4796021 prefixEnd_4796021 2462664002057085279481007 := by
  unfold tailWord_4796021
  simp only [CollatzResearch.WordTrace]
  refine ⟨174925256557842487020411917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116616837705228324680274611 174925256557842487020411917)
  ·
    refine ⟨65596971209190932632654469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 174925256557842487020411917 65596971209190932632654469)
    ·
      refine ⟨12299432101723299868622713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 65596971209190932632654469 12299432101723299868622713)
      ·
        refine ⟨9224574076292474901467035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12299432101723299868622713 9224574076292474901467035)
        ·
          refine ⟨13836861114438712352200553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9224574076292474901467035 13836861114438712352200553)
          ·
            refine ⟨10377645835829034264150415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13836861114438712352200553 10377645835829034264150415)
            ·
              refine ⟨15566468753743551396225623, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10377645835829034264150415 15566468753743551396225623)
              ·
                refine ⟨23349703130615327094338435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15566468753743551396225623 23349703130615327094338435)
                ·
                  refine ⟨35024554695922990641507653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23349703130615327094338435 35024554695922990641507653)
                  ·
                    refine ⟨6567104005485560745282685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 35024554695922990641507653 6567104005485560745282685)
                    ·
                      refine ⟨2462664002057085279481007, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6567104005485560745282685 2462664002057085279481007)
                      ·
                        rfl

theorem cell23_4796021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 2, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 2, 1, 1, 1, 4, 3].length) (baseStart_4796021 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4796021 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4796021 prefixEnd_4796021 := by exact prefixLift 4796021
  have htrace : WordTrace (prefixWord ++ tailWord_4796021) baseStart_4796021 baseEnd_4796021 := by
    simpa [prefixWord, tailWord_4796021, baseEnd_4796021] using wordTrace_append hprefix tailTrace_4796021
  have hstable : (prefixWord ++ tailWord_4796021).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4796021).length < 2 ^ (prefixWord ++ tailWord_4796021).sum := by decide
  have hdescent : baseEnd_4796021 < baseStart_4796021 := by decide
  rcases family_descends (prefixWord ++ tailWord_4796021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4796057 : List Nat := [1, 2, 1, 2, 1, 2, 2, 1, 2, 5, 4]
def baseStart_4796057 : Nat := 118140960795 + 4796057 * 2 ^ 59
def prefixEnd_4796057 : Nat := 4983230072969 + 3 ^ 40 * 4796057 * 2
def baseEnd_4796057 : Nat := 2462682487360647138630841

theorem tailTrace_4796057 : CollatzResearch.WordTrace tailWord_4796057 prefixEnd_4796057 2462682487360647138630841 := by
  unfold tailWord_4796057
  simp only [CollatzResearch.WordTrace]
  refine ⟨174926569585712065168722425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116617713057141376779148283 174926569585712065168722425)
  ·
    refine ⟨131194927189284048876541819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 174926569585712065168722425 131194927189284048876541819)
    ·
      refine ⟨196792390783926073314812729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 131194927189284048876541819 196792390783926073314812729)
      ·
        refine ⟨147594293087944554986109547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 196792390783926073314812729 147594293087944554986109547)
        ·
          refine ⟨221391439631916832479164321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 147594293087944554986109547 221391439631916832479164321)
          ·
            refine ⟨166043579723937624359373241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 221391439631916832479164321 166043579723937624359373241)
            ·
              refine ⟨124532684792953218269529931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 166043579723937624359373241 124532684792953218269529931)
              ·
                refine ⟨186799027189429827404294897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 124532684792953218269529931 186799027189429827404294897)
                ·
                  refine ⟨140099270392072370553221173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 186799027189429827404294897 140099270392072370553221173)
                  ·
                    refine ⟨13134306599256784739364485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 140099270392072370553221173 13134306599256784739364485)
                    ·
                      refine ⟨2462682487360647138630841, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13134306599256784739364485 2462682487360647138630841)
                      ·
                        rfl

theorem cell23_4796057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 2, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 2, 1, 2, 5, 4].length) (baseStart_4796057 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4796057 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4796057 prefixEnd_4796057 := by exact prefixLift 4796057
  have htrace : WordTrace (prefixWord ++ tailWord_4796057) baseStart_4796057 baseEnd_4796057 := by
    simpa [prefixWord, tailWord_4796057, baseEnd_4796057] using wordTrace_append hprefix tailTrace_4796057
  have hstable : (prefixWord ++ tailWord_4796057).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4796057).length < 2 ^ (prefixWord ++ tailWord_4796057).sum := by decide
  have hdescent : baseEnd_4796057 < baseStart_4796057 := by decide
  rcases family_descends (prefixWord ++ tailWord_4796057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4796091 : List Nat := [1, 1, 1, 1, 1, 2, 3, 4, 5, 2, 2]
def baseStart_4796091 : Nat := 118140960795 + 4796091 * 2 ^ 59
def prefixEnd_4796091 : Nat := 4983230072969 + 3 ^ 40 * 4796091 * 2
def baseEnd_4796091 : Nat := 2462699945702900005605685

theorem tailTrace_4796091 : CollatzResearch.WordTrace tailWord_4796091 prefixEnd_4796091 2462699945702900005605685 := by
  unfold tailWord_4796091
  simp only [CollatzResearch.WordTrace]
  refine ⟨174927809667588888975460127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116618539778392592650306751 174927809667588888975460127)
  ·
    refine ⟨262391714501383333463190191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 174927809667588888975460127 262391714501383333463190191)
    ·
      refine ⟨393587571752075000194785287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 262391714501383333463190191 393587571752075000194785287)
      ·
        refine ⟨590381357628112500292177931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 393587571752075000194785287 590381357628112500292177931)
        ·
          refine ⟨885572036442168750438266897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 590381357628112500292177931 885572036442168750438266897)
          ·
            refine ⟨664179027331626562828700173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 885572036442168750438266897 664179027331626562828700173)
            ·
              refine ⟨249067135249359961060762565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 664179027331626562828700173 249067135249359961060762565)
              ·
                refine ⟨46700087859254992698892981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 249067135249359961060762565 46700087859254992698892981)
                ·
                  refine ⟨4378133236805155565521217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 46700087859254992698892981 4378133236805155565521217)
                  ·
                    refine ⟨3283599927603866674140913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4378133236805155565521217 3283599927603866674140913)
                    ·
                      refine ⟨2462699945702900005605685, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3283599927603866674140913 2462699945702900005605685)
                      ·
                        rfl

theorem cell23_4796091_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 4, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 4, 5, 2, 2].length) (baseStart_4796091 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4796091 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4796091 prefixEnd_4796091 := by exact prefixLift 4796091
  have htrace : WordTrace (prefixWord ++ tailWord_4796091) baseStart_4796091 baseEnd_4796091 := by
    simpa [prefixWord, tailWord_4796091, baseEnd_4796091] using wordTrace_append hprefix tailTrace_4796091
  have hstable : (prefixWord ++ tailWord_4796091).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4796091).length < 2 ^ (prefixWord ++ tailWord_4796091).sum := by decide
  have hdescent : baseEnd_4796091 < baseStart_4796091 := by decide
  rcases family_descends (prefixWord ++ tailWord_4796091) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4796102 : List Nat := [6, 1, 2, 1, 1, 1, 3, 1, 3, 1, 3]
def baseStart_4796102 : Nat := 118140960795 + 4796102 * 2 ^ 59
def prefixEnd_4796102 : Nat := 4983230072969 + 3 ^ 40 * 4796102 * 2
def baseEnd_4796102 : Nat := 2462705593990099462568135

theorem tailTrace_4796102 : CollatzResearch.WordTrace tailWord_4796102 prefixEnd_4796102 2462705593990099462568135 := by
  unfold tailWord_4796102
  simp only [CollatzResearch.WordTrace]
  refine ⟨5466506589704657432940955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 116618807247032691902740373 5466506589704657432940955)
  ·
    refine ⟨8199759884556986149411433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5466506589704657432940955 8199759884556986149411433)
    ·
      refine ⟨6149819913417739612058575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8199759884556986149411433 6149819913417739612058575)
      ·
        refine ⟨9224729870126609418087863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6149819913417739612058575 9224729870126609418087863)
        ·
          refine ⟨13837094805189914127131795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9224729870126609418087863 13837094805189914127131795)
          ·
            refine ⟨20755642207784871190697693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13837094805189914127131795 20755642207784871190697693)
            ·
              refine ⟨7783365827919326696511635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20755642207784871190697693 7783365827919326696511635)
              ·
                refine ⟨11675048741878990044767453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7783365827919326696511635 11675048741878990044767453)
                ·
                  refine ⟨4378143278204621266787795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11675048741878990044767453 4378143278204621266787795)
                  ·
                    refine ⟨6567214917306931900181693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4378143278204621266787795 6567214917306931900181693)
                    ·
                      refine ⟨2462705593990099462568135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6567214917306931900181693 2462705593990099462568135)
                      ·
                        rfl

theorem cell23_4796102_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 3, 1, 3, 1, 3].length) (baseStart_4796102 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4796102 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4796102 prefixEnd_4796102 := by exact prefixLift 4796102
  have htrace : WordTrace (prefixWord ++ tailWord_4796102) baseStart_4796102 baseEnd_4796102 := by
    simpa [prefixWord, tailWord_4796102, baseEnd_4796102] using wordTrace_append hprefix tailTrace_4796102
  have hstable : (prefixWord ++ tailWord_4796102).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4796102).length < 2 ^ (prefixWord ++ tailWord_4796102).sum := by decide
  have hdescent : baseEnd_4796102 < baseStart_4796102 := by decide
  rcases family_descends (prefixWord ++ tailWord_4796102) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4796114 : List Nat := [3, 2, 2, 2, 2, 1, 1, 10]
def baseStart_4796114 : Nat := 118140960795 + 4796114 * 2 ^ 59
def prefixEnd_4796114 : Nat := 4983230072969 + 3 ^ 40 * 4796114 * 2
def baseEnd_4796114 : Nat := 91211546509553830208077

theorem tailTrace_4796114 : CollatzResearch.WordTrace tailWord_4796114 prefixEnd_4796114 91211546509553830208077 := by
  unfold tailWord_4796114
  simp only [CollatzResearch.WordTrace]
  refine ⟨43732162136626390975886849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 116619099031003709269031597 43732162136626390975886849)
  ·
    refine ⟨32799121602469793231915137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43732162136626390975886849 32799121602469793231915137)
    ·
      refine ⟨24599341201852344923936353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32799121602469793231915137 24599341201852344923936353)
      ·
        refine ⟨18449505901389258692952265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24599341201852344923936353 18449505901389258692952265)
        ·
          refine ⟨13837129426041944019714199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18449505901389258692952265 13837129426041944019714199)
          ·
            refine ⟨20755694139062916029571299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13837129426041944019714199 20755694139062916029571299)
            ·
              refine ⟨31133541208594374044356949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20755694139062916029571299 31133541208594374044356949)
              ·
                refine ⟨91211546509553830208077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 31133541208594374044356949 91211546509553830208077)
                ·
                  rfl

theorem cell23_4796114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 1, 10].length) (baseStart_4796114 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4796114 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4796114 prefixEnd_4796114 := by exact prefixLift 4796114
  have htrace : WordTrace (prefixWord ++ tailWord_4796114) baseStart_4796114 baseEnd_4796114 := by
    simpa [prefixWord, tailWord_4796114, baseEnd_4796114] using wordTrace_append hprefix tailTrace_4796114
  have hstable : (prefixWord ++ tailWord_4796114).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4796114).length < 2 ^ (prefixWord ++ tailWord_4796114).sum := by decide
  have hdescent : baseEnd_4796114 < baseStart_4796114 := by decide
  rcases family_descends (prefixWord ++ tailWord_4796114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4796141 : List Nat := [1, 5, 1, 2, 1, 2, 1, 1, 3, 3, 3]
def baseStart_4796141 : Nat := 118140960795 + 4796141 * 2 ^ 59
def prefixEnd_4796141 : Nat := 4983230072969 + 3 ^ 40 * 4796141 * 2
def baseEnd_4796141 : Nat := 2462725619735624809980455

theorem tailTrace_4796141 : CollatzResearch.WordTrace tailWord_4796141 prefixEnd_4796141 2462725619735624809980455 := by
  unfold tailWord_4796141
  simp only [CollatzResearch.WordTrace]
  refine ⟨174929633317407747514780277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116619755544938498343186851 174929633317407747514780277)
  ·
    refine ⟨16399653123506976329510651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 174929633317407747514780277 16399653123506976329510651)
    ·
      refine ⟨24599479685260464494265977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16399653123506976329510651 24599479685260464494265977)
      ·
        refine ⟨18449609763945348370699483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24599479685260464494265977 18449609763945348370699483)
        ·
          refine ⟨27674414645918022556049225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18449609763945348370699483 27674414645918022556049225)
          ·
            refine ⟨20755810984438516917036919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27674414645918022556049225 20755810984438516917036919)
            ·
              refine ⟨31133716476657775375555379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20755810984438516917036919 31133716476657775375555379)
              ·
                refine ⟨46700574714986663063333069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31133716476657775375555379 46700574714986663063333069)
                ·
                  refine ⟨17512715518119998648749901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 46700574714986663063333069 17512715518119998648749901)
                  ·
                    refine ⟨6567268319294999493281213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17512715518119998648749901 6567268319294999493281213)
                    ·
                      refine ⟨2462725619735624809980455, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6567268319294999493281213 2462725619735624809980455)
                      ·
                        rfl

theorem cell23_4796141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 1, 1, 3, 3, 3].length) (baseStart_4796141 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4796141 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4796141 prefixEnd_4796141 := by exact prefixLift 4796141
  have htrace : WordTrace (prefixWord ++ tailWord_4796141) baseStart_4796141 baseEnd_4796141 := by
    simpa [prefixWord, tailWord_4796141, baseEnd_4796141] using wordTrace_append hprefix tailTrace_4796141
  have hstable : (prefixWord ++ tailWord_4796141).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4796141).length < 2 ^ (prefixWord ++ tailWord_4796141).sum := by decide
  have hdescent : baseEnd_4796141 < baseStart_4796141 := by decide
  rcases family_descends (prefixWord ++ tailWord_4796141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4796174 : List Nat := [4, 1, 1, 2, 1, 1, 3, 1, 1, 8]
def baseStart_4796174 : Nat := 118140960795 + 4796174 * 2 ^ 59
def prefixEnd_4796174 : Nat := 4983230072969 + 3 ^ 40 * 4796174 * 2
def baseEnd_4796174 : Nat := 820914188199074393622601

theorem tailTrace_4796174 : CollatzResearch.WordTrace tailWord_4796174 prefixEnd_4796174 820914188199074393622601 := by
  unfold tailWord_4796174
  simp only [CollatzResearch.WordTrace]
  refine ⟨21866354615786024268841447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 116620557950858796100487717 21866354615786024268841447)
  ·
    refine ⟨32799531923679036403262171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21866354615786024268841447 32799531923679036403262171)
    ·
      refine ⟨49199297885518554604893257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32799531923679036403262171 49199297885518554604893257)
      ·
        refine ⟨36899473414138915953669943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49199297885518554604893257 36899473414138915953669943)
        ·
          refine ⟨55349210121208373930504915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36899473414138915953669943 55349210121208373930504915)
          ·
            refine ⟨83023815181812560895757373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55349210121208373930504915 83023815181812560895757373)
            ·
              refine ⟨31133930693179710335909015, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 83023815181812560895757373 31133930693179710335909015)
              ·
                refine ⟨46700896039769565503863523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31133930693179710335909015 46700896039769565503863523)
                ·
                  refine ⟨70051344059654348255795285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 46700896039769565503863523 70051344059654348255795285)
                  ·
                    refine ⟨820914188199074393622601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 70051344059654348255795285 820914188199074393622601)
                    ·
                      rfl

theorem cell23_4796174_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 3, 1, 1, 8].length) (baseStart_4796174 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4796174 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4796174 prefixEnd_4796174 := by exact prefixLift 4796174
  have htrace : WordTrace (prefixWord ++ tailWord_4796174) baseStart_4796174 baseEnd_4796174 := by
    simpa [prefixWord, tailWord_4796174, baseEnd_4796174] using wordTrace_append hprefix tailTrace_4796174
  have hstable : (prefixWord ++ tailWord_4796174).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4796174).length < 2 ^ (prefixWord ++ tailWord_4796174).sum := by decide
  have hdescent : baseEnd_4796174 < baseStart_4796174 := by decide
  rcases family_descends (prefixWord ++ tailWord_4796174) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4796184 : List Nat := [2, 1, 2, 3, 1, 1, 2, 1, 4, 1, 5]
def baseStart_4796184 : Nat := 118140960795 + 4796184 * 2 ^ 59
def prefixEnd_4796184 : Nat := 4983230072969 + 3 ^ 40 * 4796184 * 2
def baseEnd_4796184 : Nat := 2462747699403768141742757

theorem tailTrace_4796184 : CollatzResearch.WordTrace tailWord_4796184 prefixEnd_4796184 2462747699403768141742757 := by
  unfold tailWord_4796184
  simp only [CollatzResearch.WordTrace]
  refine ⟨87465600828125982929297803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116620801104167977239063737 87465600828125982929297803)
  ·
    refine ⟨131198401242188974393946705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87465600828125982929297803 131198401242188974393946705)
    ·
      refine ⟨98398800931641730795460029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 131198401242188974393946705 98398800931641730795460029)
      ·
        refine ⟨36899550349365649048297511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 98398800931641730795460029 36899550349365649048297511)
        ·
          refine ⟨55349325524048473572446267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36899550349365649048297511 55349325524048473572446267)
          ·
            refine ⟨83023988286072710358669401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55349325524048473572446267 83023988286072710358669401)
            ·
              refine ⟨62267991214554532769002051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 83023988286072710358669401 62267991214554532769002051)
              ·
                refine ⟨93401986821831799153503077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 62267991214554532769002051 93401986821831799153503077)
                ·
                  refine ⟨17512872529093462341281827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 93401986821831799153503077 17512872529093462341281827)
                  ·
                    refine ⟨26269308793640193511922741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17512872529093462341281827 26269308793640193511922741)
                    ·
                      refine ⟨2462747699403768141742757, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26269308793640193511922741 2462747699403768141742757)
                      ·
                        rfl

theorem cell23_4796184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 2, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 2, 1, 4, 1, 5].length) (baseStart_4796184 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4796184 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4796184 prefixEnd_4796184 := by exact prefixLift 4796184
  have htrace : WordTrace (prefixWord ++ tailWord_4796184) baseStart_4796184 baseEnd_4796184 := by
    simpa [prefixWord, tailWord_4796184, baseEnd_4796184] using wordTrace_append hprefix tailTrace_4796184
  have hstable : (prefixWord ++ tailWord_4796184).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4796184).length < 2 ^ (prefixWord ++ tailWord_4796184).sum := by decide
  have hdescent : baseEnd_4796184 < baseStart_4796184 := by decide
  rcases family_descends (prefixWord ++ tailWord_4796184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4796221 : List Nat := [1, 4, 1, 4, 1, 1, 1, 3, 7]
def baseStart_4796221 : Nat := 118140960795 + 4796221 * 2 ^ 59
def prefixEnd_4796221 : Nat := 4983230072969 + 3 ^ 40 * 4796221 * 2
def baseEnd_4796221 : Nat := 273640744243109388553343

theorem tailTrace_4796221 : CollatzResearch.WordTrace tailWord_4796221 prefixEnd_4796221 273640744243109388553343 := by
  unfold tailWord_4796221
  simp only [CollatzResearch.WordTrace]
  refine ⟨174932551157117921177692517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116621700771411947451795011 174932551157117921177692517)
  ·
    refine ⟨32799853341959610220817347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 174932551157117921177692517 32799853341959610220817347)
    ·
      refine ⟨49199780012939415331226021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32799853341959610220817347 49199780012939415331226021)
      ·
        refine ⟨9224958752426140374604879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 49199780012939415331226021 9224958752426140374604879)
        ·
          refine ⟨13837438128639210561907319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9224958752426140374604879 13837438128639210561907319)
          ·
            refine ⟨20756157192958815842860979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13837438128639210561907319 20756157192958815842860979)
            ·
              refine ⟨31134235789438223764291469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20756157192958815842860979 31134235789438223764291469)
              ·
                refine ⟨11675338421039333911609301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 31134235789438223764291469 11675338421039333911609301)
                ·
                  refine ⟨273640744243109388553343, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11675338421039333911609301 273640744243109388553343)
                  ·
                    rfl

theorem cell23_4796221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 1, 3, 7].length) (baseStart_4796221 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4796221 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4796221 prefixEnd_4796221 := by exact prefixLift 4796221
  have htrace : WordTrace (prefixWord ++ tailWord_4796221) baseStart_4796221 baseEnd_4796221 := by
    simpa [prefixWord, tailWord_4796221, baseEnd_4796221] using wordTrace_append hprefix tailTrace_4796221
  have hstable : (prefixWord ++ tailWord_4796221).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4796221).length < 2 ^ (prefixWord ++ tailWord_4796221).sum := by decide
  have hdescent : baseEnd_4796221 < baseStart_4796221 := by decide
  rcases family_descends (prefixWord ++ tailWord_4796221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4796231 : List Nat := [1, 1, 4, 1, 2, 1, 4, 1, 2, 3, 3]
def baseStart_4796231 : Nat := 118140960795 + 4796231 * 2 ^ 59
def prefixEnd_4796231 : Nat := 4983230072969 + 3 ^ 40 * 4796231 * 2
def baseEnd_4796231 : Nat := 2462771832994529457855041

theorem tailTrace_4796231 : CollatzResearch.WordTrace tailWord_4796231 prefixEnd_4796231 2462771832994529457855041 := by
  unfold tailWord_4796231
  simp only [CollatzResearch.WordTrace]
  refine ⟨174932915887081692885556547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116621943924721128590371031 174932915887081692885556547)
  ·
    refine ⟨262399373830622539328334821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 174932915887081692885556547 262399373830622539328334821)
    ·
      refine ⟨49199882593241726124062779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 262399373830622539328334821 49199882593241726124062779)
      ·
        refine ⟨73799823889862589186094169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49199882593241726124062779 73799823889862589186094169)
        ·
          refine ⟨55349867917396941889570627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 73799823889862589186094169 55349867917396941889570627)
          ·
            refine ⟨83024801876095412834355941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55349867917396941889570627 83024801876095412834355941)
            ·
              refine ⟨15567150351767889906441739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 83024801876095412834355941 15567150351767889906441739)
              ·
                refine ⟨23350725527651834859662609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15567150351767889906441739 23350725527651834859662609)
                ·
                  refine ⟨17513044145738876144746957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23350725527651834859662609 17513044145738876144746957)
                  ·
                    refine ⟨6567391554652078554280109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17513044145738876144746957 6567391554652078554280109)
                    ·
                      refine ⟨2462771832994529457855041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6567391554652078554280109 2462771832994529457855041)
                      ·
                        rfl

theorem cell23_4796231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 4, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 4, 1, 2, 3, 3].length) (baseStart_4796231 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4796231 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4796231 prefixEnd_4796231 := by exact prefixLift 4796231
  have htrace : WordTrace (prefixWord ++ tailWord_4796231) baseStart_4796231 baseEnd_4796231 := by
    simpa [prefixWord, tailWord_4796231, baseEnd_4796231] using wordTrace_append hprefix tailTrace_4796231
  have hstable : (prefixWord ++ tailWord_4796231).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4796231).length < 2 ^ (prefixWord ++ tailWord_4796231).sum := by decide
  have hdescent : baseEnd_4796231 < baseStart_4796231 := by decide
  rcases family_descends (prefixWord ++ tailWord_4796231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4796232 : List Nat := [2, 1, 3, 1, 1, 5, 3, 1, 2, 2, 2]
def baseStart_4796232 : Nat := 118140960795 + 4796232 * 2 ^ 59
def prefixEnd_4796232 : Nat := 4983230072969 + 3 ^ 40 * 4796232 * 2
def baseEnd_4796232 : Nat := 2462772346475183953942537

theorem tailTrace_4796232 : CollatzResearch.WordTrace tailWord_4796232 prefixEnd_4796232 2462772346475183953942537 := by
  unfold tailWord_4796232
  simp only [CollatzResearch.WordTrace]
  refine ⟨87466476180039035028171475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116621968240052046704228633 87466476180039035028171475)
  ·
    refine ⟨131199714270058552542257213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87466476180039035028171475 131199714270058552542257213)
    ·
      refine ⟨49199892851271957203346455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 131199714270058552542257213 49199892851271957203346455)
      ·
        refine ⟨73799839276907935805019683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49199892851271957203346455 73799839276907935805019683)
        ·
          refine ⟨110699758915361903707529525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 73799839276907935805019683 110699758915361903707529525)
          ·
            refine ⟨10378102398315178472580893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 110699758915361903707529525 10378102398315178472580893)
            ·
              refine ⟨3891788399368191927217835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10378102398315178472580893 3891788399368191927217835)
              ·
                refine ⟨5837682599052287890826753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3891788399368191927217835 5837682599052287890826753)
                ·
                  refine ⟨4378261949289215918120065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5837682599052287890826753 4378261949289215918120065)
                  ·
                    refine ⟨3283696461966911938590049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4378261949289215918120065 3283696461966911938590049)
                    ·
                      refine ⟨2462772346475183953942537, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3283696461966911938590049 2462772346475183953942537)
                      ·
                        rfl

theorem cell23_4796232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 5, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 5, 3, 1, 2, 2, 2].length) (baseStart_4796232 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4796232 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4796232 prefixEnd_4796232 := by exact prefixLift 4796232
  have htrace : WordTrace (prefixWord ++ tailWord_4796232) baseStart_4796232 baseEnd_4796232 := by
    simpa [prefixWord, tailWord_4796232, baseEnd_4796232] using wordTrace_append hprefix tailTrace_4796232
  have hstable : (prefixWord ++ tailWord_4796232).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4796232).length < 2 ^ (prefixWord ++ tailWord_4796232).sum := by decide
  have hdescent : baseEnd_4796232 < baseStart_4796232 := by decide
  rcases family_descends (prefixWord ++ tailWord_4796232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4796234 : List Nat := [3, 1, 2, 1, 1, 1, 3, 1, 3, 7]
def baseStart_4796234 : Nat := 118140960795 + 4796234 * 2 ^ 59
def prefixEnd_4796234 : Nat := 4983230072969 + 3 ^ 40 * 4796234 * 2
def baseEnd_4796234 : Nat := 820924457812164315372509

theorem tailTrace_4796234 : CollatzResearch.WordTrace tailWord_4796234 prefixEnd_4796234 820924457812164315372509 := by
  unfold tailWord_4796234
  simp only [CollatzResearch.WordTrace]
  refine ⟨43733256326517706099478939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 116622016870713882931943837 43733256326517706099478939)
  ·
    refine ⟨65599884489776559149218409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43733256326517706099478939 65599884489776559149218409)
    ·
      refine ⟨49199913367332419361913807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 65599884489776559149218409 49199913367332419361913807)
      ·
        refine ⟨73799870050998629042870711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49199913367332419361913807 73799870050998629042870711)
        ·
          refine ⟨110699805076497943564306067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 73799870050998629042870711 110699805076497943564306067)
          ·
            refine ⟨166049707614746915346459101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 110699805076497943564306067 166049707614746915346459101)
            ·
              refine ⟨62268640355530093254922163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 166049707614746915346459101 62268640355530093254922163)
              ·
                refine ⟨93402960533295139882383245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 62268640355530093254922163 93402960533295139882383245)
                ·
                  refine ⟨35026110199985677455893717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 93402960533295139882383245 35026110199985677455893717)
                  ·
                    refine ⟨820924457812164315372509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 35026110199985677455893717 820924457812164315372509)
                    ·
                      rfl

theorem cell23_4796234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 3, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 3, 1, 3, 7].length) (baseStart_4796234 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4796234 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4796234 prefixEnd_4796234 := by exact prefixLift 4796234
  have htrace : WordTrace (prefixWord ++ tailWord_4796234) baseStart_4796234 baseEnd_4796234 := by
    simpa [prefixWord, tailWord_4796234, baseEnd_4796234] using wordTrace_append hprefix tailTrace_4796234
  have hstable : (prefixWord ++ tailWord_4796234).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4796234).length < 2 ^ (prefixWord ++ tailWord_4796234).sum := by decide
  have hdescent : baseEnd_4796234 < baseStart_4796234 := by decide
  rcases family_descends (prefixWord ++ tailWord_4796234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4796338 : List Nat := [3, 2, 1, 1, 1, 1, 1, 2, 7, 1, 3]
def baseStart_4796338 : Nat := 118140960795 + 4796338 * 2 ^ 59
def prefixEnd_4796338 : Nat := 4983230072969 + 3 ^ 40 * 4796338 * 2
def baseEnd_4796338 : Nat := 2462826775424560539217049

theorem tailTrace_4796338 : CollatzResearch.WordTrace tailWord_4796338 prefixEnd_4796338 2462826775424560539217049 := by
  unfold tailWord_4796338
  simp only [CollatzResearch.WordTrace]
  refine ⟨43734204624423512539925417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 116624545665129366773134445 43734204624423512539925417)
  ·
    refine ⟨32800653468317634404944063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43734204624423512539925417 32800653468317634404944063)
    ·
      refine ⟨49200980202476451607416095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32800653468317634404944063 49200980202476451607416095)
      ·
        refine ⟨73801470303714677411124143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49200980202476451607416095 73801470303714677411124143)
        ·
          refine ⟨110702205455572016116686215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 73801470303714677411124143 110702205455572016116686215)
          ·
            refine ⟨166053308183358024175029323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 110702205455572016116686215 166053308183358024175029323)
            ·
              refine ⟨249079962275037036262543985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 166053308183358024175029323 249079962275037036262543985)
              ·
                refine ⟨186809971706277777196907989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 249079962275037036262543985 186809971706277777196907989)
                ·
                  refine ⟨4378358711865885403052531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 186809971706277777196907989 4378358711865885403052531)
                  ·
                    refine ⟨6567538067798828104578797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4378358711865885403052531 6567538067798828104578797)
                    ·
                      refine ⟨2462826775424560539217049, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6567538067798828104578797 2462826775424560539217049)
                      ·
                        rfl

theorem cell23_4796338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 2, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 2, 7, 1, 3].length) (baseStart_4796338 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4796338 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4796338 prefixEnd_4796338 := by exact prefixLift 4796338
  have htrace : WordTrace (prefixWord ++ tailWord_4796338) baseStart_4796338 baseEnd_4796338 := by
    simpa [prefixWord, tailWord_4796338, baseEnd_4796338] using wordTrace_append hprefix tailTrace_4796338
  have hstable : (prefixWord ++ tailWord_4796338).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4796338).length < 2 ^ (prefixWord ++ tailWord_4796338).sum := by decide
  have hdescent : baseEnd_4796338 < baseStart_4796338 := by decide
  rcases family_descends (prefixWord ++ tailWord_4796338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4796388 : List Nat := [2, 3, 1, 1, 1, 1, 5, 1, 4, 4]
def baseStart_4796388 : Nat := 118140960795 + 4796388 * 2 ^ 59
def prefixEnd_4796388 : Nat := 4983230072969 + 3 ^ 40 * 4796388 * 2
def baseEnd_4796388 : Nat := 820950816485761781197273

theorem tailTrace_4796388 : CollatzResearch.WordTrace tailWord_4796388 prefixEnd_4796388 820950816485761781197273 := by
  unfold tailWord_4796388
  simp only [CollatzResearch.WordTrace]
  refine ⟨87469321073756454349510909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116625761431675272466014545 87469321073756454349510909)
  ·
    refine ⟨32800995402658670381066591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 87469321073756454349510909 32800995402658670381066591)
    ·
      refine ⟨49201493103988005571599887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32800995402658670381066591 49201493103988005571599887)
      ·
        refine ⟨73802239655982008357399831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49201493103988005571599887 73802239655982008357399831)
        ·
          refine ⟨110703359483973012536099747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 73802239655982008357399831 110703359483973012536099747)
          ·
            refine ⟨166055039225959518804149621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 110703359483973012536099747 166055039225959518804149621)
            ·
              refine ⟨15567659927433704887889027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 166055039225959518804149621 15567659927433704887889027)
              ·
                refine ⟨23351489891150557331833541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15567659927433704887889027 23351489891150557331833541)
                ·
                  refine ⟨4378404354590729499718789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 23351489891150557331833541 4378404354590729499718789)
                  ·
                    refine ⟨820950816485761781197273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4378404354590729499718789 820950816485761781197273)
                    ·
                      rfl

theorem cell23_4796388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 5, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 5, 1, 4, 4].length) (baseStart_4796388 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4796388 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4796388 prefixEnd_4796388 := by exact prefixLift 4796388
  have htrace : WordTrace (prefixWord ++ tailWord_4796388) baseStart_4796388 baseEnd_4796388 := by
    simpa [prefixWord, tailWord_4796388, baseEnd_4796388] using wordTrace_append hprefix tailTrace_4796388
  have hstable : (prefixWord ++ tailWord_4796388).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4796388).length < 2 ^ (prefixWord ++ tailWord_4796388).sum := by decide
  have hdescent : baseEnd_4796388 < baseStart_4796388 := by decide
  rcases family_descends (prefixWord ++ tailWord_4796388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4796398 : List Nat := [4, 1, 2, 1, 3, 1, 1, 1, 3, 1, 5]
def baseStart_4796398 : Nat := 118140960795 + 4796398 * 2 ^ 59
def prefixEnd_4796398 : Nat := 4983230072969 + 3 ^ 40 * 4796398 * 2
def baseEnd_4796398 : Nat := 2462857584263830304466773

theorem tailTrace_4796398 : CollatzResearch.WordTrace tailWord_4796398 prefixEnd_4796398 2462857584263830304466773 := by
  unfold tailWord_4796398
  simp only [CollatzResearch.WordTrace]
  refine ⟨21867375859684585050860731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 116626004584984453604590565 21867375859684585050860731)
  ·
    refine ⟨32801063789526877576291097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21867375859684585050860731 32801063789526877576291097)
    ·
      refine ⟨24600797842145158182218323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32801063789526877576291097 24600797842145158182218323)
      ·
        refine ⟨36901196763217737273327485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24600797842145158182218323 36901196763217737273327485)
        ·
          refine ⟨13837948786206651477497807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 36901196763217737273327485 13837948786206651477497807)
          ·
            refine ⟨20756923179309977216246711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13837948786206651477497807 20756923179309977216246711)
            ·
              refine ⟨31135384768964965824370067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20756923179309977216246711 31135384768964965824370067)
              ·
                refine ⟨46703077153447448736555101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31135384768964965824370067 46703077153447448736555101)
                ·
                  refine ⟨17513653932542793276208163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 46703077153447448736555101 17513653932542793276208163)
                  ·
                    refine ⟨26270480898814189914312245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17513653932542793276208163 26270480898814189914312245)
                    ·
                      refine ⟨2462857584263830304466773, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26270480898814189914312245 2462857584263830304466773)
                      ·
                        rfl

theorem cell23_4796398_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 1, 1, 3, 1, 5].length) (baseStart_4796398 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4796398 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4796398 prefixEnd_4796398 := by exact prefixLift 4796398
  have htrace : WordTrace (prefixWord ++ tailWord_4796398) baseStart_4796398 baseEnd_4796398 := by
    simpa [prefixWord, tailWord_4796398, baseEnd_4796398] using wordTrace_append hprefix tailTrace_4796398
  have hstable : (prefixWord ++ tailWord_4796398).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4796398).length < 2 ^ (prefixWord ++ tailWord_4796398).sum := by decide
  have hdescent : baseEnd_4796398 < baseStart_4796398 := by decide
  rcases family_descends (prefixWord ++ tailWord_4796398) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4796408 : List Nat := [2, 1, 2, 1, 1, 3, 5, 1, 1, 2, 4]
def baseStart_4796408 : Nat := 118140960795 + 4796408 * 2 ^ 59
def prefixEnd_4796408 : Nat := 4983230072969 + 3 ^ 40 * 4796408 * 2
def baseEnd_4796408 : Nat := 2462862719070375265341727

theorem tailTrace_4796408 : CollatzResearch.WordTrace tailWord_4796408 prefixEnd_4796408 2462862719070375265341727 := by
  unfold tailWord_4796408
  simp only [CollatzResearch.WordTrace]
  refine ⟨87469685803720226057374939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116626247738293634743166585 87469685803720226057374939)
  ·
    refine ⟨131204528705580339086062409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87469685803720226057374939 131204528705580339086062409)
    ·
      refine ⟨98403396529185254314546807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 131204528705580339086062409 98403396529185254314546807)
      ·
        refine ⟨147605094793777881471820211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 98403396529185254314546807 147605094793777881471820211)
        ·
          refine ⟨221407642190666822207730317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 147605094793777881471820211 221407642190666822207730317)
          ·
            refine ⟨83027865821500058327898869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 221407642190666822207730317 83027865821500058327898869)
            ·
              refine ⟨7783862420765630468240519, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 83027865821500058327898869 7783862420765630468240519)
              ·
                refine ⟨11675793631148445702360779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7783862420765630468240519 11675793631148445702360779)
                ·
                  refine ⟨17513690446722668553541169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11675793631148445702360779 17513690446722668553541169)
                  ·
                    refine ⟨13135267835042001415155877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17513690446722668553541169 13135267835042001415155877)
                    ·
                      refine ⟨2462862719070375265341727, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13135267835042001415155877 2462862719070375265341727)
                      ·
                        rfl

theorem cell23_4796408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 5, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 5, 1, 1, 2, 4].length) (baseStart_4796408 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4796408 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4796408 prefixEnd_4796408 := by exact prefixLift 4796408
  have htrace : WordTrace (prefixWord ++ tailWord_4796408) baseStart_4796408 baseEnd_4796408 := by
    simpa [prefixWord, tailWord_4796408, baseEnd_4796408] using wordTrace_append hprefix tailTrace_4796408
  have hstable : (prefixWord ++ tailWord_4796408).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4796408).length < 2 ^ (prefixWord ++ tailWord_4796408).sum := by decide
  have hdescent : baseEnd_4796408 < baseStart_4796408 := by decide
  rcases family_descends (prefixWord ++ tailWord_4796408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4796428 : List Nat := [2, 2, 1, 2, 3, 1, 2, 1, 3, 3, 3]
def baseStart_4796428 : Nat := 118140960795 + 4796428 * 2 ^ 59
def prefixEnd_4796428 : Nat := 4983230072969 + 3 ^ 40 * 4796428 * 2
def baseEnd_4796428 : Nat := 2462872988683465187091635

theorem tailTrace_4796428 : CollatzResearch.WordTrace tailWord_4796428 prefixEnd_4796428 2462872988683465187091635 := by
  unfold tailWord_4796428
  simp only [CollatzResearch.WordTrace]
  refine ⟨87470050533683997765238969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116626734044911997020318625 87470050533683997765238969)
  ·
    refine ⟨65602537900262998323929227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 87470050533683997765238969 65602537900262998323929227)
    ·
      refine ⟨98403806850394497485893841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65602537900262998323929227 98403806850394497485893841)
      ·
        refine ⟨73802855137795873114420381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 98403806850394497485893841 73802855137795873114420381)
        ·
          refine ⟨27676070676673452417907643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 73802855137795873114420381 27676070676673452417907643)
          ·
            refine ⟨41514106015010178626861465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27676070676673452417907643 41514106015010178626861465)
            ·
              refine ⟨31135579511257633970146099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 41514106015010178626861465 31135579511257633970146099)
              ·
                refine ⟨46703369266886450955219149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31135579511257633970146099 46703369266886450955219149)
                ·
                  refine ⟨17513763475082419108207181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 46703369266886450955219149 17513763475082419108207181)
                  ·
                    refine ⟨6567661303155907165577693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17513763475082419108207181 6567661303155907165577693)
                    ·
                      refine ⟨2462872988683465187091635, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6567661303155907165577693 2462872988683465187091635)
                      ·
                        rfl

theorem cell23_4796428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 2, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 2, 1, 3, 3, 3].length) (baseStart_4796428 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4796428 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4796428 prefixEnd_4796428 := by exact prefixLift 4796428
  have htrace : WordTrace (prefixWord ++ tailWord_4796428) baseStart_4796428 baseEnd_4796428 := by
    simpa [prefixWord, tailWord_4796428, baseEnd_4796428] using wordTrace_append hprefix tailTrace_4796428
  have hstable : (prefixWord ++ tailWord_4796428).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4796428).length < 2 ^ (prefixWord ++ tailWord_4796428).sum := by decide
  have hdescent : baseEnd_4796428 < baseStart_4796428 := by decide
  rcases family_descends (prefixWord ++ tailWord_4796428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4796441 : List Nat := [1, 2, 1, 2, 1, 1, 3, 1, 4, 2, 5]
def baseStart_4796441 : Nat := 118140960795 + 4796441 * 2 ^ 59
def prefixEnd_4796441 : Nat := 4983230072969 + 3 ^ 40 * 4796441 * 2
def baseEnd_4796441 : Nat := 2462879663931973636229075

theorem tailTrace_4796441 : CollatzResearch.WordTrace tailWord_4796441 prefixEnd_4796441 2462879663931973636229075 := by
  unfold tailWord_4796441
  simp only [CollatzResearch.WordTrace]
  refine ⟨174940575216320898750701177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116627050144213932500467451 174940575216320898750701177)
  ·
    refine ⟨131205431412240674063025883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 174940575216320898750701177 131205431412240674063025883)
    ·
      refine ⟨196808147118361011094538825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 131205431412240674063025883 196808147118361011094538825)
      ·
        refine ⟨147606110338770758320904119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 196808147118361011094538825 147606110338770758320904119)
        ·
          refine ⟨221409165508156137481356179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 147606110338770758320904119 221409165508156137481356179)
          ·
            refine ⟨332113748262234206222034269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 221409165508156137481356179 332113748262234206222034269)
            ·
              refine ⟨124542655598337827333262851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 332113748262234206222034269 124542655598337827333262851)
              ·
                refine ⟨186813983397506740999894277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 124542655598337827333262851 186813983397506740999894277)
                ·
                  refine ⟨35027621887032513937480177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 186813983397506740999894277 35027621887032513937480177)
                  ·
                    refine ⟨26270716415274385453110133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 35027621887032513937480177 26270716415274385453110133)
                    ·
                      refine ⟨2462879663931973636229075, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26270716415274385453110133 2462879663931973636229075)
                      ·
                        rfl

theorem cell23_4796441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 3, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 3, 1, 4, 2, 5].length) (baseStart_4796441 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4796441 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4796441 prefixEnd_4796441 := by exact prefixLift 4796441
  have htrace : WordTrace (prefixWord ++ tailWord_4796441) baseStart_4796441 baseEnd_4796441 := by
    simpa [prefixWord, tailWord_4796441, baseEnd_4796441] using wordTrace_append hprefix tailTrace_4796441
  have hstable : (prefixWord ++ tailWord_4796441).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4796441).length < 2 ^ (prefixWord ++ tailWord_4796441).sum := by decide
  have hdescent : baseEnd_4796441 < baseStart_4796441 := by decide
  rcases family_descends (prefixWord ++ tailWord_4796441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4796456 : List Nat := [2, 1, 5, 3, 1, 2, 2, 1, 2, 4]
def baseStart_4796456 : Nat := 118140960795 + 4796456 * 2 ^ 59
def prefixEnd_4796456 : Nat := 4983230072969 + 3 ^ 40 * 4796456 * 2
def baseEnd_4796456 : Nat := 820962455380597025847169

theorem tailTrace_4796456 : CollatzResearch.WordTrace tailWord_4796456 prefixEnd_4796456 820962455380597025847169 := by
  unfold tailWord_4796456
  simp only [CollatzResearch.WordTrace]
  refine ⟨87470561155633278156248611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116627414874177704208331481 87470561155633278156248611)
  ·
    refine ⟨131205841733449917234372917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87470561155633278156248611 131205841733449917234372917)
    ·
      refine ⟨12300547662510929740722461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 131205841733449917234372917 12300547662510929740722461)
      ·
        refine ⟨4612705373441598652770923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12300547662510929740722461 4612705373441598652770923)
        ·
          refine ⟨6919058060162397979156385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4612705373441598652770923 6919058060162397979156385)
          ·
            refine ⟨5189293545121798484367289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6919058060162397979156385 5189293545121798484367289)
            ·
              refine ⟨3891970158841348863275467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5189293545121798484367289 3891970158841348863275467)
              ·
                refine ⟨5837955238262023294913201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3891970158841348863275467 5837955238262023294913201)
                ·
                  refine ⟨4378466428696517471184901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5837955238262023294913201 4378466428696517471184901)
                  ·
                    refine ⟨820962455380597025847169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4378466428696517471184901 820962455380597025847169)
                    ·
                      rfl

theorem cell23_4796456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 1, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 1, 2, 2, 1, 2, 4].length) (baseStart_4796456 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4796456 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4796456 prefixEnd_4796456 := by exact prefixLift 4796456
  have htrace : WordTrace (prefixWord ++ tailWord_4796456) baseStart_4796456 baseEnd_4796456 := by
    simpa [prefixWord, tailWord_4796456, baseEnd_4796456] using wordTrace_append hprefix tailTrace_4796456
  have hstable : (prefixWord ++ tailWord_4796456).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4796456).length < 2 ^ (prefixWord ++ tailWord_4796456).sum := by decide
  have hdescent : baseEnd_4796456 < baseStart_4796456 := by decide
  rcases family_descends (prefixWord ++ tailWord_4796456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4796472 : List Nat := [2, 1, 2, 1, 6, 1, 1, 1, 3, 3, 2]
def baseStart_4796472 : Nat := 118140960795 + 4796472 * 2 ^ 59
def prefixEnd_4796472 : Nat := 4983230072969 + 3 ^ 40 * 4796472 * 2
def baseEnd_4796472 : Nat := 2462895581832263014941433

theorem tailTrace_4796472 : CollatzResearch.WordTrace tailWord_4796472 prefixEnd_4796472 2462895581832263014941433 := by
  unfold tailWord_4796472
  simp only [CollatzResearch.WordTrace]
  refine ⟨87470852939604295522539835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116627803919472394030053113 87470852939604295522539835)
  ·
    refine ⟨131206279409406443283809753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87470852939604295522539835 131206279409406443283809753)
    ·
      refine ⟨98404709557054832462857315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 131206279409406443283809753 98404709557054832462857315)
      ·
        refine ⟨147607064335582248694285973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 98404709557054832462857315 147607064335582248694285973)
        ·
          refine ⟨6919081140730417907544655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 147607064335582248694285973 6919081140730417907544655)
          ·
            refine ⟨10378621711095626861316983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6919081140730417907544655 10378621711095626861316983)
            ·
              refine ⟨15567932566643440291975475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10378621711095626861316983 15567932566643440291975475)
              ·
                refine ⟨23351898849965160437963213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15567932566643440291975475 23351898849965160437963213)
                ·
                  refine ⟨8756962068736935164236205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23351898849965160437963213 8756962068736935164236205)
                  ·
                    refine ⟨3283860775776350686588577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8756962068736935164236205 3283860775776350686588577)
                    ·
                      refine ⟨2462895581832263014941433, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3283860775776350686588577 2462895581832263014941433)
                      ·
                        rfl

theorem cell23_4796472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 6, 1, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 6, 1, 1, 1, 3, 3, 2].length) (baseStart_4796472 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4796472 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4796472 prefixEnd_4796472 := by exact prefixLift 4796472
  have htrace : WordTrace (prefixWord ++ tailWord_4796472) baseStart_4796472 baseEnd_4796472 := by
    simpa [prefixWord, tailWord_4796472, baseEnd_4796472] using wordTrace_append hprefix tailTrace_4796472
  have hstable : (prefixWord ++ tailWord_4796472).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4796472).length < 2 ^ (prefixWord ++ tailWord_4796472).sum := by decide
  have hdescent : baseEnd_4796472 < baseStart_4796472 := by decide
  rcases family_descends (prefixWord ++ tailWord_4796472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4796491 : List Nat := [1, 1, 1, 1, 3, 1, 2, 4, 9]
def baseStart_4796491 : Nat := 118140960795 + 4796491 * 2 ^ 59
def prefixEnd_4796491 : Nat := 4983230072969 + 3 ^ 40 * 4796491 * 2
def baseEnd_4796491 : Nat := 273656148662744271178205

theorem tailTrace_4796491 : CollatzResearch.WordTrace tailWord_4796491 prefixEnd_4796491 273656148662744271178205 := by
  unfold tailWord_4796491
  simp only [CollatzResearch.WordTrace]
  refine ⟨174942398866139757290021327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116628265910759838193347551 174942398866139757290021327)
  ·
    refine ⟨262413598299209635935031991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 174942398866139757290021327 262413598299209635935031991)
    ·
      refine ⟨393620397448814453902547987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 262413598299209635935031991 393620397448814453902547987)
      ·
        refine ⟨590430596173221680853821981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 393620397448814453902547987 590430596173221680853821981)
        ·
          refine ⟨221411473564958130320183243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 590430596173221680853821981 221411473564958130320183243)
          ·
            refine ⟨332117210347437195480274865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 221411473564958130320183243 332117210347437195480274865)
            ·
              refine ⟨249087907760577896610206149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 332117210347437195480274865 249087907760577896610206149)
              ·
                refine ⟨46703982705108355614413653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 249087907760577896610206149 46703982705108355614413653)
                ·
                  refine ⟨273656148662744271178205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 46703982705108355614413653 273656148662744271178205)
                  ·
                    rfl

theorem cell23_4796491_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 4, 9].length) (baseStart_4796491 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4796491 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4796491 prefixEnd_4796491 := by exact prefixLift 4796491
  have htrace : WordTrace (prefixWord ++ tailWord_4796491) baseStart_4796491 baseEnd_4796491 := by
    simpa [prefixWord, tailWord_4796491, baseEnd_4796491] using wordTrace_append hprefix tailTrace_4796491
  have hstable : (prefixWord ++ tailWord_4796491).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4796491).length < 2 ^ (prefixWord ++ tailWord_4796491).sum := by decide
  have hdescent : baseEnd_4796491 < baseStart_4796491 := by decide
  rcases family_descends (prefixWord ++ tailWord_4796491) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4796502 : List Nat := [5, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4]
def baseStart_4796502 : Nat := 118140960795 + 4796502 * 2 ^ 59
def prefixEnd_4796502 : Nat := 4983230072969 + 3 ^ 40 * 4796502 * 2
def baseEnd_4796502 : Nat := 2462910986251897897566295

theorem tailTrace_4796502 : CollatzResearch.WordTrace tailWord_4796502 prefixEnd_4796502 2462910986251897897566295 := by
  unfold tailWord_4796502
  simp only [CollatzResearch.WordTrace]
  refine ⟨10933925004318744135541985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 116628533379399937445781173 10933925004318744135541985)
  ·
    refine ⟨8200443753239058101656489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10933925004318744135541985 8200443753239058101656489)
    ·
      refine ⟨6150332814929293576242367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8200443753239058101656489 6150332814929293576242367)
      ·
        refine ⟨9225499222393940364363551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6150332814929293576242367 9225499222393940364363551)
        ·
          refine ⟨13838248833590910546545327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9225499222393940364363551 13838248833590910546545327)
          ·
            refine ⟨20757373250386365819817991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13838248833590910546545327 20757373250386365819817991)
            ·
              refine ⟨31136059875579548729726987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20757373250386365819817991 31136059875579548729726987)
              ·
                refine ⟨46704089813369323094590481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31136059875579548729726987 46704089813369323094590481)
                ·
                  refine ⟨35028067360026992320942861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 46704089813369323094590481 35028067360026992320942861)
                  ·
                    refine ⟨13135525260010122120353573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 35028067360026992320942861 13135525260010122120353573)
                    ·
                      refine ⟨2462910986251897897566295, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13135525260010122120353573 2462910986251897897566295)
                      ·
                        rfl

theorem cell23_4796502_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4].length) (baseStart_4796502 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4796502 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4796502 prefixEnd_4796502 := by exact prefixLift 4796502
  have htrace : WordTrace (prefixWord ++ tailWord_4796502) baseStart_4796502 baseEnd_4796502 := by
    simpa [prefixWord, tailWord_4796502, baseEnd_4796502] using wordTrace_append hprefix tailTrace_4796502
  have hstable : (prefixWord ++ tailWord_4796502).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4796502).length < 2 ^ (prefixWord ++ tailWord_4796502).sum := by decide
  have hdescent : baseEnd_4796502 < baseStart_4796502 := by decide
  rcases family_descends (prefixWord ++ tailWord_4796502) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4796575 : List Nat := [1, 1, 2, 6, 1, 1, 1, 2, 1, 3, 4]
def baseStart_4796575 : Nat := 118140960795 + 4796575 * 2 ^ 59
def prefixEnd_4796575 : Nat := 4983230072969 + 3 ^ 40 * 4796575 * 2
def baseEnd_4796575 : Nat := 2462948470339676111953459

theorem tailTrace_4796575 : CollatzResearch.WordTrace tailWord_4796575 prefixEnd_4796575 2462948470339676111953459 := by
  unfold tailWord_4796575
  simp only [CollatzResearch.WordTrace]
  refine ⟨174945462597835439636079179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116630308398556959757386119 174945462597835439636079179)
  ·
    refine ⟨262418193896753159454118769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 174945462597835439636079179 262418193896753159454118769)
    ·
      refine ⟨196813645422564869590589077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 262418193896753159454118769 196813645422564869590589077)
      ·
        refine ⟨9225639629182728262058863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 196813645422564869590589077 9225639629182728262058863)
        ·
          refine ⟨13838459443774092393088295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9225639629182728262058863 13838459443774092393088295)
          ·
            refine ⟨20757689165661138589632443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13838459443774092393088295 20757689165661138589632443)
            ·
              refine ⟨31136533748491707884448665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20757689165661138589632443 31136533748491707884448665)
              ·
                refine ⟨23352400311368780913336499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31136533748491707884448665 23352400311368780913336499)
                ·
                  refine ⟨35028600467053171370004749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23352400311368780913336499 35028600467053171370004749)
                  ·
                    refine ⟨13135725175144939263751781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 35028600467053171370004749 13135725175144939263751781)
                    ·
                      refine ⟨2462948470339676111953459, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13135725175144939263751781 2462948470339676111953459)
                      ·
                        rfl

theorem cell23_4796575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 1, 2, 1, 3, 4].length) (baseStart_4796575 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4796575 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4796575 prefixEnd_4796575 := by exact prefixLift 4796575
  have htrace : WordTrace (prefixWord ++ tailWord_4796575) baseStart_4796575 baseEnd_4796575 := by
    simpa [prefixWord, tailWord_4796575, baseEnd_4796575] using wordTrace_append hprefix tailTrace_4796575
  have hstable : (prefixWord ++ tailWord_4796575).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4796575).length < 2 ^ (prefixWord ++ tailWord_4796575).sum := by decide
  have hdescent : baseEnd_4796575 < baseStart_4796575 := by decide
  rcases family_descends (prefixWord ++ tailWord_4796575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4796595 : List Nat := [1, 1, 1, 2, 3, 2, 1, 5, 2, 2, 3]
def baseStart_4796595 : Nat := 118140960795 + 4796595 * 2 ^ 59
def prefixEnd_4796595 : Nat := 4983230072969 + 3 ^ 40 * 4796595 * 2
def baseEnd_4796595 : Nat := 2462958739952766033703367

theorem tailTrace_4796595 : CollatzResearch.WordTrace tailWord_4796595 prefixEnd_4796595 2462958739952766033703367 := by
  unfold tailWord_4796595
  simp only [CollatzResearch.WordTrace]
  refine ⟨174946192057762983051807239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116630794705175322034538159 174946192057762983051807239)
  ·
    refine ⟨262419288086644474577710859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 174946192057762983051807239 262419288086644474577710859)
    ·
      refine ⟨393628932129966711866566289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 262419288086644474577710859 393628932129966711866566289)
      ·
        refine ⟨295221699097475033899924717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 393628932129966711866566289 295221699097475033899924717)
        ·
          refine ⟨110708137161553137712471769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 295221699097475033899924717 110708137161553137712471769)
          ·
            refine ⟨83031102871164853284353827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 110708137161553137712471769 83031102871164853284353827)
            ·
              refine ⟨124546654306747279926530741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 83031102871164853284353827 124546654306747279926530741)
              ·
                refine ⟨11676248841257557493112257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 124546654306747279926530741 11676248841257557493112257)
                ·
                  refine ⟨8757186630943168119834193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11676248841257557493112257 8757186630943168119834193)
                  ·
                    refine ⟨6567889973207376089875645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8757186630943168119834193 6567889973207376089875645)
                    ·
                      refine ⟨2462958739952766033703367, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6567889973207376089875645 2462958739952766033703367)
                      ·
                        rfl

theorem cell23_4796595_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 1, 5, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 1, 5, 2, 2, 3].length) (baseStart_4796595 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4796595 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4796595 prefixEnd_4796595 := by exact prefixLift 4796595
  have htrace : WordTrace (prefixWord ++ tailWord_4796595) baseStart_4796595 baseEnd_4796595 := by
    simpa [prefixWord, tailWord_4796595, baseEnd_4796595] using wordTrace_append hprefix tailTrace_4796595
  have hstable : (prefixWord ++ tailWord_4796595).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4796595).length < 2 ^ (prefixWord ++ tailWord_4796595).sum := by decide
  have hdescent : baseEnd_4796595 < baseStart_4796595 := by decide
  rcases family_descends (prefixWord ++ tailWord_4796595) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4796609 : List Nat := [1, 2, 6, 1, 2, 1, 1, 2, 2, 1, 4]
def baseStart_4796609 : Nat := 118140960795 + 4796609 * 2 ^ 59
def prefixEnd_4796609 : Nat := 4983230072969 + 3 ^ 40 * 4796609 * 2
def baseEnd_4796609 : Nat := 2462965928681928978928303

theorem tailTrace_4796609 : CollatzResearch.WordTrace tailWord_4796609 prefixEnd_4796609 2462965928681928978928303 := by
  unfold tailWord_4796609
  simp only [CollatzResearch.WordTrace]
  refine ⟨174946702679712263442816881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116631135119808175628544587 174946702679712263442816881)
  ·
    refine ⟨131210027009784197582112661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 174946702679712263442816881 131210027009784197582112661)
    ·
      refine ⟨6150470016083634261661531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 131210027009784197582112661 6150470016083634261661531)
      ·
        refine ⟨9225705024125451392492297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6150470016083634261661531 9225705024125451392492297)
        ·
          refine ⟨6919278768094088544369223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9225705024125451392492297 6919278768094088544369223)
          ·
            refine ⟨10378918152141132816553835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6919278768094088544369223 10378918152141132816553835)
            ·
              refine ⟨15568377228211699224830753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10378918152141132816553835 15568377228211699224830753)
              ·
                refine ⟨11676282921158774418623065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15568377228211699224830753 11676282921158774418623065)
                ·
                  refine ⟨8757212190869080813967299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11676282921158774418623065 8757212190869080813967299)
                  ·
                    refine ⟨13135818286303621220950949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8757212190869080813967299 13135818286303621220950949)
                    ·
                      refine ⟨2462965928681928978928303, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13135818286303621220950949 2462965928681928978928303)
                      ·
                        rfl

theorem cell23_4796609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 2, 1, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 2, 1, 1, 2, 2, 1, 4].length) (baseStart_4796609 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4796609 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4796609 prefixEnd_4796609 := by exact prefixLift 4796609
  have htrace : WordTrace (prefixWord ++ tailWord_4796609) baseStart_4796609 baseEnd_4796609 := by
    simpa [prefixWord, tailWord_4796609, baseEnd_4796609] using wordTrace_append hprefix tailTrace_4796609
  have hstable : (prefixWord ++ tailWord_4796609).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4796609).length < 2 ^ (prefixWord ++ tailWord_4796609).sum := by decide
  have hdescent : baseEnd_4796609 < baseStart_4796609 := by decide
  rcases family_descends (prefixWord ++ tailWord_4796609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4796612 : List Nat := [2, 3, 3, 1, 2, 1, 1, 1, 4, 2, 3]
def baseStart_4796612 : Nat := 118140960795 + 4796612 * 2 ^ 59
def prefixEnd_4796612 : Nat := 4983230072969 + 3 ^ 40 * 4796612 * 2
def baseEnd_4796612 : Nat := 2462967469123892467190789

theorem tailTrace_4796612 : CollatzResearch.WordTrace tailWord_4796612 prefixEnd_4796612 2462967469123892467190789 := by
  unfold tailWord_4796612
  simp only [CollatzResearch.WordTrace]
  refine ⟨87473406049350697477588045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116631208065800929970117393 87473406049350697477588045)
  ·
    refine ⟨32802527268506511554095517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 87473406049350697477588045 32802527268506511554095517)
    ·
      refine ⟨12300947725689941832785819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32802527268506511554095517 12300947725689941832785819)
      ·
        refine ⟨18451421588534912749178729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12300947725689941832785819 18451421588534912749178729)
        ·
          refine ⟨13838566191401184561884047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18451421588534912749178729 13838566191401184561884047)
          ·
            refine ⟨20757849287101776842826071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13838566191401184561884047 20757849287101776842826071)
            ·
              refine ⟨31136773930652665264239107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20757849287101776842826071 31136773930652665264239107)
              ·
                refine ⟨46705160895978997896358661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31136773930652665264239107 46705160895978997896358661)
                ·
                  refine ⟨8757217667996062105567249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 46705160895978997896358661 8757217667996062105567249)
                  ·
                    refine ⟨6567913250997046579175437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8757217667996062105567249 6567913250997046579175437)
                    ·
                      refine ⟨2462967469123892467190789, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6567913250997046579175437 2462967469123892467190789)
                      ·
                        rfl

theorem cell23_4796612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 1, 1, 4, 2, 3].length) (baseStart_4796612 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4796612 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4796612 prefixEnd_4796612 := by exact prefixLift 4796612
  have htrace : WordTrace (prefixWord ++ tailWord_4796612) baseStart_4796612 baseEnd_4796612 := by
    simpa [prefixWord, tailWord_4796612, baseEnd_4796612] using wordTrace_append hprefix tailTrace_4796612
  have hstable : (prefixWord ++ tailWord_4796612).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4796612).length < 2 ^ (prefixWord ++ tailWord_4796612).sum := by decide
  have hdescent : baseEnd_4796612 < baseStart_4796612 := by decide
  rcases family_descends (prefixWord ++ tailWord_4796612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4796619 : List Nat := [1, 1, 1, 1, 3, 2, 7, 2, 1, 4]
def baseStart_4796619 : Nat := 118140960795 + 4796619 * 2 ^ 59
def prefixEnd_4796619 : Nat := 4983230072969 + 3 ^ 40 * 4796619 * 2
def baseEnd_4796619 : Nat := 820990354496157979934419

theorem tailTrace_4796619 : CollatzResearch.WordTrace tailWord_4796619 prefixEnd_4796619 820990354496157979934419 := by
  unfold tailWord_4796619
  simp only [CollatzResearch.WordTrace]
  refine ⟨174947067409676035150680911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116631378273117356767120607 174947067409676035150680911)
  ·
    refine ⟨262420601114514052726021367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 174947067409676035150680911 262420601114514052726021367)
    ·
      refine ⟨393630901671771079089032051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 262420601114514052726021367 393630901671771079089032051)
      ·
        refine ⟨590446352507656618633548077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 393630901671771079089032051 590446352507656618633548077)
        ·
          refine ⟨221417382190371231987580529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 590446352507656618633548077 221417382190371231987580529)
          ·
            refine ⟨166063036642778423990685397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 221417382190371231987580529 166063036642778423990685397)
            ·
              refine ⟨3892102421315119312281689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 166063036642778423990685397 3892102421315119312281689)
              ·
                refine ⟨2919076815986339484211267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3892102421315119312281689 2919076815986339484211267)
                ·
                  refine ⟨4378615223979509226316901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2919076815986339484211267 4378615223979509226316901)
                  ·
                    refine ⟨820990354496157979934419, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4378615223979509226316901 820990354496157979934419)
                    ·
                      rfl

theorem cell23_4796619_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 7, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 7, 2, 1, 4].length) (baseStart_4796619 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4796619 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4796619 prefixEnd_4796619 := by exact prefixLift 4796619
  have htrace : WordTrace (prefixWord ++ tailWord_4796619) baseStart_4796619 baseEnd_4796619 := by
    simpa [prefixWord, tailWord_4796619, baseEnd_4796619] using wordTrace_append hprefix tailTrace_4796619
  have hstable : (prefixWord ++ tailWord_4796619).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4796619).length < 2 ^ (prefixWord ++ tailWord_4796619).sum := by decide
  have hdescent : baseEnd_4796619 < baseStart_4796619 := by decide
  rcases family_descends (prefixWord ++ tailWord_4796619) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4796632 : List Nat := [2, 1, 2, 2, 4, 1, 4, 1, 6]
def baseStart_4796632 : Nat := 118140960795 + 4796632 * 2 ^ 59
def prefixEnd_4796632 : Nat := 4983230072969 + 3 ^ 40 * 4796632 * 2
def baseEnd_4796632 : Nat := 273664193192998043215633

theorem tailTrace_4796632 : CollatzResearch.WordTrace tailWord_4796632 prefixEnd_4796632 273664193192998043215633 := by
  unfold tailWord_4796632
  simp only [CollatzResearch.WordTrace]
  refine ⟨87473770779314469185452075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116631694372419292247269433 87473770779314469185452075)
  ·
    refine ⟨131210656168971703778178113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87473770779314469185452075 131210656168971703778178113)
    ·
      refine ⟨98407992126728777833633585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 131210656168971703778178113 98407992126728777833633585)
      ·
        refine ⟨73805994095046583375225189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 98407992126728777833633585 73805994095046583375225189)
        ·
          refine ⟨13838623892821234382854723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 73805994095046583375225189 13838623892821234382854723)
          ·
            refine ⟨20757935839231851574282085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13838623892821234382854723 20757935839231851574282085)
            ·
              refine ⟨3892112969855972170177891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 20757935839231851574282085 3892112969855972170177891)
              ·
                refine ⟨5838169454783958255266837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3892112969855972170177891 5838169454783958255266837)
                ·
                  refine ⟨273664193192998043215633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5838169454783958255266837 273664193192998043215633)
                  ·
                    rfl

theorem cell23_4796632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 4, 1, 6].length) (baseStart_4796632 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4796632 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4796632 prefixEnd_4796632 := by exact prefixLift 4796632
  have htrace : WordTrace (prefixWord ++ tailWord_4796632) baseStart_4796632 baseEnd_4796632 := by
    simpa [prefixWord, tailWord_4796632, baseEnd_4796632] using wordTrace_append hprefix tailTrace_4796632
  have hstable : (prefixWord ++ tailWord_4796632).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4796632).length < 2 ^ (prefixWord ++ tailWord_4796632).sum := by decide
  have hdescent : baseEnd_4796632 < baseStart_4796632 := by decide
  rcases family_descends (prefixWord ++ tailWord_4796632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4796659 : List Nat := [1, 1, 1, 2, 2, 4, 2, 5, 1, 1, 3]
def baseStart_4796659 : Nat := 118140960795 + 4796659 * 2 ^ 59
def prefixEnd_4796659 : Nat := 4983230072969 + 3 ^ 40 * 4796659 * 2
def baseEnd_4796659 : Nat := 2462991602714653783303073

theorem tailTrace_4796659 : CollatzResearch.WordTrace tailWord_4796659 prefixEnd_4796659 2462991602714653783303073 := by
  unfold tailWord_4796659
  simp only [CollatzResearch.WordTrace]
  refine ⟨174948526329531121982137031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116632350886354081321424687 174948526329531121982137031)
  ·
    refine ⟨262422789494296682973205547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 174948526329531121982137031 262422789494296682973205547)
    ·
      refine ⟨393634184241445024459808321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 262422789494296682973205547 393634184241445024459808321)
      ·
        refine ⟨295225638181083768344856241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 393634184241445024459808321 295225638181083768344856241)
        ·
          refine ⟨221419228635812826258642181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 295225638181083768344856241 221419228635812826258642181)
          ·
            refine ⟨41516105369214904923495409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 221419228635812826258642181 41516105369214904923495409)
            ·
              refine ⟨31137079026911178692621557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 41516105369214904923495409 31137079026911178692621557)
              ·
                refine ⟨2919101158772923002433271, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 31137079026911178692621557 2919101158772923002433271)
                ·
                  refine ⟨4378651738159384503649907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2919101158772923002433271 4378651738159384503649907)
                  ·
                    refine ⟨6567977607239076755474861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4378651738159384503649907 6567977607239076755474861)
                    ·
                      refine ⟨2462991602714653783303073, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6567977607239076755474861 2462991602714653783303073)
                      ·
                        rfl

theorem cell23_4796659_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 2, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 2, 5, 1, 1, 3].length) (baseStart_4796659 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4796659 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4796659 prefixEnd_4796659 := by exact prefixLift 4796659
  have htrace : WordTrace (prefixWord ++ tailWord_4796659) baseStart_4796659 baseEnd_4796659 := by
    simpa [prefixWord, tailWord_4796659, baseEnd_4796659] using wordTrace_append hprefix tailTrace_4796659
  have hstable : (prefixWord ++ tailWord_4796659).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4796659).length < 2 ^ (prefixWord ++ tailWord_4796659).sum := by decide
  have hdescent : baseEnd_4796659 < baseStart_4796659 := by decide
  rcases family_descends (prefixWord ++ tailWord_4796659) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4796662 : List Nat := [5, 1, 1, 1, 1, 1, 2, 5, 1, 5]
def baseStart_4796662 : Nat := 118140960795 + 4796662 * 2 ^ 59
def prefixEnd_4796662 : Nat := 4983230072969 + 3 ^ 40 * 4796662 * 2
def baseEnd_4796662 : Nat := 820997714385539090521853

theorem tailTrace_4796662 : CollatzResearch.WordTrace tailWord_4796662 prefixEnd_4796662 820997714385539090521853 := by
  unfold tailWord_4796662
  simp only [CollatzResearch.WordTrace]
  refine ⟨10934289734282515843406015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 116632423832346835662997493 10934289734282515843406015)
  ·
    refine ⟨16401434601423773765109023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10934289734282515843406015 16401434601423773765109023)
    ·
      refine ⟨24602151902135660647663535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16401434601423773765109023 24602151902135660647663535)
      ·
        refine ⟨36903227853203490971495303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24602151902135660647663535 36903227853203490971495303)
        ·
          refine ⟨55354841779805236457242955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36903227853203490971495303 55354841779805236457242955)
          ·
            refine ⟨83032262669707854685864433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55354841779805236457242955 83032262669707854685864433)
            ·
              refine ⟨62274197002280891014398325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 83032262669707854685864433 62274197002280891014398325)
              ·
                refine ⟨5838205968963833532599843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 62274197002280891014398325 5838205968963833532599843)
                ·
                  refine ⟨8757308953445750298899765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5838205968963833532599843 8757308953445750298899765)
                  ·
                    refine ⟨820997714385539090521853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8757308953445750298899765 820997714385539090521853)
                    ·
                      rfl

theorem cell23_4796662_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 2, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 2, 5, 1, 5].length) (baseStart_4796662 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4796662 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4796662 prefixEnd_4796662 := by exact prefixLift 4796662
  have htrace : WordTrace (prefixWord ++ tailWord_4796662) baseStart_4796662 baseEnd_4796662 := by
    simpa [prefixWord, tailWord_4796662, baseEnd_4796662] using wordTrace_append hprefix tailTrace_4796662
  have hstable : (prefixWord ++ tailWord_4796662).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4796662).length < 2 ^ (prefixWord ++ tailWord_4796662).sum := by decide
  have hdescent : baseEnd_4796662 < baseStart_4796662 := by decide
  rcases family_descends (prefixWord ++ tailWord_4796662) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4796716 : List Nat := [2, 2, 1, 1, 1, 3, 3, 5, 1, 2, 2]
def baseStart_4796716 : Nat := 118140960795 + 4796716 * 2 ^ 59
def prefixEnd_4796716 : Nat := 4983230072969 + 3 ^ 40 * 4796716 * 2
def baseEnd_4796716 : Nat := 2463020871111960060290311

theorem tailTrace_4796716 : CollatzResearch.WordTrace tailWord_4796716 prefixEnd_4796716 2463020871111960060290311 := by
  unfold tailWord_4796716
  simp only [CollatzResearch.WordTrace]
  refine ⟨87475302645162310358481001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116633736860216413811308001 87475302645162310358481001)
  ·
    refine ⟨65606476983871732768860751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 87475302645162310358481001 65606476983871732768860751)
    ·
      refine ⟨98409715475807599153291127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65606476983871732768860751 98409715475807599153291127)
      ·
        refine ⟨147614573213711398729936691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 98409715475807599153291127 147614573213711398729936691)
        ·
          refine ⟨221421859820567098094905037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 147614573213711398729936691 221421859820567098094905037)
          ·
            refine ⟨83033197432712661785589389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 221421859820567098094905037 83033197432712661785589389)
            ·
              refine ⟨31137449037267248169596021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 83033197432712661785589389 31137449037267248169596021)
              ·
                refine ⟨2919135847243804515899627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 31137449037267248169596021 2919135847243804515899627)
                ·
                  refine ⟨4378703770865706773849441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2919135847243804515899627 4378703770865706773849441)
                  ·
                    refine ⟨3284027828149280080387081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4378703770865706773849441 3284027828149280080387081)
                    ·
                      refine ⟨2463020871111960060290311, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3284027828149280080387081 2463020871111960060290311)
                      ·
                        rfl

theorem cell23_4796716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 3, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 3, 5, 1, 2, 2].length) (baseStart_4796716 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4796716 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4796716 prefixEnd_4796716 := by exact prefixLift 4796716
  have htrace : WordTrace (prefixWord ++ tailWord_4796716) baseStart_4796716 baseEnd_4796716 := by
    simpa [prefixWord, tailWord_4796716, baseEnd_4796716] using wordTrace_append hprefix tailTrace_4796716
  have hstable : (prefixWord ++ tailWord_4796716).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4796716).length < 2 ^ (prefixWord ++ tailWord_4796716).sum := by decide
  have hdescent : baseEnd_4796716 < baseStart_4796716 := by decide
  rcases family_descends (prefixWord ++ tailWord_4796716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4796719 : List Nat := [1, 1, 2, 1, 2, 1, 8, 1, 1, 2, 3]
def baseStart_4796719 : Nat := 118140960795 + 4796719 * 2 ^ 59
def prefixEnd_4796719 : Nat := 4983230072969 + 3 ^ 40 * 4796719 * 2
def baseEnd_4796719 : Nat := 2463022411553923548552797

theorem tailTrace_4796719 : CollatzResearch.WordTrace tailWord_4796719 prefixEnd_4796719 2463022411553923548552797 := by
  unfold tailWord_4796719
  simp only [CollatzResearch.WordTrace]
  refine ⟨174950714709313752229321211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116633809806209168152880807 174950714709313752229321211)
  ·
    refine ⟨262426072063970628343981817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 174950714709313752229321211 262426072063970628343981817)
    ·
      refine ⟨196819554047977971257986363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 262426072063970628343981817 196819554047977971257986363)
      ·
        refine ⟨295229331071966956886979545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 196819554047977971257986363 295229331071966956886979545)
        ·
          refine ⟨221421998303975217665234659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 295229331071966956886979545 221421998303975217665234659)
          ·
            refine ⟨332132997455962826497851989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 221421998303975217665234659 332132997455962826497851989)
            ·
              refine ⟨3892183563937064373021703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 332132997455962826497851989 3892183563937064373021703)
              ·
                refine ⟨5838275345905596559532555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3892183563937064373021703 5838275345905596559532555)
                ·
                  refine ⟨8757413018858394839298833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5838275345905596559532555 8757413018858394839298833)
                  ·
                    refine ⟨6568059764143796129474125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8757413018858394839298833 6568059764143796129474125)
                    ·
                      refine ⟨2463022411553923548552797, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6568059764143796129474125 2463022411553923548552797)
                      ·
                        rfl

theorem cell23_4796719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 8, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 8, 1, 1, 2, 3].length) (baseStart_4796719 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4796719 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4796719 prefixEnd_4796719 := by exact prefixLift 4796719
  have htrace : WordTrace (prefixWord ++ tailWord_4796719) baseStart_4796719 baseEnd_4796719 := by
    simpa [prefixWord, tailWord_4796719, baseEnd_4796719] using wordTrace_append hprefix tailTrace_4796719
  have hstable : (prefixWord ++ tailWord_4796719).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4796719).length < 2 ^ (prefixWord ++ tailWord_4796719).sum := by decide
  have hdescent : baseEnd_4796719 < baseStart_4796719 := by decide
  rcases family_descends (prefixWord ++ tailWord_4796719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4796776 : List Nat := [2, 1, 4, 2, 2, 1, 2, 3, 1, 3, 2]
def baseStart_4796776 : Nat := 118140960795 + 4796776 * 2 ^ 59
def prefixEnd_4796776 : Nat := 4983230072969 + 3 ^ 40 * 4796776 * 2
def baseEnd_4796776 : Nat := 2463051679951229825540035

theorem tailTrace_4796776 : CollatzResearch.WordTrace tailWord_4796776 prefixEnd_4796776 2463051679951229825540035 := by
  unfold tailWord_4796776
  simp only [CollatzResearch.WordTrace]
  refine ⟨87476396835053625482073091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116635195780071500642764121 87476396835053625482073091)
  ·
    refine ⟨131214595252580438223109637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87476396835053625482073091 131214595252580438223109637)
    ·
      refine ⟨24602736609858832166833057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 131214595252580438223109637 24602736609858832166833057)
      ·
        refine ⟨18452052457394124125124793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24602736609858832166833057 18452052457394124125124793)
        ·
          refine ⟨13839039343045593093843595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18452052457394124125124793 13839039343045593093843595)
          ·
            refine ⟨20758559014568389640765393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13839039343045593093843595 20758559014568389640765393)
            ·
              refine ⟨15568919260926292230574045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20758559014568389640765393 15568919260926292230574045)
              ·
                refine ⟨5838344722847359586465267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15568919260926292230574045 5838344722847359586465267)
                ·
                  refine ⟨8757517084271039379697901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5838344722847359586465267 8757517084271039379697901)
                  ·
                    refine ⟨3284068906601639767386713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8757517084271039379697901 3284068906601639767386713)
                    ·
                      refine ⟨2463051679951229825540035, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3284068906601639767386713 2463051679951229825540035)
                      ·
                        rfl

theorem cell23_4796776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 2, 3, 1, 3, 2].length) (baseStart_4796776 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4796776 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4796776 prefixEnd_4796776 := by exact prefixLift 4796776
  have htrace : WordTrace (prefixWord ++ tailWord_4796776) baseStart_4796776 baseEnd_4796776 := by
    simpa [prefixWord, tailWord_4796776, baseEnd_4796776] using wordTrace_append hprefix tailTrace_4796776
  have hstable : (prefixWord ++ tailWord_4796776).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4796776).length < 2 ^ (prefixWord ++ tailWord_4796776).sum := by decide
  have hdescent : baseEnd_4796776 < baseStart_4796776 := by decide
  rcases family_descends (prefixWord ++ tailWord_4796776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4796810 : List Nat := [3, 1, 2, 5, 1, 2, 1, 2, 1, 3, 2]
def baseStart_4796810 : Nat := 118140960795 + 4796810 * 2 ^ 59
def prefixEnd_4796810 : Nat := 4983230072969 + 3 ^ 40 * 4796810 * 2
def baseEnd_4796810 : Nat := 2463069138293482692514879

theorem tailTrace_4796810 : CollatzResearch.WordTrace tailWord_4796810 prefixEnd_4796810 2463069138293482692514879 := by
  unfold tailWord_4796810
  simp only [CollatzResearch.WordTrace]
  refine ⟨43738508437996018692720971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 116636022501322716513922589 43738508437996018692720971)
  ·
    refine ⟨65607762656994028039081457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43738508437996018692720971 65607762656994028039081457)
    ·
      refine ⟨49205821992745521029311093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 65607762656994028039081457 49205821992745521029311093)
      ·
        refine ⟨4613045811819892596497915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 49205821992745521029311093 4613045811819892596497915)
        ·
          refine ⟨6919568717729838894746873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4613045811819892596497915 6919568717729838894746873)
          ·
            refine ⟨5189676538297379171060155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6919568717729838894746873 5189676538297379171060155)
            ·
              refine ⟨7784514807446068756590233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5189676538297379171060155 7784514807446068756590233)
              ·
                refine ⟨5838386105584551567442675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7784514807446068756590233 5838386105584551567442675)
                ·
                  refine ⟨8757579158376827351164013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5838386105584551567442675 8757579158376827351164013)
                  ·
                    refine ⟨3284092184391310256686505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8757579158376827351164013 3284092184391310256686505)
                    ·
                      refine ⟨2463069138293482692514879, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3284092184391310256686505 2463069138293482692514879)
                      ·
                        rfl

theorem cell23_4796810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 1, 2, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 1, 2, 1, 2, 1, 3, 2].length) (baseStart_4796810 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4796810 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4796810 prefixEnd_4796810 := by exact prefixLift 4796810
  have htrace : WordTrace (prefixWord ++ tailWord_4796810) baseStart_4796810 baseEnd_4796810 := by
    simpa [prefixWord, tailWord_4796810, baseEnd_4796810] using wordTrace_append hprefix tailTrace_4796810
  have hstable : (prefixWord ++ tailWord_4796810).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4796810).length < 2 ^ (prefixWord ++ tailWord_4796810).sum := by decide
  have hdescent : baseEnd_4796810 < baseStart_4796810 := by decide
  rcases family_descends (prefixWord ++ tailWord_4796810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4796840 : List Nat := [2, 1, 6, 1, 1, 2, 2, 2, 2, 2, 2]
def baseStart_4796840 : Nat := 118140960795 + 4796840 * 2 ^ 59
def prefixEnd_4796840 : Nat := 4983230072969 + 3 ^ 40 * 4796840 * 2
def baseEnd_4796840 : Nat := 2463084542713117575139741

theorem tailTrace_4796840 : CollatzResearch.WordTrace tailWord_4796840 prefixEnd_4796840 2463084542713117575139741 := by
  unfold tailWord_4796840
  simp only [CollatzResearch.WordTrace]
  refine ⟨87477563970937694947237987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116636751961250259929650649 87477563970937694947237987)
  ·
    refine ⟨131216345956406542420856981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87477563970937694947237987 131216345956406542420856981)
    ·
      refine ⟨6150766216706556675977671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 131216345956406542420856981 6150766216706556675977671)
      ·
        refine ⟨9226149325059835013966507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6150766216706556675977671 9226149325059835013966507)
        ·
          refine ⟨13839223987589752520949761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9226149325059835013966507 13839223987589752520949761)
          ·
            refine ⟨10379417990692314390712321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13839223987589752520949761 10379417990692314390712321)
            ·
              refine ⟨7784563493019235793034241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10379417990692314390712321 7784563493019235793034241)
              ·
                refine ⟨5838422619764426844775681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7784563493019235793034241 5838422619764426844775681)
                ·
                  refine ⟨4378816964823320133581761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5838422619764426844775681 4378816964823320133581761)
                  ·
                    refine ⟨3284112723617490100186321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4378816964823320133581761 3284112723617490100186321)
                    ·
                      refine ⟨2463084542713117575139741, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3284112723617490100186321 2463084542713117575139741)
                      ·
                        rfl

theorem cell23_4796840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 2, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 2, 2, 2, 2, 2, 2].length) (baseStart_4796840 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4796840 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4796840 prefixEnd_4796840 := by exact prefixLift 4796840
  have htrace : WordTrace (prefixWord ++ tailWord_4796840) baseStart_4796840 baseEnd_4796840 := by
    simpa [prefixWord, tailWord_4796840, baseEnd_4796840] using wordTrace_append hprefix tailTrace_4796840
  have hstable : (prefixWord ++ tailWord_4796840).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4796840).length < 2 ^ (prefixWord ++ tailWord_4796840).sum := by decide
  have hdescent : baseEnd_4796840 < baseStart_4796840 := by decide
  rcases family_descends (prefixWord ++ tailWord_4796840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4796849 : List Nat := [1, 2, 2, 4, 1, 2, 1, 1, 2, 5, 2]
def baseStart_4796849 : Nat := 118140960795 + 4796849 * 2 ^ 59
def prefixEnd_4796849 : Nat := 4983230072969 + 3 ^ 40 * 4796849 * 2
def baseEnd_4796849 : Nat := 2463089164039008039927199

theorem tailTrace_4796849 : CollatzResearch.WordTrace tailWord_4796849 prefixEnd_4796849 2463089164039008039927199 := by
  unfold tailWord_4796849
  simp only [CollatzResearch.WordTrace]
  refine ⟨174955456198842784431553601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116636970799228522954369067 174955456198842784431553601)
  ·
    refine ⟨131216592149132088323665201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 174955456198842784431553601 131216592149132088323665201)
    ·
      refine ⟨98412444111849066242748901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 131216592149132088323665201 98412444111849066242748901)
      ·
        refine ⟨18452333270971699920515419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 98412444111849066242748901 18452333270971699920515419)
        ·
          refine ⟨27678499906457549880773129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18452333270971699920515419 27678499906457549880773129)
          ·
            refine ⟨20758874929843162410579847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27678499906457549880773129 20758874929843162410579847)
            ·
              refine ⟨31138312394764743615869771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20758874929843162410579847 31138312394764743615869771)
              ·
                refine ⟨46707468592147115423804657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31138312394764743615869771 46707468592147115423804657)
                ·
                  refine ⟨35030601444110336567853493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 46707468592147115423804657 35030601444110336567853493)
                  ·
                    refine ⟨3284118885385344053236265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 35030601444110336567853493 3284118885385344053236265)
                    ·
                      refine ⟨2463089164039008039927199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3284118885385344053236265 2463089164039008039927199)
                      ·
                        rfl

theorem cell23_4796849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 1, 1, 2, 5, 2].length) (baseStart_4796849 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4796849 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4796849 prefixEnd_4796849 := by exact prefixLift 4796849
  have htrace : WordTrace (prefixWord ++ tailWord_4796849) baseStart_4796849 baseEnd_4796849 := by
    simpa [prefixWord, tailWord_4796849, baseEnd_4796849] using wordTrace_append hprefix tailTrace_4796849
  have hstable : (prefixWord ++ tailWord_4796849).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4796849).length < 2 ^ (prefixWord ++ tailWord_4796849).sum := by decide
  have hdescent : baseEnd_4796849 < baseStart_4796849 := by decide
  rcases family_descends (prefixWord ++ tailWord_4796849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4796876 : List Nat := [2, 2, 1, 4, 3, 2, 1, 1, 2, 5]
def baseStart_4796876 : Nat := 118140960795 + 4796876 * 2 ^ 59
def prefixEnd_4796876 : Nat := 4983230072969 + 3 ^ 40 * 4796876 * 2
def baseEnd_4796876 : Nat := 821034342672226478096525

theorem tailTrace_4796876 : CollatzResearch.WordTrace tailWord_4796876 prefixEnd_4796876 821034342672226478096525 := by
  unfold tailWord_4796876
  simp only [CollatzResearch.WordTrace]
  refine ⟨87478220484872484021393241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116637627313163312028524321 87478220484872484021393241)
  ·
    refine ⟨65608665363654363016044931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 87478220484872484021393241 65608665363654363016044931)
    ·
      refine ⟨98412998045481544524067397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65608665363654363016044931 98412998045481544524067397)
      ·
        refine ⟨18452437133527789598262637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 98412998045481544524067397 18452437133527789598262637)
        ·
          refine ⟨6919663925072921099348489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18452437133527789598262637 6919663925072921099348489)
          ·
            refine ⟨5189747943804690824511367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6919663925072921099348489 5189747943804690824511367)
            ·
              refine ⟨7784621915707036236767051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5189747943804690824511367 7784621915707036236767051)
              ·
                refine ⟨11676932873560554355150577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7784621915707036236767051 11676932873560554355150577)
                ·
                  refine ⟨8757699655170415766362933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11676932873560554355150577 8757699655170415766362933)
                  ·
                    refine ⟨821034342672226478096525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8757699655170415766362933 821034342672226478096525)
                    ·
                      rfl

theorem cell23_4796876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 3, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 3, 2, 1, 1, 2, 5].length) (baseStart_4796876 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4796876 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4796876 prefixEnd_4796876 := by exact prefixLift 4796876
  have htrace : WordTrace (prefixWord ++ tailWord_4796876) baseStart_4796876 baseEnd_4796876 := by
    simpa [prefixWord, tailWord_4796876, baseEnd_4796876] using wordTrace_append hprefix tailTrace_4796876
  have hstable : (prefixWord ++ tailWord_4796876).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4796876).length < 2 ^ (prefixWord ++ tailWord_4796876).sum := by decide
  have hdescent : baseEnd_4796876 < baseStart_4796876 := by decide
  rcases family_descends (prefixWord ++ tailWord_4796876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4796906 : List Nat := [3, 1, 3, 1, 3, 2, 2, 1, 3, 4]
def baseStart_4796906 : Nat := 118140960795 + 4796906 * 2 ^ 59
def prefixEnd_4796906 : Nat := 4983230072969 + 3 ^ 40 * 4796906 * 2
def baseEnd_4796906 : Nat := 821039477478771438971479

theorem tailTrace_4796906 : CollatzResearch.WordTrace tailWord_4796906 prefixEnd_4796906 821039477478771438971479 := by
  unfold tailWord_4796906
  simp only [CollatzResearch.WordTrace]
  refine ⟨43739383789909070791594643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 116638356773090855444252381 43739383789909070791594643)
  ·
    refine ⟨65609075684863606187391965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43739383789909070791594643 65609075684863606187391965)
    ·
      refine ⟨24603403381823852320271987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 65609075684863606187391965 24603403381823852320271987)
      ·
        refine ⟨36905105072735778480407981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24603403381823852320271987 36905105072735778480407981)
        ·
          refine ⟨13839414402275916930152993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 36905105072735778480407981 13839414402275916930152993)
          ·
            refine ⟨10379560801706937697614745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13839414402275916930152993 10379560801706937697614745)
            ·
              refine ⟨7784670601280203273211059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10379560801706937697614745 7784670601280203273211059)
              ·
                refine ⟨11677005901920304909816589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7784670601280203273211059 11677005901920304909816589)
                ·
                  refine ⟨4378877213220114341181221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11677005901920304909816589 4378877213220114341181221)
                  ·
                    refine ⟨821039477478771438971479, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4378877213220114341181221 821039477478771438971479)
                    ·
                      rfl

theorem cell23_4796906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 2, 2, 1, 3, 4].length) (baseStart_4796906 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4796906 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4796906 prefixEnd_4796906 := by exact prefixLift 4796906
  have htrace : WordTrace (prefixWord ++ tailWord_4796906) baseStart_4796906 baseEnd_4796906 := by
    simpa [prefixWord, tailWord_4796906, baseEnd_4796906] using wordTrace_append hprefix tailTrace_4796906
  have hstable : (prefixWord ++ tailWord_4796906).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4796906).length < 2 ^ (prefixWord ++ tailWord_4796906).sum := by decide
  have hdescent : baseEnd_4796906 < baseStart_4796906 := by decide
  rcases family_descends (prefixWord ++ tailWord_4796906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4796949 : List Nat := [1, 3, 2, 1, 3, 1, 1, 5, 1, 5]
def baseStart_4796949 : Nat := 118140960795 + 4796949 * 2 ^ 59
def prefixEnd_4796949 : Nat := 4983230072969 + 3 ^ 40 * 4796949 * 2
def baseEnd_4796949 : Nat := 821046837368152549558913

theorem tailTrace_4796949 : CollatzResearch.WordTrace tailWord_4796949 prefixEnd_4796949 821046837368152549558913 := by
  unfold tailWord_4796949
  simp only [CollatzResearch.WordTrace]
  refine ⟨174959103498480501510193901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116639402332320334340129267 174959103498480501510193901)
  ·
    refine ⟨65609663811930188066322713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 174959103498480501510193901 65609663811930188066322713)
    ·
      refine ⟨49207247858947641049742035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 65609663811930188066322713 49207247858947641049742035)
      ·
        refine ⟨73810871788421461574613053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49207247858947641049742035 73810871788421461574613053)
        ·
          refine ⟨27679076920658048090479895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 73810871788421461574613053 27679076920658048090479895)
          ·
            refine ⟨41518615380987072135719843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27679076920658048090479895 41518615380987072135719843)
            ·
              refine ⟨62277923071480608203579765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41518615380987072135719843 62277923071480608203579765)
              ·
                refine ⟨5838555287951307019085603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 62277923071480608203579765 5838555287951307019085603)
                ·
                  refine ⟨8757832931926960528628405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5838555287951307019085603 8757832931926960528628405)
                  ·
                    refine ⟨821046837368152549558913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8757832931926960528628405 821046837368152549558913)
                    ·
                      rfl

theorem cell23_4796949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 1, 5, 1, 5].length) (baseStart_4796949 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4796949 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4796949 prefixEnd_4796949 := by exact prefixLift 4796949
  have htrace : WordTrace (prefixWord ++ tailWord_4796949) baseStart_4796949 baseEnd_4796949 := by
    simpa [prefixWord, tailWord_4796949, baseEnd_4796949] using wordTrace_append hprefix tailTrace_4796949
  have hstable : (prefixWord ++ tailWord_4796949).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4796949).length < 2 ^ (prefixWord ++ tailWord_4796949).sum := by decide
  have hdescent : baseEnd_4796949 < baseStart_4796949 := by decide
  rcases family_descends (prefixWord ++ tailWord_4796949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4796956 : List Nat := [2, 2, 3, 1, 2, 2, 1, 1, 4, 3, 2]
def baseStart_4796956 : Nat := 118140960795 + 4796956 * 2 ^ 59
def prefixEnd_4796956 : Nat := 4983230072969 + 3 ^ 40 * 4796956 * 2
def baseEnd_4796956 : Nat := 2463144106469039121289207

theorem tailTrace_4796956 : CollatzResearch.WordTrace tailWord_4796956 prefixEnd_4796956 2463144106469039121289207 := by
  unfold tailWord_4796956
  simp only [CollatzResearch.WordTrace]
  refine ⟨87479679404727570852849361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116639572539636761137132481 87479679404727570852849361)
  ·
    refine ⟨65609759553545678139637021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 87479679404727570852849361 65609759553545678139637021)
    ·
      refine ⟨24603659832579629302363883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 65609759553545678139637021 24603659832579629302363883)
      ·
        refine ⟨36905489748869443953545825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24603659832579629302363883 36905489748869443953545825)
        ·
          refine ⟨27679117311652082965159369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36905489748869443953545825 27679117311652082965159369)
          ·
            refine ⟨20759337983739062223869527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27679117311652082965159369 20759337983739062223869527)
            ·
              refine ⟨31139006975608593335804291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20759337983739062223869527 31139006975608593335804291)
              ·
                refine ⟨46708510463412890003706437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31139006975608593335804291 46708510463412890003706437)
                ·
                  refine ⟨8757845711889916875694957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 46708510463412890003706437 8757845711889916875694957)
                  ·
                    refine ⟨3284192141958718828385609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8757845711889916875694957 3284192141958718828385609)
                    ·
                      refine ⟨2463144106469039121289207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3284192141958718828385609 2463144106469039121289207)
                      ·
                        rfl

theorem cell23_4796956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 1, 1, 4, 3, 2].length) (baseStart_4796956 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4796956 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4796956 prefixEnd_4796956 := by exact prefixLift 4796956
  have htrace : WordTrace (prefixWord ++ tailWord_4796956) baseStart_4796956 baseEnd_4796956 := by
    simpa [prefixWord, tailWord_4796956, baseEnd_4796956] using wordTrace_append hprefix tailTrace_4796956
  have hstable : (prefixWord ++ tailWord_4796956).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4796956).length < 2 ^ (prefixWord ++ tailWord_4796956).sum := by decide
  have hdescent : baseEnd_4796956 < baseStart_4796956 := by decide
  rcases family_descends (prefixWord ++ tailWord_4796956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4796963 : List Nat := [1, 1, 1, 4, 4, 3, 1, 1, 3, 1, 3]
def baseStart_4796963 : Nat := 118140960795 + 4796963 * 2 ^ 59
def prefixEnd_4796963 : Nat := 4983230072969 + 3 ^ 40 * 4796963 * 2
def baseEnd_4796963 : Nat := 2463147700833620593901675

theorem tailTrace_4796963 : CollatzResearch.WordTrace tailWord_4796963 prefixEnd_4796963 2463147700833620593901675 := by
  unfold tailWord_4796963
  simp only [CollatzResearch.WordTrace]
  refine ⟨174959614120429781901203543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116639742746953187934135695 174959614120429781901203543)
  ·
    refine ⟨262439421180644672851805315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 174959614120429781901203543 262439421180644672851805315)
    ·
      refine ⟨393659131770967009277707973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 262439421180644672851805315 393659131770967009277707973)
      ·
        refine ⟨73811087207056314239570245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 393659131770967009277707973 73811087207056314239570245)
        ·
          refine ⟨13839578851323058919919421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 73811087207056314239570245 13839578851323058919919421)
          ·
            refine ⟨5189842069246147094969783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13839578851323058919919421 5189842069246147094969783)
            ·
              refine ⟨7784763103869220642454675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5189842069246147094969783 7784763103869220642454675)
              ·
                refine ⟨11677144655803830963682013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7784763103869220642454675 11677144655803830963682013)
                ·
                  refine ⟨4378929245926436611380755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11677144655803830963682013 4378929245926436611380755)
                  ·
                    refine ⟨6568393868889654917071133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4378929245926436611380755 6568393868889654917071133)
                    ·
                      refine ⟨2463147700833620593901675, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6568393868889654917071133 2463147700833620593901675)
                      ·
                        rfl

theorem cell23_4796963_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 3, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 3, 1, 1, 3, 1, 3].length) (baseStart_4796963 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4796963 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4796963 prefixEnd_4796963 := by exact prefixLift 4796963
  have htrace : WordTrace (prefixWord ++ tailWord_4796963) baseStart_4796963 baseEnd_4796963 := by
    simpa [prefixWord, tailWord_4796963, baseEnd_4796963] using wordTrace_append hprefix tailTrace_4796963
  have hstable : (prefixWord ++ tailWord_4796963).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4796963).length < 2 ^ (prefixWord ++ tailWord_4796963).sum := by decide
  have hdescent : baseEnd_4796963 < baseStart_4796963 := by decide
  rcases family_descends (prefixWord ++ tailWord_4796963) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4796986 : List Nat := [3, 1, 1, 1, 3, 3, 3, 2, 1, 1, 4]
def baseStart_4796986 : Nat := 118140960795 + 4796986 * 2 ^ 59
def prefixEnd_4796986 : Nat := 4983230072969 + 3 ^ 40 * 4796986 * 2
def baseEnd_4796986 : Nat := 2463159510888674003914069

theorem tailTrace_4796986 : CollatzResearch.WordTrace tailWord_4796986 prefixEnd_4796986 2463159510888674003914069 := by
  unfold tailWord_4796986
  simp only [CollatzResearch.WordTrace]
  refine ⟨43740113249836614207322703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 116640301999564304552860541 43740113249836614207322703)
  ·
    refine ⟨65610169874754921310984055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43740113249836614207322703 65610169874754921310984055)
    ·
      refine ⟨98415254812132381966476083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65610169874754921310984055 98415254812132381966476083)
      ·
        refine ⟨147622882218198572949714125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 98415254812132381966476083 147622882218198572949714125)
        ·
          refine ⟨55358580831824464856142797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 147622882218198572949714125 55358580831824464856142797)
          ·
            refine ⟨20759467811934174321053549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 55358580831824464856142797 20759467811934174321053549)
            ·
              refine ⟨7784800429475315370395081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20759467811934174321053549 7784800429475315370395081)
              ·
                refine ⟨5838600322106486527796311, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7784800429475315370395081 5838600322106486527796311)
                ·
                  refine ⟨8757900483159729791694467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5838600322106486527796311 8757900483159729791694467)
                  ·
                    refine ⟨13136850724739594687541701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8757900483159729791694467 13136850724739594687541701)
                    ·
                      refine ⟨2463159510888674003914069, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13136850724739594687541701 2463159510888674003914069)
                      ·
                        rfl

theorem cell23_4796986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 3, 2, 1, 1, 4].length) (baseStart_4796986 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4796986 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4796986 prefixEnd_4796986 := by exact prefixLift 4796986
  have htrace : WordTrace (prefixWord ++ tailWord_4796986) baseStart_4796986 baseEnd_4796986 := by
    simpa [prefixWord, tailWord_4796986, baseEnd_4796986] using wordTrace_append hprefix tailTrace_4796986
  have hstable : (prefixWord ++ tailWord_4796986).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4796986).length < 2 ^ (prefixWord ++ tailWord_4796986).sum := by decide
  have hdescent : baseEnd_4796986 < baseStart_4796986 := by decide
  rcases family_descends (prefixWord ++ tailWord_4796986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4796992 : List Nat := [2, 1, 1, 2, 2, 2, 4, 9]
def baseStart_4796992 : Nat := 118140960795 + 4796992 * 2 ^ 59
def prefixEnd_4796992 : Nat := 4983230072969 + 3 ^ 40 * 4796992 * 2
def baseEnd_4796992 : Nat := 91228244139725962238483

theorem tailTrace_4796992 : CollatzResearch.WordTrace tailWord_4796992 prefixEnd_4796992 91228244139725962238483 := by
  unfold tailWord_4796992
  simp only [CollatzResearch.WordTrace]
  refine ⟨87480335918662359927004615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 116640447891549813236006153 87480335918662359927004615)
  ·
    refine ⟨131220503877993539890506923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87480335918662359927004615 131220503877993539890506923)
    ·
      refine ⟨196830755816990309835760385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 131220503877993539890506923 196830755816990309835760385)
      ·
        refine ⟨147623066862742732376820289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 196830755816990309835760385 147623066862742732376820289)
        ·
          refine ⟨110717300147057049282615217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 147623066862742732376820289 110717300147057049282615217)
          ·
            refine ⟨83037975110292786961961413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 110717300147057049282615217 83037975110292786961961413)
            ·
              refine ⟨15569620333179897555367765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 83037975110292786961961413 15569620333179897555367765)
              ·
                refine ⟨91228244139725962238483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 15569620333179897555367765 91228244139725962238483)
                ·
                  rfl

theorem cell23_4796992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 4, 9].length) (baseStart_4796992 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4796992 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4796992 prefixEnd_4796992 := by exact prefixLift 4796992
  have htrace : WordTrace (prefixWord ++ tailWord_4796992) baseStart_4796992 baseEnd_4796992 := by
    simpa [prefixWord, tailWord_4796992, baseEnd_4796992] using wordTrace_append hprefix tailTrace_4796992
  have hstable : (prefixWord ++ tailWord_4796992).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4796992).length < 2 ^ (prefixWord ++ tailWord_4796992).sum := by decide
  have hdescent : baseEnd_4796992 < baseStart_4796992 := by decide
  rcases family_descends (prefixWord ++ tailWord_4796992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4796999 : List Nat := [1, 1, 4, 1, 4, 1, 1, 1, 3, 2, 4]
def baseStart_4796999 : Nat := 118140960795 + 4796999 * 2 ^ 59
def prefixEnd_4796999 : Nat := 4983230072969 + 3 ^ 40 * 4796999 * 2
def baseEnd_4796999 : Nat := 2463166186137182453051509

theorem tailTrace_4796999 : CollatzResearch.WordTrace tailWord_4796999 prefixEnd_4796999 2463166186137182453051509 := by
  unfold tailWord_4796999
  simp only [CollatzResearch.WordTrace]
  refine ⟨174960927148299360049514051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116640618098866240033009367 174960927148299360049514051)
  ·
    refine ⟨262441390722449040074271077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 174960927148299360049514051 262441390722449040074271077)
    ·
      refine ⟨49207760760459195013925827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 262441390722449040074271077 49207760760459195013925827)
      ·
        refine ⟨73811641140688792520888741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49207760760459195013925827 73811641140688792520888741)
        ·
          refine ⟨13839682713879148597666639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 73811641140688792520888741 13839682713879148597666639)
          ·
            refine ⟨20759524070818722896499959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13839682713879148597666639 20759524070818722896499959)
            ·
              refine ⟨31139286106228084344749939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20759524070818722896499959 31139286106228084344749939)
              ·
                refine ⟨46708929159342126517124909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31139286106228084344749939 46708929159342126517124909)
                ·
                  refine ⟨17515848434753297443921841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 46708929159342126517124909 17515848434753297443921841)
                  ·
                    refine ⟨13136886326064973082941381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17515848434753297443921841 13136886326064973082941381)
                    ·
                      refine ⟨2463166186137182453051509, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13136886326064973082941381 2463166186137182453051509)
                      ·
                        rfl

theorem cell23_4796999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 1, 1, 3, 2, 4].length) (baseStart_4796999 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4796999 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4796999 prefixEnd_4796999 := by exact prefixLift 4796999
  have htrace : WordTrace (prefixWord ++ tailWord_4796999) baseStart_4796999 baseEnd_4796999 := by
    simpa [prefixWord, tailWord_4796999, baseEnd_4796999] using wordTrace_append hprefix tailTrace_4796999
  have hstable : (prefixWord ++ tailWord_4796999).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4796999).length < 2 ^ (prefixWord ++ tailWord_4796999).sum := by decide
  have hdescent : baseEnd_4796999 < baseStart_4796999 := by decide
  rcases family_descends (prefixWord ++ tailWord_4796999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4797006 : List Nat := [4, 1, 1, 1, 1, 2, 2, 5, 1, 2, 3]
def baseStart_4797006 : Nat := 118140960795 + 4797006 * 2 ^ 59
def prefixEnd_4797006 : Nat := 4983230072969 + 3 ^ 40 * 4797006 * 2
def baseEnd_4797006 : Nat := 2463169780501763925663977

theorem tailTrace_4797006 : CollatzResearch.WordTrace tailWord_4797006 prefixEnd_4797006 2463169780501763925663977 := by
  unfold tailWord_4797006
  simp only [CollatzResearch.WordTrace]
  refine ⟨21870147807409250030627359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 116640788306182666830012581 21870147807409250030627359)
  ·
    refine ⟨32805221711113875045941039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21870147807409250030627359 32805221711113875045941039)
    ·
      refine ⟨49207832566670812568911559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32805221711113875045941039 49207832566670812568911559)
      ·
        refine ⟨73811748850006218853367339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49207832566670812568911559 73811748850006218853367339)
        ·
          refine ⟨110717623275009328280051009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 73811748850006218853367339 110717623275009328280051009)
          ·
            refine ⟨83038217456256996210038257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 110717623275009328280051009 83038217456256996210038257)
            ·
              refine ⟨62278663092192747157528693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 83038217456256996210038257 62278663092192747157528693)
              ·
                refine ⟨5838624664893070046018315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 62278663092192747157528693 5838624664893070046018315)
                ·
                  refine ⟨8757936997339605069027473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5838624664893070046018315 8757936997339605069027473)
                  ·
                    refine ⟨6568452748004703801770605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8757936997339605069027473 6568452748004703801770605)
                    ·
                      refine ⟨2463169780501763925663977, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6568452748004703801770605 2463169780501763925663977)
                      ·
                        rfl

theorem cell23_4797006_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 2, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 2, 5, 1, 2, 3].length) (baseStart_4797006 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4797006 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4797006 prefixEnd_4797006 := by exact prefixLift 4797006
  have htrace : WordTrace (prefixWord ++ tailWord_4797006) baseStart_4797006 baseEnd_4797006 := by
    simpa [prefixWord, tailWord_4797006, baseEnd_4797006] using wordTrace_append hprefix tailTrace_4797006
  have hstable : (prefixWord ++ tailWord_4797006).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4797006).length < 2 ^ (prefixWord ++ tailWord_4797006).sum := by decide
  have hdescent : baseEnd_4797006 < baseStart_4797006 := by decide
  rcases family_descends (prefixWord ++ tailWord_4797006) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4797063 : List Nat := [1, 1, 4, 2, 1, 2, 3, 3, 1, 3, 2]
def baseStart_4797063 : Nat := 118140960795 + 4797063 * 2 ^ 59
def prefixEnd_4797063 : Nat := 4983230072969 + 3 ^ 40 * 4797063 * 2
def baseEnd_4797063 : Nat := 2463199048899070202651215

theorem tailTrace_4797063 : CollatzResearch.WordTrace tailWord_4797063 prefixEnd_4797063 2463199048899070202651215 := by
  unfold tailWord_4797063
  simp only [CollatzResearch.WordTrace]
  refine ⟨174963261420067498979843843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 116642174280044999319895895 174963261420067498979843843)
  ·
    refine ⟨262444892130101248469765765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 174963261420067498979843843 262444892130101248469765765)
    ·
      refine ⟨49208417274393984088081081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 262444892130101248469765765 49208417274393984088081081)
      ·
        refine ⟨36906312955795488066060811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49208417274393984088081081 36906312955795488066060811)
        ·
          refine ⟨55359469433693232099091217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36906312955795488066060811 55359469433693232099091217)
          ·
            refine ⟨41519602075269924074318413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 55359469433693232099091217 41519602075269924074318413)
            ·
              refine ⟨15569850778226221527869405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 41519602075269924074318413 15569850778226221527869405)
              ·
                refine ⟨5838694041834833072951027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15569850778226221527869405 5838694041834833072951027)
                ·
                  refine ⟨8758041062752249609426541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5838694041834833072951027 8758041062752249609426541)
                  ·
                    refine ⟨3284265398532093603534953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8758041062752249609426541 3284265398532093603534953)
                    ·
                      refine ⟨2463199048899070202651215, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3284265398532093603534953 2463199048899070202651215)
                      ·
                        rfl

theorem cell23_4797063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 3, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 3, 3, 1, 3, 2].length) (baseStart_4797063 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4797063 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4797063 prefixEnd_4797063 := by exact prefixLift 4797063
  have htrace : WordTrace (prefixWord ++ tailWord_4797063) baseStart_4797063 baseEnd_4797063 := by
    simpa [prefixWord, tailWord_4797063, baseEnd_4797063] using wordTrace_append hprefix tailTrace_4797063
  have hstable : (prefixWord ++ tailWord_4797063).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4797063).length < 2 ^ (prefixWord ++ tailWord_4797063).sum := by decide
  have hdescent : baseEnd_4797063 < baseStart_4797063 := by decide
  rcases family_descends (prefixWord ++ tailWord_4797063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4797086 : List Nat := [4, 3, 1, 1, 1, 1, 1, 3, 2, 6]
def baseStart_4797086 : Nat := 118140960795 + 4797086 * 2 ^ 59
def prefixEnd_4797086 : Nat := 4983230072969 + 3 ^ 40 * 4797086 * 2
def baseEnd_4797086 : Nat := 821070286318041204221203

theorem tailTrace_4797086 : CollatzResearch.WordTrace tailWord_4797086 prefixEnd_4797086 821070286318041204221203 := by
  unfold tailWord_4797086
  simp only [CollatzResearch.WordTrace]
  refine ⟨21870512537373021738491389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 116642733532656115938620741 21870512537373021738491389)
  ·
    refine ⟨8201442201514883151934271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21870512537373021738491389 8201442201514883151934271)
    ·
      refine ⟨12302163302272324727901407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8201442201514883151934271 12302163302272324727901407)
      ·
        refine ⟨18453244953408487091852111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12302163302272324727901407 18453244953408487091852111)
        ·
          refine ⟨27679867430112730637778167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18453244953408487091852111 27679867430112730637778167)
          ·
            refine ⟨41519801145169095956667251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27679867430112730637778167 41519801145169095956667251)
            ·
              refine ⟨62279701717753643935000877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41519801145169095956667251 62279701717753643935000877)
              ·
                refine ⟨23354888144157616475625329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 62279701717753643935000877 23354888144157616475625329)
                ·
                  refine ⟨17516166108118212356718997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23354888144157616475625329 17516166108118212356718997)
                  ·
                    refine ⟨821070286318041204221203, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17516166108118212356718997 821070286318041204221203)
                    ·
                      rfl

theorem cell23_4797086_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 1, 3, 2, 6].length) (baseStart_4797086 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4797086 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4797086 prefixEnd_4797086 := by exact prefixLift 4797086
  have htrace : WordTrace (prefixWord ++ tailWord_4797086) baseStart_4797086 baseEnd_4797086 := by
    simpa [prefixWord, tailWord_4797086, baseEnd_4797086] using wordTrace_append hprefix tailTrace_4797086
  have hstable : (prefixWord ++ tailWord_4797086).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4797086).length < 2 ^ (prefixWord ++ tailWord_4797086).sum := by decide
  have hdescent : baseEnd_4797086 < baseStart_4797086 := by decide
  rcases family_descends (prefixWord ++ tailWord_4797086) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
