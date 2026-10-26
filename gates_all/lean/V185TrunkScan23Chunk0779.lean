import V185TrunkScan23Chunk0778

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_4607233 : List Nat := [1, 2, 4, 1, 1, 3, 1, 2, 3, 1, 4]
def baseStart_4607233 : Nat := 118140960795 + 4607233 * 2 ^ 59
def prefixEnd_4607233 : Nat := 4983230072969 + 3 ^ 40 * 4607233 * 2
def baseEnd_4607233 : Nat := 2365725016256077913399227

theorem tailTrace_4607233 : CollatzResearch.WordTrace tailWord_4607233 prefixEnd_4607233 2365725016256077913399227 := by
  unfold tailWord_4607233
  simp only [CollatzResearch.WordTrace]
  refine ⟨168039592517789168596962353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112026395011859445731308235 168039592517789168596962353)
  ·
    refine ⟨126029694388341876447721765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 168039592517789168596962353 126029694388341876447721765)
    ·
      refine ⟨23630567697814101833947831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 126029694388341876447721765 23630567697814101833947831)
      ·
        refine ⟨35445851546721152750921747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23630567697814101833947831 35445851546721152750921747)
        ·
          refine ⟨53168777320081729126382621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35445851546721152750921747 53168777320081729126382621)
          ·
            refine ⟨19938291495030648422393483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 53168777320081729126382621 19938291495030648422393483)
            ·
              refine ⟨29907437242545972633590225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19938291495030648422393483 29907437242545972633590225)
              ·
                refine ⟨22430577931909479475192669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29907437242545972633590225 22430577931909479475192669)
                ·
                  refine ⟨8411466724466054803197251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22430577931909479475192669 8411466724466054803197251)
                  ·
                    refine ⟨12617200086699082204795877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8411466724466054803197251 12617200086699082204795877)
                    ·
                      refine ⟨2365725016256077913399227, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12617200086699082204795877 2365725016256077913399227)
                      ·
                        rfl

theorem cell23_4607233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 1, 2, 3, 1, 4].length) (baseStart_4607233 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4607233 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4607233 prefixEnd_4607233 := by exact prefixLift 4607233
  have htrace : WordTrace (prefixWord ++ tailWord_4607233) baseStart_4607233 baseEnd_4607233 := by
    simpa [prefixWord, tailWord_4607233, baseEnd_4607233] using wordTrace_append hprefix tailTrace_4607233
  have hstable : (prefixWord ++ tailWord_4607233).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4607233).length < 2 ^ (prefixWord ++ tailWord_4607233).sum := by decide
  have hdescent : baseEnd_4607233 < baseStart_4607233 := by decide
  rcases family_descends (prefixWord ++ tailWord_4607233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4607243 : List Nat := [1, 1, 1, 1, 5, 4, 2, 1, 1, 6]
def baseStart_4607243 : Nat := 118140960795 + 4607243 * 2 ^ 59
def prefixEnd_4607243 : Nat := 4983230072969 + 3 ^ 40 * 4607243 * 2
def baseEnd_4607243 : Nat := 788576717020874291424727

theorem tailTrace_4607243 : CollatzResearch.WordTrace tailWord_4607243 prefixEnd_4607243 788576717020874291424727 := by
  unfold tailWord_4607243
  simp only [CollatzResearch.WordTrace]
  refine ⟨168039957247752940304826383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112026638165168626869884255 168039957247752940304826383)
  ·
    refine ⟨252059935871629410457239575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 168039957247752940304826383 252059935871629410457239575)
    ·
      refine ⟨378089903807444115685859363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 252059935871629410457239575 378089903807444115685859363)
      ·
        refine ⟨567134855711166173528789045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 378089903807444115685859363 567134855711166173528789045)
        ·
          refine ⟨53168892722921828768323973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 567134855711166173528789045 53168892722921828768323973)
          ·
            refine ⟨9969167385547842894060745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 53168892722921828768323973 9969167385547842894060745)
            ·
              refine ⟨7476875539160882170545559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9969167385547842894060745 7476875539160882170545559)
              ·
                refine ⟨11215313308741323255818339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7476875539160882170545559 11215313308741323255818339)
                ·
                  refine ⟨16822969963111984883727509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11215313308741323255818339 16822969963111984883727509)
                  ·
                    refine ⟨788576717020874291424727, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16822969963111984883727509 788576717020874291424727)
                    ·
                      rfl

theorem cell23_4607243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 4, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 4, 2, 1, 1, 6].length) (baseStart_4607243 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4607243 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4607243 prefixEnd_4607243 := by exact prefixLift 4607243
  have htrace : WordTrace (prefixWord ++ tailWord_4607243) baseStart_4607243 baseEnd_4607243 := by
    simpa [prefixWord, tailWord_4607243, baseEnd_4607243] using wordTrace_append hprefix tailTrace_4607243
  have hstable : (prefixWord ++ tailWord_4607243).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4607243).length < 2 ^ (prefixWord ++ tailWord_4607243).sum := by decide
  have hdescent : baseEnd_4607243 < baseStart_4607243 := by decide
  rcases family_descends (prefixWord ++ tailWord_4607243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4607264 : List Nat := [2, 1, 1, 5, 4, 1, 2, 1, 1, 5]
def baseStart_4607264 : Nat := 118140960795 + 4607264 * 2 ^ 59
def prefixEnd_4607264 : Nat := 4983230072969 + 3 ^ 40 * 4607264 * 2
def baseEnd_4607264 : Nat := 788580311385455764037195

theorem tailTrace_4607264 : CollatzResearch.WordTrace tailWord_4607264 prefixEnd_4607264 788580311385455764037195 := by
  unfold tailWord_4607264
  simp only [CollatzResearch.WordTrace]
  refine ⟨84020361590338430445670423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 112027148787117907260893897 84020361590338430445670423)
  ·
    refine ⟨126030542385507645668505635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84020361590338430445670423 126030542385507645668505635)
    ·
      refine ⟨189045813578261468502758453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 126030542385507645668505635 189045813578261468502758453)
      ·
        refine ⟨17723045022962012672133605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 189045813578261468502758453 17723045022962012672133605)
        ·
          refine ⟨3323070941805377376025051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 17723045022962012672133605 3323070941805377376025051)
          ·
            refine ⟨4984606412708066064037577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3323070941805377376025051 4984606412708066064037577)
            ·
              refine ⟨3738454809531049548028183, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4984606412708066064037577 3738454809531049548028183)
              ·
                refine ⟨5607682214296574322042275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3738454809531049548028183 5607682214296574322042275)
                ·
                  refine ⟨8411523321444861483063413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5607682214296574322042275 8411523321444861483063413)
                  ·
                    refine ⟨788580311385455764037195, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8411523321444861483063413 788580311385455764037195)
                    ·
                      rfl

theorem cell23_4607264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 4, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 4, 1, 2, 1, 1, 5].length) (baseStart_4607264 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4607264 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4607264 prefixEnd_4607264 := by exact prefixLift 4607264
  have htrace : WordTrace (prefixWord ++ tailWord_4607264) baseStart_4607264 baseEnd_4607264 := by
    simpa [prefixWord, tailWord_4607264, baseEnd_4607264] using wordTrace_append hprefix tailTrace_4607264
  have hstable : (prefixWord ++ tailWord_4607264).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4607264).length < 2 ^ (prefixWord ++ tailWord_4607264).sum := by decide
  have hdescent : baseEnd_4607264 < baseStart_4607264 := by decide
  rcases family_descends (prefixWord ++ tailWord_4607264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4607267 : List Nat := [1, 1, 1, 4, 2, 5, 2, 1, 1, 1, 4]
def baseStart_4607267 : Nat := 118140960795 + 4607267 * 2 ^ 59
def prefixEnd_4607267 : Nat := 4983230072969 + 3 ^ 40 * 4607267 * 2
def baseEnd_4607267 : Nat := 2365742474598330780374071

theorem tailTrace_4607267 : CollatzResearch.WordTrace tailWord_4607267 prefixEnd_4607267 2365742474598330780374071 := by
  unfold tailWord_4607267
  simp only [CollatzResearch.WordTrace]
  refine ⟨168040832599665992403700055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112027221733110661602466703 168040832599665992403700055)
  ·
    refine ⟨252061248899498988605550083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 168040832599665992403700055 252061248899498988605550083)
    ·
      refine ⟨378091873349248482908325125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 252061248899498988605550083 378091873349248482908325125)
      ·
        refine ⟨70892226252984090545310961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 378091873349248482908325125 70892226252984090545310961)
        ·
          refine ⟨53169169689738067908983221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 70892226252984090545310961 53169169689738067908983221)
          ·
            refine ⟨4984609658412943866467177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 53169169689738067908983221 4984609658412943866467177)
            ·
              refine ⟨3738457243809707899850383, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4984609658412943866467177 3738457243809707899850383)
              ·
                refine ⟨5607685865714561849775575, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3738457243809707899850383 5607685865714561849775575)
                ·
                  refine ⟨8411528798571842774663363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5607685865714561849775575 8411528798571842774663363)
                  ·
                    refine ⟨12617293197857764161995045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8411528798571842774663363 12617293197857764161995045)
                    ·
                      refine ⟨2365742474598330780374071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12617293197857764161995045 2365742474598330780374071)
                      ·
                        rfl

theorem cell23_4607267_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 5, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 5, 2, 1, 1, 1, 4].length) (baseStart_4607267 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4607267 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4607267 prefixEnd_4607267 := by exact prefixLift 4607267
  have htrace : WordTrace (prefixWord ++ tailWord_4607267) baseStart_4607267 baseEnd_4607267 := by
    simpa [prefixWord, tailWord_4607267, baseEnd_4607267] using wordTrace_append hprefix tailTrace_4607267
  have hstable : (prefixWord ++ tailWord_4607267).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4607267).length < 2 ^ (prefixWord ++ tailWord_4607267).sum := by decide
  have hdescent : baseEnd_4607267 < baseStart_4607267 := by decide
  rcases family_descends (prefixWord ++ tailWord_4607267) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4607276 : List Nat := [2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 6]
def baseStart_4607276 : Nat := 118140960795 + 4607276 * 2 ^ 59
def prefixEnd_4607276 : Nat := 4983230072969 + 3 ^ 40 * 4607276 * 2
def baseEnd_4607276 : Nat := 2365747095924221245161529

theorem tailTrace_4607276 : CollatzResearch.WordTrace tailWord_4607276 prefixEnd_4607276 2365747095924221245161529 := by
  unfold tailWord_4607276
  simp only [CollatzResearch.WordTrace]
  refine ⟨84020580428316693470388841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 112027440571088924627185121 84020580428316693470388841)
  ·
    refine ⟨63015435321237520102791631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 84020580428316693470388841 63015435321237520102791631)
    ·
      refine ⟨94523152981856280154187447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63015435321237520102791631 94523152981856280154187447)
      ·
        refine ⟨141784729472784420231281171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 94523152981856280154187447 141784729472784420231281171)
        ·
          refine ⟨212677094209176630346921757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 141784729472784420231281171 212677094209176630346921757)
          ·
            refine ⟨79753910328441236380095659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 212677094209176630346921757 79753910328441236380095659)
            ·
              refine ⟨119630865492661854570143489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 79753910328441236380095659 119630865492661854570143489)
              ·
                refine ⟨89723149119496390927607617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 119630865492661854570143489 89723149119496390927607617)
                ·
                  refine ⟨67292361839622293195705713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 89723149119496390927607617 67292361839622293195705713)
                  ·
                    refine ⟨50469271379716719896779285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 67292361839622293195705713 50469271379716719896779285)
                    ·
                      refine ⟨2365747095924221245161529, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 50469271379716719896779285 2365747095924221245161529)
                      ·
                        rfl

theorem cell23_4607276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 6].length) (baseStart_4607276 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4607276 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4607276 prefixEnd_4607276 := by exact prefixLift 4607276
  have htrace : WordTrace (prefixWord ++ tailWord_4607276) baseStart_4607276 baseEnd_4607276 := by
    simpa [prefixWord, tailWord_4607276, baseEnd_4607276] using wordTrace_append hprefix tailTrace_4607276
  have hstable : (prefixWord ++ tailWord_4607276).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4607276).length < 2 ^ (prefixWord ++ tailWord_4607276).sum := by decide
  have hdescent : baseEnd_4607276 < baseStart_4607276 := by decide
  rcases family_descends (prefixWord ++ tailWord_4607276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4607277 : List Nat := [1, 5, 3, 1, 1, 2, 1, 1, 4, 4]
def baseStart_4607277 : Nat := 118140960795 + 4607277 * 2 ^ 59
def prefixEnd_4607277 : Nat := 4983230072969 + 3 ^ 40 * 4607277 * 2
def baseEnd_4607277 : Nat := 788582536468291913749675

theorem tailTrace_4607277 : CollatzResearch.WordTrace tailWord_4607277 prefixEnd_4607277 788582536468291913749675 := by
  unfold tailWord_4607277
  simp only [CollatzResearch.WordTrace]
  refine ⟨168041197329629764111564085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112027464886419842741042723 168041197329629764111564085)
  ·
    refine ⟨15753862249652790385459133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 168041197329629764111564085 15753862249652790385459133)
    ·
      refine ⟨5907698343619796394547175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15753862249652790385459133 5907698343619796394547175)
      ·
        refine ⟨8861547515429694591820763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5907698343619796394547175 8861547515429694591820763)
        ·
          refine ⟨13292321273144541887731145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8861547515429694591820763 13292321273144541887731145)
          ·
            refine ⟨9969240954858406415798359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13292321273144541887731145 9969240954858406415798359)
            ·
              refine ⟨14953861432287609623697539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9969240954858406415798359 14953861432287609623697539)
              ·
                refine ⟨22430792148431414435546309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14953861432287609623697539 22430792148431414435546309)
                ·
                  refine ⟨4205773527830890206664933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 22430792148431414435546309 4205773527830890206664933)
                  ·
                    refine ⟨788582536468291913749675, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4205773527830890206664933 788582536468291913749675)
                    ·
                      rfl

theorem cell23_4607277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 2, 1, 1, 4, 4].length) (baseStart_4607277 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4607277 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4607277 prefixEnd_4607277 := by exact prefixLift 4607277
  have htrace : WordTrace (prefixWord ++ tailWord_4607277) baseStart_4607277 baseEnd_4607277 := by
    simpa [prefixWord, tailWord_4607277, baseEnd_4607277] using wordTrace_append hprefix tailTrace_4607277
  have hstable : (prefixWord ++ tailWord_4607277).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4607277).length < 2 ^ (prefixWord ++ tailWord_4607277).sum := by decide
  have hdescent : baseEnd_4607277 < baseStart_4607277 := by decide
  rcases family_descends (prefixWord ++ tailWord_4607277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4607284 : List Nat := [2, 5, 1, 1, 1, 1, 4, 1, 3, 2, 2]
def baseStart_4607284 : Nat := 118140960795 + 4607284 * 2 ^ 59
def prefixEnd_4607284 : Nat := 4983230072969 + 3 ^ 40 * 4607284 * 2
def baseEnd_4607284 : Nat := 2365751203769457213861493

theorem tailTrace_4607284 : CollatzResearch.WordTrace tailWord_4607284 prefixEnd_4607284 2365751203769457213861493 := by
  unfold tailWord_4607284
  simp only [CollatzResearch.WordTrace]
  refine ⟨84020726320302202153534453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 112027635093736269538045937 84020726320302202153534453)
  ·
    refine ⟨7876943092528331451893855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 84020726320302202153534453 7876943092528331451893855)
    ·
      refine ⟨11815414638792497177840783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7876943092528331451893855 11815414638792497177840783)
      ·
        refine ⟨17723121958188745766761175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11815414638792497177840783 17723121958188745766761175)
        ·
          refine ⟨26584682937283118650141763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17723121958188745766761175 26584682937283118650141763)
          ·
            refine ⟨39877024405924677975212645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26584682937283118650141763 39877024405924677975212645)
            ·
              refine ⟨7476942076110877120352371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 39877024405924677975212645 7476942076110877120352371)
              ·
                refine ⟨11215413114166315680528557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7476942076110877120352371 11215413114166315680528557)
                ·
                  refine ⟨4205779917812368380198209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11215413114166315680528557 4205779917812368380198209)
                  ·
                    refine ⟨3154334938359276285148657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4205779917812368380198209 3154334938359276285148657)
                    ·
                      refine ⟨2365751203769457213861493, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3154334938359276285148657 2365751203769457213861493)
                      ·
                        rfl

theorem cell23_4607284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 4, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 4, 1, 3, 2, 2].length) (baseStart_4607284 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4607284 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4607284 prefixEnd_4607284 := by exact prefixLift 4607284
  have htrace : WordTrace (prefixWord ++ tailWord_4607284) baseStart_4607284 baseEnd_4607284 := by
    simpa [prefixWord, tailWord_4607284, baseEnd_4607284] using wordTrace_append hprefix tailTrace_4607284
  have hstable : (prefixWord ++ tailWord_4607284).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4607284).length < 2 ^ (prefixWord ++ tailWord_4607284).sum := by decide
  have hdescent : baseEnd_4607284 < baseStart_4607284 := by decide
  rcases family_descends (prefixWord ++ tailWord_4607284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4607297 : List Nat := [1, 2, 5, 2, 1, 3, 1, 1, 1, 2, 4]
def baseStart_4607297 : Nat := 118140960795 + 4607297 * 2 ^ 59
def prefixEnd_4607297 : Nat := 4983230072969 + 3 ^ 40 * 4607297 * 2
def baseEnd_4607297 : Nat := 2365757879017965662998933

theorem tailTrace_4607297 : CollatzResearch.WordTrace tailWord_4607297 prefixEnd_4607297 2365757879017965662998933 := by
  unfold tailWord_4607297
  simp only [CollatzResearch.WordTrace]
  refine ⟨168041926789557307527292145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112027951193038205018194763 168041926789557307527292145)
  ·
    refine ⟨126031445092167980645469109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 168041926789557307527292145 126031445092167980645469109)
    ·
      refine ⟨11815447977390748185512729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 126031445092167980645469109 11815447977390748185512729)
      ·
        refine ⟨8861585983043061139134547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11815447977390748185512729 8861585983043061139134547)
        ·
          refine ⟨13292378974564591708701821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8861585983043061139134547 13292378974564591708701821)
          ·
            refine ⟨4984642115461721890763183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13292378974564591708701821 4984642115461721890763183)
            ·
              refine ⟨7476963173192582836144775, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4984642115461721890763183 7476963173192582836144775)
              ·
                refine ⟨11215444759788874254217163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7476963173192582836144775 11215444759788874254217163)
                ·
                  refine ⟨16823167139683311381325745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11215444759788874254217163 16823167139683311381325745)
                  ·
                    refine ⟨12617375354762483535994309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16823167139683311381325745 12617375354762483535994309)
                    ·
                      refine ⟨2365757879017965662998933, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12617375354762483535994309 2365757879017965662998933)
                      ·
                        rfl

theorem cell23_4607297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 3, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 3, 1, 1, 1, 2, 4].length) (baseStart_4607297 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4607297 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4607297 prefixEnd_4607297 := by exact prefixLift 4607297
  have htrace : WordTrace (prefixWord ++ tailWord_4607297) baseStart_4607297 baseEnd_4607297 := by
    simpa [prefixWord, tailWord_4607297, baseEnd_4607297] using wordTrace_append hprefix tailTrace_4607297
  have hstable : (prefixWord ++ tailWord_4607297).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4607297).length < 2 ^ (prefixWord ++ tailWord_4607297).sum := by decide
  have hdescent : baseEnd_4607297 < baseStart_4607297 := by decide
  rcases family_descends (prefixWord ++ tailWord_4607297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4607343 : List Nat := [1, 1, 2, 1, 3, 1, 4, 1, 2, 4, 3]
def baseStart_4607343 : Nat := 118140960795 + 4607343 * 2 ^ 59
def prefixEnd_4607343 : Nat := 4983230072969 + 3 ^ 40 * 4607343 * 2
def baseEnd_4607343 : Nat := 2365781499128072483023721

theorem tailTrace_4607343 : CollatzResearch.WordTrace tailWord_4607343 prefixEnd_4607343 2365781499128072483023721 := by
  unfold tailWord_4607343
  simp only [CollatzResearch.WordTrace]
  refine ⟨168043604547390657383466683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112029069698260438255644455 168043604547390657383466683)
  ·
    refine ⟨252065406821085986075200025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 168043604547390657383466683 252065406821085986075200025)
    ·
      refine ⟨189049055115814489556400019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 252065406821085986075200025 189049055115814489556400019)
      ·
        refine ⟨283573582673721734334600029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 189049055115814489556400019 283573582673721734334600029)
        ·
          refine ⟨106340093502645650375475011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 283573582673721734334600029 106340093502645650375475011)
          ·
            refine ⟨159510140253968475563212517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 106340093502645650375475011 159510140253968475563212517)
            ·
              refine ⟨29908151297619089168102347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 159510140253968475563212517 29908151297619089168102347)
              ·
                refine ⟨44862226946428633752153521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29908151297619089168102347 44862226946428633752153521)
                ·
                  refine ⟨33646670209821475314115141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 44862226946428633752153521 33646670209821475314115141)
                  ·
                    refine ⟨6308750664341526621396589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 33646670209821475314115141 6308750664341526621396589)
                    ·
                      refine ⟨2365781499128072483023721, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6308750664341526621396589 2365781499128072483023721)
                      ·
                        rfl

theorem cell23_4607343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 4, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 4, 1, 2, 4, 3].length) (baseStart_4607343 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4607343 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4607343 prefixEnd_4607343 := by exact prefixLift 4607343
  have htrace : WordTrace (prefixWord ++ tailWord_4607343) baseStart_4607343 baseEnd_4607343 := by
    simpa [prefixWord, tailWord_4607343, baseEnd_4607343] using wordTrace_append hprefix tailTrace_4607343
  have hstable : (prefixWord ++ tailWord_4607343).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4607343).length < 2 ^ (prefixWord ++ tailWord_4607343).sum := by decide
  have hdescent : baseEnd_4607343 < baseStart_4607343 := by decide
  rcases family_descends (prefixWord ++ tailWord_4607343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4607353 : List Nat := [1, 2, 1, 3, 2, 1, 2, 3, 2, 2, 4]
def baseStart_4607353 : Nat := 118140960795 + 4607353 * 2 ^ 59
def prefixEnd_4607353 : Nat := 4983230072969 + 3 ^ 40 * 4607353 * 2
def baseEnd_4607353 : Nat := 2365786633934617443898675

theorem tailTrace_4607353 : CollatzResearch.WordTrace tailWord_4607353 prefixEnd_4607353 2365786633934617443898675 := by
  unfold tailWord_4607353
  simp only [CollatzResearch.WordTrace]
  refine ⟨168043969277354429091330713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112029312851569619394220475 168043969277354429091330713)
  ·
    refine ⟨126032976958015821818498035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 168043969277354429091330713 126032976958015821818498035)
    ·
      refine ⟨189049465437023732727747053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 126032976958015821818498035 189049465437023732727747053)
      ·
        refine ⟨70893549538883899772905145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 189049465437023732727747053 70893549538883899772905145)
        ·
          refine ⟨53170162154162924829678859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 70893549538883899772905145 53170162154162924829678859)
          ·
            refine ⟨79755243231244387244518289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53170162154162924829678859 79755243231244387244518289)
            ·
              refine ⟨59816432423433290433388717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 79755243231244387244518289 59816432423433290433388717)
              ·
                refine ⟨22431162158787483912520769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 59816432423433290433388717 22431162158787483912520769)
                ·
                  refine ⟨16823371619090612934390577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22431162158787483912520769 16823371619090612934390577)
                  ·
                    refine ⟨12617528714317959700792933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16823371619090612934390577 12617528714317959700792933)
                    ·
                      refine ⟨2365786633934617443898675, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12617528714317959700792933 2365786633934617443898675)
                      ·
                        rfl

theorem cell23_4607353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 2, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 2, 3, 2, 2, 4].length) (baseStart_4607353 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4607353 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4607353 prefixEnd_4607353 := by exact prefixLift 4607353
  have htrace : WordTrace (prefixWord ++ tailWord_4607353) baseStart_4607353 baseEnd_4607353 := by
    simpa [prefixWord, tailWord_4607353, baseEnd_4607353] using wordTrace_append hprefix tailTrace_4607353
  have hstable : (prefixWord ++ tailWord_4607353).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4607353).length < 2 ^ (prefixWord ++ tailWord_4607353).sum := by decide
  have hdescent : baseEnd_4607353 < baseStart_4607353 := by decide
  rcases family_descends (prefixWord ++ tailWord_4607353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4607361 : List Nat := [1, 2, 4, 3, 2, 2, 1, 2, 1, 3, 2]
def baseStart_4607361 : Nat := 118140960795 + 4607361 * 2 ^ 59
def prefixEnd_4607361 : Nat := 4983230072969 + 3 ^ 40 * 4607361 * 2
def baseEnd_4607361 : Nat := 2365790741779853412598639

theorem tailTrace_4607361 : CollatzResearch.WordTrace tailWord_4607361 prefixEnd_4607361 2365790741779853412598639 := by
  unfold tailWord_4607361
  simp only [CollatzResearch.WordTrace]
  refine ⟨168044261061325446457621937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112029507374216964305081291 168044261061325446457621937)
  ·
    refine ⟨126033195795994084843216453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 168044261061325446457621937 126033195795994084843216453)
    ·
      refine ⟨23631224211748890908103085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 126033195795994084843216453 23631224211748890908103085)
      ·
        refine ⟨8861709079405834090538657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23631224211748890908103085 8861709079405834090538657)
        ·
          refine ⟨6646281809554375567903993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8861709079405834090538657 6646281809554375567903993)
          ·
            refine ⟨4984711357165781675927995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6646281809554375567903993 4984711357165781675927995)
            ·
              refine ⟨7477067035748672513891993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4984711357165781675927995 7477067035748672513891993)
              ·
                refine ⟨5607800276811504385418995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7477067035748672513891993 5607800276811504385418995)
                ·
                  refine ⟨8411700415217256578128493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5607800276811504385418995 8411700415217256578128493)
                  ·
                    refine ⟨3154387655706471216798185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8411700415217256578128493 3154387655706471216798185)
                    ·
                      refine ⟨2365790741779853412598639, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3154387655706471216798185 2365790741779853412598639)
                      ·
                        rfl

theorem cell23_4607361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 2, 2, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 2, 2, 1, 2, 1, 3, 2].length) (baseStart_4607361 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4607361 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4607361 prefixEnd_4607361 := by exact prefixLift 4607361
  have htrace : WordTrace (prefixWord ++ tailWord_4607361) baseStart_4607361 baseEnd_4607361 := by
    simpa [prefixWord, tailWord_4607361, baseEnd_4607361] using wordTrace_append hprefix tailTrace_4607361
  have hstable : (prefixWord ++ tailWord_4607361).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4607361).length < 2 ^ (prefixWord ++ tailWord_4607361).sum := by decide
  have hdescent : baseEnd_4607361 < baseStart_4607361 := by decide
  rcases family_descends (prefixWord ++ tailWord_4607361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4607374 : List Nat := [4, 1, 1, 4, 2, 1, 1, 2, 1, 4, 2]
def baseStart_4607374 : Nat := 118140960795 + 4607374 * 2 ^ 59
def prefixEnd_4607374 : Nat := 4983230072969 + 3 ^ 40 * 4607374 * 2
def baseEnd_4607374 : Nat := 2365797417028361861736079

theorem tailTrace_4607374 : CollatzResearch.WordTrace tailWord_4607374 prefixEnd_4607374 2365797417028361861736079 := by
  unfold tailWord_4607374
  simp only [CollatzResearch.WordTrace]
  refine ⟨21005591901284793709730647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 112029823473518899785230117 21005591901284793709730647)
  ·
    refine ⟨31508387851927190564595971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21005591901284793709730647 31508387851927190564595971)
    ·
      refine ⟨47262581777890785846893957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31508387851927190564595971 47262581777890785846893957)
      ·
        refine ⟨8861734083354522346292617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 47262581777890785846893957 8861734083354522346292617)
        ·
          refine ⟨6646300562515891759719463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8861734083354522346292617 6646300562515891759719463)
          ·
            refine ⟨9969450843773837639579195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6646300562515891759719463 9969450843773837639579195)
            ·
              refine ⟨14954176265660756459368793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9969450843773837639579195 14954176265660756459368793)
              ·
                refine ⟨11215632199245567344526595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14954176265660756459368793 11215632199245567344526595)
                ·
                  refine ⟨16823448298868351016789893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11215632199245567344526595 16823448298868351016789893)
                  ·
                    refine ⟨3154396556037815815648105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16823448298868351016789893 3154396556037815815648105)
                    ·
                      refine ⟨2365797417028361861736079, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3154396556037815815648105 2365797417028361861736079)
                      ·
                        rfl

theorem cell23_4607374_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 2, 1, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 2, 1, 1, 2, 1, 4, 2].length) (baseStart_4607374 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4607374 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4607374 prefixEnd_4607374 := by exact prefixLift 4607374
  have htrace : WordTrace (prefixWord ++ tailWord_4607374) baseStart_4607374 baseEnd_4607374 := by
    simpa [prefixWord, tailWord_4607374, baseEnd_4607374] using wordTrace_append hprefix tailTrace_4607374
  have hstable : (prefixWord ++ tailWord_4607374).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4607374).length < 2 ^ (prefixWord ++ tailWord_4607374).sum := by decide
  have hdescent : baseEnd_4607374 < baseStart_4607374 := by decide
  rcases family_descends (prefixWord ++ tailWord_4607374) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4607378 : List Nat := [3, 2, 3, 3, 1, 1, 3, 1, 1, 3, 2]
def baseStart_4607378 : Nat := 118140960795 + 4607378 * 2 ^ 59
def prefixEnd_4607378 : Nat := 4983230072969 + 3 ^ 40 * 4607378 * 2
def baseEnd_4607378 : Nat := 2365799470950979846086061

theorem tailTrace_4607378 : CollatzResearch.WordTrace tailWord_4607378 prefixEnd_4607378 2365799470950979846086061 := by
  unfold tailWord_4607378
  simp only [CollatzResearch.WordTrace]
  refine ⟨42011220275565964590247697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 112029920734842572240660525 42011220275565964590247697)
  ·
    refine ⟨31508415206674473442685773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42011220275565964590247697 31508415206674473442685773)
    ·
      refine ⟨11815655702502927541007165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31508415206674473442685773 11815655702502927541007165)
      ·
        refine ⟨4430870888438597827877687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11815655702502927541007165 4430870888438597827877687)
        ·
          refine ⟨6646306332657896741816531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4430870888438597827877687 6646306332657896741816531)
          ·
            refine ⟨9969459498986845112724797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6646306332657896741816531 9969459498986845112724797)
            ·
              refine ⟨3738547312120066917271799, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9969459498986845112724797 3738547312120066917271799)
              ·
                refine ⟨5607820968180100375907699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3738547312120066917271799 5607820968180100375907699)
                ·
                  refine ⟨8411731452270150563861549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5607820968180100375907699 8411731452270150563861549)
                  ·
                    refine ⟨3154399294601306461448081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8411731452270150563861549 3154399294601306461448081)
                    ·
                      refine ⟨2365799470950979846086061, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3154399294601306461448081 2365799470950979846086061)
                      ·
                        rfl

theorem cell23_4607378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 1, 1, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 1, 1, 3, 1, 1, 3, 2].length) (baseStart_4607378 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4607378 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4607378 prefixEnd_4607378 := by exact prefixLift 4607378
  have htrace : WordTrace (prefixWord ++ tailWord_4607378) baseStart_4607378 baseEnd_4607378 := by
    simpa [prefixWord, tailWord_4607378, baseEnd_4607378] using wordTrace_append hprefix tailTrace_4607378
  have hstable : (prefixWord ++ tailWord_4607378).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4607378).length < 2 ^ (prefixWord ++ tailWord_4607378).sum := by decide
  have hdescent : baseEnd_4607378 < baseStart_4607378 := by decide
  rcases family_descends (prefixWord ++ tailWord_4607378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4607457 : List Nat := [1, 2, 3, 1, 2, 4, 2, 1, 3, 4]
def baseStart_4607457 : Nat := 118140960795 + 4607457 * 2 ^ 59
def prefixEnd_4607457 : Nat := 4983230072969 + 3 ^ 40 * 4607457 * 2
def baseEnd_4607457 : Nat := 788613345307561678999399

theorem tailTrace_4607457 : CollatzResearch.WordTrace tailWord_4607457 prefixEnd_4607457 788613345307561678999399 := by
  unfold tailWord_4607457
  simp only [CollatzResearch.WordTrace]
  refine ⟨168047762468977654853116625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112031841645985103235411083 168047762468977654853116625)
  ·
    refine ⟨126035821851733241139837469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 168047762468977654853116625 126035821851733241139837469)
    ·
      refine ⟨47263433194399965427439051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 126035821851733241139837469 47263433194399965427439051)
      ·
        refine ⟨70895149791599948141158577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47263433194399965427439051 70895149791599948141158577)
        ·
          refine ⟨53171362343699961105868933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 70895149791599948141158577 53171362343699961105868933)
          ·
            refine ⟨9969630439443742707350425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 53171362343699961105868933 9969630439443742707350425)
            ·
              refine ⟨7477222829582807030512819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9969630439443742707350425 7477222829582807030512819)
              ·
                refine ⟨11215834244374210545769229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7477222829582807030512819 11215834244374210545769229)
                ·
                  refine ⟨4205937841640328954663461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11215834244374210545769229 4205937841640328954663461)
                  ·
                    refine ⟨788613345307561678999399, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4205937841640328954663461 788613345307561678999399)
                    ·
                      rfl

theorem cell23_4607457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 4, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 4, 2, 1, 3, 4].length) (baseStart_4607457 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4607457 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4607457 prefixEnd_4607457 := by exact prefixLift 4607457
  have htrace : WordTrace (prefixWord ++ tailWord_4607457) baseStart_4607457 baseEnd_4607457 := by
    simpa [prefixWord, tailWord_4607457, baseEnd_4607457] using wordTrace_append hprefix tailTrace_4607457
  have hstable : (prefixWord ++ tailWord_4607457).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4607457).length < 2 ^ (prefixWord ++ tailWord_4607457).sum := by decide
  have hdescent : baseEnd_4607457 < baseStart_4607457 := by decide
  rcases family_descends (prefixWord ++ tailWord_4607457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4607507 : List Nat := [1, 1, 1, 2, 1, 6, 1, 1, 4, 3, 2]
def baseStart_4607507 : Nat := 118140960795 + 4607507 * 2 ^ 59
def prefixEnd_4607507 : Nat := 4983230072969 + 3 ^ 40 * 4607507 * 2
def baseEnd_4607507 : Nat := 2365865709955409841372967

theorem tailTrace_4607507 : CollatzResearch.WordTrace tailWord_4607507 prefixEnd_4607507 2365865709955409841372967 := by
  unfold tailWord_4607507
  simp only [CollatzResearch.WordTrace]
  refine ⟨168049586118796513392436775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112033057412531008928291183 168049586118796513392436775)
  ·
    refine ⟨252074379178194770088655163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 168049586118796513392436775 252074379178194770088655163)
    ·
      refine ⟨378111568767292155132982745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 252074379178194770088655163 378111568767292155132982745)
      ·
        refine ⟨283583676575469116349737059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 378111568767292155132982745 283583676575469116349737059)
        ·
          refine ⟨425375514863203674524605589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 283583676575469116349737059 425375514863203674524605589)
          ·
            refine ⟨19939477259212672243340887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 425375514863203674524605589 19939477259212672243340887)
            ·
              refine ⟨29909215888819008365011331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19939477259212672243340887 29909215888819008365011331)
              ·
                refine ⟨44863823833228512547516997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29909215888819008365011331 44863823833228512547516997)
                ·
                  refine ⟨8411966968730346102659437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 44863823833228512547516997 8411966968730346102659437)
                  ·
                    refine ⟨3154487613273879788497289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8411966968730346102659437 3154487613273879788497289)
                    ·
                      refine ⟨2365865709955409841372967, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3154487613273879788497289 2365865709955409841372967)
                      ·
                        rfl

theorem cell23_4607507_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 1, 1, 4, 3, 2].length) (baseStart_4607507 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4607507 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4607507 prefixEnd_4607507 := by exact prefixLift 4607507
  have htrace : WordTrace (prefixWord ++ tailWord_4607507) baseStart_4607507 baseEnd_4607507 := by
    simpa [prefixWord, tailWord_4607507, baseEnd_4607507] using wordTrace_append hprefix tailTrace_4607507
  have hstable : (prefixWord ++ tailWord_4607507).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4607507).length < 2 ^ (prefixWord ++ tailWord_4607507).sum := by decide
  have hdescent : baseEnd_4607507 < baseStart_4607507 := by decide
  rcases family_descends (prefixWord ++ tailWord_4607507) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4607508 : List Nat := [2, 4, 3, 1, 3, 1, 1, 1, 3, 4]
def baseStart_4607508 : Nat := 118140960795 + 4607508 * 2 ^ 59
def prefixEnd_4607508 : Nat := 4983230072969 + 3 ^ 40 * 4607508 * 2
def baseEnd_4607508 : Nat := 788622074478688112486821

theorem tailTrace_4607508 : CollatzResearch.WordTrace tailWord_4607508 prefixEnd_4607508 788622074478688112486821 := by
  unfold tailWord_4607508
  simp only [CollatzResearch.WordTrace]
  refine ⟨84024811295896445281611589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 112033081727861927042148785 84024811295896445281611589)
  ·
    refine ⟨15754652117980583490302173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 84024811295896445281611589 15754652117980583490302173)
    ·
      refine ⟨5907994544242718808863315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15754652117980583490302173 5907994544242718808863315)
      ·
        refine ⟨8861991816364078213294973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5907994544242718808863315 8861991816364078213294973)
        ·
          refine ⟨3323246931136529329985615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8861991816364078213294973 3323246931136529329985615)
          ·
            refine ⟨4984870396704793994978423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3323246931136529329985615 4984870396704793994978423)
            ·
              refine ⟨7477305595057190992467635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4984870396704793994978423 7477305595057190992467635)
              ·
                refine ⟨11215958392585786488701453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7477305595057190992467635 11215958392585786488701453)
                ·
                  refine ⟨4205984397219669933263045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11215958392585786488701453 4205984397219669933263045)
                  ·
                    refine ⟨788622074478688112486821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4205984397219669933263045 788622074478688112486821)
                    ·
                      rfl

theorem cell23_4607508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 3, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 3, 1, 1, 1, 3, 4].length) (baseStart_4607508 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4607508 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4607508 prefixEnd_4607508 := by exact prefixLift 4607508
  have htrace : WordTrace (prefixWord ++ tailWord_4607508) baseStart_4607508 baseEnd_4607508 := by
    simpa [prefixWord, tailWord_4607508, baseEnd_4607508] using wordTrace_append hprefix tailTrace_4607508
  have hstable : (prefixWord ++ tailWord_4607508).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4607508).length < 2 ^ (prefixWord ++ tailWord_4607508).sum := by decide
  have hdescent : baseEnd_4607508 < baseStart_4607508 := by decide
  rcases family_descends (prefixWord ++ tailWord_4607508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4607513 : List Nat := [1, 2, 1, 2, 1, 1, 2, 1, 2, 10]
def baseStart_4607513 : Nat := 118140960795 + 4607513 * 2 ^ 59
def prefixEnd_4607513 : Nat := 4983230072969 + 3 ^ 40 * 4607513 * 2
def baseEnd_4607513 : Nat := 788622930279778939299313

theorem tailTrace_4607513 : CollatzResearch.WordTrace tailWord_4607513 prefixEnd_4607513 788622930279778939299313 := by
  unfold tailWord_4607513
  simp only [CollatzResearch.WordTrace]
  refine ⟨168049804956774776417155193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112033203304516517611436795 168049804956774776417155193)
  ·
    refine ⟨126037353717581082312866395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 168049804956774776417155193 126037353717581082312866395)
    ·
      refine ⟨189056030576371623469299593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 126037353717581082312866395 189056030576371623469299593)
      ·
        refine ⟨141792022932278717601974695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 189056030576371623469299593 141792022932278717601974695)
        ·
          refine ⟨212688034398418076402962043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 141792022932278717601974695 212688034398418076402962043)
          ·
            refine ⟨319032051597627114604443065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 212688034398418076402962043 319032051597627114604443065)
            ·
              refine ⟨239274038698220335953332299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 319032051597627114604443065 239274038698220335953332299)
              ·
                refine ⟨358911058047330503929998449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 239274038698220335953332299 358911058047330503929998449)
                ·
                  refine ⟨269183293535497877947498837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 358911058047330503929998449 269183293535497877947498837)
                  ·
                    refine ⟨788622930279778939299313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 269183293535497877947498837 788622930279778939299313)
                    ·
                      rfl

theorem cell23_4607513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 1, 2, 10].length) (baseStart_4607513 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4607513 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4607513 prefixEnd_4607513 := by exact prefixLift 4607513
  have htrace : WordTrace (prefixWord ++ tailWord_4607513) baseStart_4607513 baseEnd_4607513 := by
    simpa [prefixWord, tailWord_4607513, baseEnd_4607513] using wordTrace_append hprefix tailTrace_4607513
  have hstable : (prefixWord ++ tailWord_4607513).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4607513).length < 2 ^ (prefixWord ++ tailWord_4607513).sum := by decide
  have hdescent : baseEnd_4607513 < baseStart_4607513 := by decide
  rcases family_descends (prefixWord ++ tailWord_4607513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4607534 : List Nat := [4, 1, 3, 1, 2, 1, 3, 2, 1, 5]
def baseStart_4607534 : Nat := 118140960795 + 4607534 * 2 ^ 59
def prefixEnd_4607534 : Nat := 4983230072969 + 3 ^ 40 * 4607534 * 2
def baseEnd_4607534 : Nat := 788626524644360411911781

theorem tailTrace_4607534 : CollatzResearch.WordTrace tailWord_4607534 prefixEnd_4607534 788626524644360411911781 := by
  unfold tailWord_4607534
  simp only [CollatzResearch.WordTrace]
  refine ⟨21006321361212337125458707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 112033713926465798002446437 21006321361212337125458707)
  ·
    refine ⟨31509482041818505688188061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21006321361212337125458707 31509482041818505688188061)
    ·
      refine ⟨11816055765681939633070523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31509482041818505688188061 11816055765681939633070523)
      ·
        refine ⟨17724083648522909449605785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11816055765681939633070523 17724083648522909449605785)
        ·
          refine ⟨13293062736392182087204339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17724083648522909449605785 13293062736392182087204339)
          ·
            refine ⟨19939594104588273130806509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13293062736392182087204339 19939594104588273130806509)
            ·
              refine ⟨7477347789220602424052441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19939594104588273130806509 7477347789220602424052441)
              ·
                refine ⟨5608010841915451818039331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7477347789220602424052441 5608010841915451818039331)
                ·
                  refine ⟨8412016262873177727058997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5608010841915451818039331 8412016262873177727058997)
                  ·
                    refine ⟨788626524644360411911781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8412016262873177727058997 788626524644360411911781)
                    ·
                      rfl

theorem cell23_4607534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 3, 2, 1, 5].length) (baseStart_4607534 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4607534 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4607534 prefixEnd_4607534 := by exact prefixLift 4607534
  have htrace : WordTrace (prefixWord ++ tailWord_4607534) baseStart_4607534 baseEnd_4607534 := by
    simpa [prefixWord, tailWord_4607534, baseEnd_4607534] using wordTrace_append hprefix tailTrace_4607534
  have hstable : (prefixWord ++ tailWord_4607534).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4607534).length < 2 ^ (prefixWord ++ tailWord_4607534).sum := by decide
  have hdescent : baseEnd_4607534 < baseStart_4607534 := by decide
  rcases family_descends (prefixWord ++ tailWord_4607534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4607564 : List Nat := [2, 2, 1, 3, 1, 4, 2, 2, 2, 4]
def baseStart_4607564 : Nat := 118140960795 + 4607564 * 2 ^ 59
def prefixEnd_4607564 : Nat := 4983230072969 + 3 ^ 40 * 4607564 * 2
def baseEnd_4607564 : Nat := 788631659450905372786735

theorem tailTrace_4607564 : CollatzResearch.WordTrace tailWord_4607564 prefixEnd_4607564 788631659450905372786735 := by
  unfold tailWord_4607564
  simp only [CollatzResearch.WordTrace]
  refine ⟨84025832539795006063630873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 112034443386393341418174497 84025832539795006063630873)
  ·
    refine ⟨63019374404846254547723155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 84025832539795006063630873 63019374404846254547723155)
    ·
      refine ⟨94529061607269381821584733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63019374404846254547723155 94529061607269381821584733)
      ·
        refine ⟨35448398102726018183094275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 94529061607269381821584733 35448398102726018183094275)
        ·
          refine ⟨53172597154089027274641413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35448398102726018183094275 53172597154089027274641413)
          ·
            refine ⟨9969861966391692613995265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 53172597154089027274641413 9969861966391692613995265)
            ·
              refine ⟨7477396474793769460496449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9969861966391692613995265 7477396474793769460496449)
              ·
                refine ⟨5608047356095327095372337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7477396474793769460496449 5608047356095327095372337)
                ·
                  refine ⟨4206035517071495321529253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5608047356095327095372337 4206035517071495321529253)
                  ·
                    refine ⟨788631659450905372786735, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4206035517071495321529253 788631659450905372786735)
                    ·
                      rfl

theorem cell23_4607564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 4, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 4, 2, 2, 2, 4].length) (baseStart_4607564 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4607564 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4607564 prefixEnd_4607564 := by exact prefixLift 4607564
  have htrace : WordTrace (prefixWord ++ tailWord_4607564) baseStart_4607564 baseEnd_4607564 := by
    simpa [prefixWord, tailWord_4607564, baseEnd_4607564] using wordTrace_append hprefix tailTrace_4607564
  have hstable : (prefixWord ++ tailWord_4607564).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4607564).length < 2 ^ (prefixWord ++ tailWord_4607564).sum := by decide
  have hdescent : baseEnd_4607564 < baseStart_4607564 := by decide
  rcases family_descends (prefixWord ++ tailWord_4607564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4607581 : List Nat := [1, 4, 4, 2, 1, 1, 2, 1, 1, 6]
def baseStart_4607581 : Nat := 118140960795 + 4607581 * 2 ^ 59
def prefixEnd_4607581 : Nat := 4983230072969 + 3 ^ 40 * 4607581 * 2
def baseEnd_4607581 : Nat := 788634569174614183949209

theorem tailTrace_4607581 : CollatzResearch.WordTrace tailWord_4607581 prefixEnd_4607581 788634569174614183949209 := by
  unfold tailWord_4607581
  simp only [CollatzResearch.WordTrace]
  refine ⟨168052285120528424030630597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112034856747018949353753731 168052285120528424030630597)
  ·
    refine ⟨31509803460099079505743237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 168052285120528424030630597 31509803460099079505743237)
    ·
      refine ⟨5908088148768577407326857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 31509803460099079505743237 5908088148768577407326857)
      ·
        refine ⟨4431066111576433055495143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5908088148768577407326857 4431066111576433055495143)
        ·
          refine ⟨6646599167364649583242715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4431066111576433055495143 6646599167364649583242715)
          ·
            refine ⟨9969898751046974374864073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6646599167364649583242715 9969898751046974374864073)
            ·
              refine ⟨7477424063285230781148055, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9969898751046974374864073 7477424063285230781148055)
              ·
                refine ⟨11216136094927846171722083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7477424063285230781148055 11216136094927846171722083)
                ·
                  refine ⟨16824204142391769257583125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11216136094927846171722083 16824204142391769257583125)
                  ·
                    refine ⟨788634569174614183949209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16824204142391769257583125 788634569174614183949209)
                    ·
                      rfl

theorem cell23_4607581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 1, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 1, 1, 2, 1, 1, 6].length) (baseStart_4607581 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4607581 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4607581 prefixEnd_4607581 := by exact prefixLift 4607581
  have htrace : WordTrace (prefixWord ++ tailWord_4607581) baseStart_4607581 baseEnd_4607581 := by
    simpa [prefixWord, tailWord_4607581, baseEnd_4607581] using wordTrace_append hprefix tailTrace_4607581
  have hstable : (prefixWord ++ tailWord_4607581).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4607581).length < 2 ^ (prefixWord ++ tailWord_4607581).sum := by decide
  have hdescent : baseEnd_4607581 < baseStart_4607581 := by decide
  rcases family_descends (prefixWord ++ tailWord_4607581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4607587 : List Nat := [1, 1, 1, 5, 1, 3, 1, 3, 1, 3, 3]
def baseStart_4607587 : Nat := 118140960795 + 4607587 * 2 ^ 59
def prefixEnd_4607587 : Nat := 4983230072969 + 3 ^ 40 * 4607587 * 2
def baseEnd_4607587 : Nat := 2365906788407769528372599

theorem tailTrace_4607587 : CollatzResearch.WordTrace tailWord_4607587 prefixEnd_4607587 2365906788407769528372599 := by
  unfold tailWord_4607587
  simp only [CollatzResearch.WordTrace]
  refine ⟨168052503958506687055349015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112035002639004458036899343 168052503958506687055349015)
  ·
    refine ⟨252078755937760030583023523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 168052503958506687055349015 252078755937760030583023523)
    ·
      refine ⟨378118133906640045874535285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 252078755937760030583023523 378118133906640045874535285)
      ·
        refine ⟨35448575053747504300737683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 378118133906640045874535285 35448575053747504300737683)
        ·
          refine ⟨53172862580621256451106525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35448575053747504300737683 53172862580621256451106525)
          ·
            refine ⟨19939823467732971169164947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 53172862580621256451106525 19939823467732971169164947)
            ·
              refine ⟨29909735201599456753747421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19939823467732971169164947 29909735201599456753747421)
              ·
                refine ⟨11216150700599796282655283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 29909735201599456753747421 11216150700599796282655283)
                ·
                  refine ⟨16824226050899694423982925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11216150700599796282655283 16824226050899694423982925)
                  ·
                    refine ⟨6309084769087385408993597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16824226050899694423982925 6309084769087385408993597)
                    ·
                      refine ⟨2365906788407769528372599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6309084769087385408993597 2365906788407769528372599)
                      ·
                        rfl

theorem cell23_4607587_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 1, 3, 1, 3, 3].length) (baseStart_4607587 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4607587 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4607587 prefixEnd_4607587 := by exact prefixLift 4607587
  have htrace : WordTrace (prefixWord ++ tailWord_4607587) baseStart_4607587 baseEnd_4607587 := by
    simpa [prefixWord, tailWord_4607587, baseEnd_4607587] using wordTrace_append hprefix tailTrace_4607587
  have hstable : (prefixWord ++ tailWord_4607587).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4607587).length < 2 ^ (prefixWord ++ tailWord_4607587).sum := by decide
  have hdescent : baseEnd_4607587 < baseStart_4607587 := by decide
  rcases family_descends (prefixWord ++ tailWord_4607587) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4607605 : List Nat := [1, 3, 4, 2, 1, 2, 2, 3, 1, 2, 2]
def baseStart_4607605 : Nat := 118140960795 + 4607605 * 2 ^ 59
def prefixEnd_4607605 : Nat := 4983230072969 + 3 ^ 40 * 4607605 * 2
def baseEnd_4607605 : Nat := 2365916031059550457947517

theorem tailTrace_4607605 : CollatzResearch.WordTrace tailWord_4607605 prefixEnd_4607605 2365916031059550457947517 := by
  unfold tailWord_4607605
  simp only [CollatzResearch.WordTrace]
  refine ⟨168053160472441476129504269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112035440314960984086336179 168053160472441476129504269)
  ·
    refine ⟨63019935177165553548564101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 168053160472441476129504269 63019935177165553548564101)
    ·
      refine ⟨11816237845718541290355769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 63019935177165553548564101 11816237845718541290355769)
      ·
        refine ⟨8862178384288905967766827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11816237845718541290355769 8862178384288905967766827)
        ·
          refine ⟨13293267576433358951650241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8862178384288905967766827 13293267576433358951650241)
          ·
            refine ⟨9969950682325019213737681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13293267576433358951650241 9969950682325019213737681)
            ·
              refine ⟨7477463011743764410303261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9969950682325019213737681 7477463011743764410303261)
              ·
                refine ⟨2804048629403911653863723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7477463011743764410303261 2804048629403911653863723)
                ·
                  refine ⟨4206072944105867480795585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2804048629403911653863723 4206072944105867480795585)
                  ·
                    refine ⟨3154554708079400610596689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4206072944105867480795585 3154554708079400610596689)
                    ·
                      refine ⟨2365916031059550457947517, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3154554708079400610596689 2365916031059550457947517)
                      ·
                        rfl

theorem cell23_4607605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 2, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 2, 2, 3, 1, 2, 2].length) (baseStart_4607605 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4607605 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4607605 prefixEnd_4607605 := by exact prefixLift 4607605
  have htrace : WordTrace (prefixWord ++ tailWord_4607605) baseStart_4607605 baseEnd_4607605 := by
    simpa [prefixWord, tailWord_4607605, baseEnd_4607605] using wordTrace_append hprefix tailTrace_4607605
  have hstable : (prefixWord ++ tailWord_4607605).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4607605).length < 2 ^ (prefixWord ++ tailWord_4607605).sum := by decide
  have hdescent : baseEnd_4607605 < baseStart_4607605 := by decide
  rcases family_descends (prefixWord ++ tailWord_4607605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4607610 : List Nat := [3, 1, 1, 1, 1, 1, 1, 4, 1, 5, 4]
def baseStart_4607610 : Nat := 118140960795 + 4607610 * 2 ^ 59
def prefixEnd_4607610 : Nat := 4983230072969 + 3 ^ 40 * 4607610 * 2
def baseEnd_4607610 : Nat := 2365918598462822938384993

theorem tailTrace_4607610 : CollatzResearch.WordTrace tailWord_4607610 prefixEnd_4607610 2365918598462822938384993 := by
  unfold tailWord_4607610
  simp only [CollatzResearch.WordTrace]
  refine ⟨42013335709355840495859071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 112035561891615574655624189 42013335709355840495859071)
  ·
    refine ⟨63020003564033760743788607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42013335709355840495859071 63020003564033760743788607)
    ·
      refine ⟨94530005346050641115682911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63020003564033760743788607 94530005346050641115682911)
      ·
        refine ⟨141795008019075961673524367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 94530005346050641115682911 141795008019075961673524367)
        ·
          refine ⟨212692512028613942510286551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 141795008019075961673524367 212692512028613942510286551)
          ·
            refine ⟨319038768042920913765429827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 212692512028613942510286551 319038768042920913765429827)
            ·
              refine ⟨478558152064381370648144741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 319038768042920913765429827 478558152064381370648144741)
              ·
                refine ⟨89729653512071506996527139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 478558152064381370648144741 89729653512071506996527139)
                ·
                  refine ⟨134594480268107260494790709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 89729653512071506996527139 134594480268107260494790709)
                  ·
                    refine ⟨12618232525135055671386629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 134594480268107260494790709 12618232525135055671386629)
                    ·
                      refine ⟨2365918598462822938384993, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12618232525135055671386629 2365918598462822938384993)
                      ·
                        rfl

theorem cell23_4607610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 4, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 4, 1, 5, 4].length) (baseStart_4607610 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4607610 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4607610 prefixEnd_4607610 := by exact prefixLift 4607610
  have htrace : WordTrace (prefixWord ++ tailWord_4607610) baseStart_4607610 baseEnd_4607610 := by
    simpa [prefixWord, tailWord_4607610, baseEnd_4607610] using wordTrace_append hprefix tailTrace_4607610
  have hstable : (prefixWord ++ tailWord_4607610).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4607610).length < 2 ^ (prefixWord ++ tailWord_4607610).sum := by decide
  have hdescent : baseEnd_4607610 < baseStart_4607610 := by decide
  rcases family_descends (prefixWord ++ tailWord_4607610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4607656 : List Nat := [2, 1, 7, 1, 2, 1, 1, 3, 1, 2, 2]
def baseStart_4607656 : Nat := 118140960795 + 4607656 * 2 ^ 59
def prefixEnd_4607656 : Nat := 4983230072969 + 3 ^ 40 * 4607656 * 2
def baseEnd_4607656 : Nat := 2365942218572929758409783

theorem tailTrace_4607656 : CollatzResearch.WordTrace tailWord_4607656 prefixEnd_4607656 2365942218572929758409783 := by
  unfold tailWord_4607656
  simp only [CollatzResearch.WordTrace]
  refine ⟨84027510297628355919805411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 112036680396837807893073881 84027510297628355919805411)
  ·
    refine ⟨126041265446442533879708117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84027510297628355919805411 126041265446442533879708117)
    ·
      refine ⟨2954092158900996887805659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 126041265446442533879708117 2954092158900996887805659)
      ·
        refine ⟨4431138238351495331708489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2954092158900996887805659 4431138238351495331708489)
        ·
          refine ⟨3323353678763621498781367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4431138238351495331708489 3323353678763621498781367)
          ·
            refine ⟨4985030518145432248172051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3323353678763621498781367 4985030518145432248172051)
            ·
              refine ⟨7477545777218148372258077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4985030518145432248172051 7477545777218148372258077)
              ·
                refine ⟨2804079666456805639596779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7477545777218148372258077 2804079666456805639596779)
                ·
                  refine ⟨4206119499685208459395169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2804079666456805639596779 4206119499685208459395169)
                  ·
                    refine ⟨3154589624763906344546377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4206119499685208459395169 3154589624763906344546377)
                    ·
                      refine ⟨2365942218572929758409783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3154589624763906344546377 2365942218572929758409783)
                      ·
                        rfl

theorem cell23_4607656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 2, 1, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 2, 1, 1, 3, 1, 2, 2].length) (baseStart_4607656 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4607656 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4607656 prefixEnd_4607656 := by exact prefixLift 4607656
  have htrace : WordTrace (prefixWord ++ tailWord_4607656) baseStart_4607656 baseEnd_4607656 := by
    simpa [prefixWord, tailWord_4607656, baseEnd_4607656] using wordTrace_append hprefix tailTrace_4607656
  have hstable : (prefixWord ++ tailWord_4607656).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4607656).length < 2 ^ (prefixWord ++ tailWord_4607656).sum := by decide
  have hdescent : baseEnd_4607656 < baseStart_4607656 := by decide
  rcases family_descends (prefixWord ++ tailWord_4607656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4607661 : List Nat := [1, 5, 2, 1, 1, 1, 1, 1, 6, 2, 2]
def baseStart_4607661 : Nat := 118140960795 + 4607661 * 2 ^ 59
def prefixEnd_4607661 : Nat := 4983230072969 + 3 ^ 40 * 4607661 * 2
def baseEnd_4607661 : Nat := 2365944785976202238847259

theorem tailTrace_4607661 : CollatzResearch.WordTrace tailWord_4607661 prefixEnd_4607661 2365944785976202238847259 := by
  unfold tailWord_4607661
  simp only [CollatzResearch.WordTrace]
  refine ⟨168055202960238597693542837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112036801973492398462361891 168055202960238597693542837)
  ·
    refine ⟨15755175277522368533769641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 168055202960238597693542837 15755175277522368533769641)
    ·
      refine ⟨11816381458141776400327231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15755175277522368533769641 11816381458141776400327231)
      ·
        refine ⟨17724572187212664600490847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11816381458141776400327231 17724572187212664600490847)
        ·
          refine ⟨26586858280818996900736271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17724572187212664600490847 26586858280818996900736271)
          ·
            refine ⟨39880287421228495351104407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26586858280818996900736271 39880287421228495351104407)
            ·
              refine ⟨59820431131842743026656611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39880287421228495351104407 59820431131842743026656611)
              ·
                refine ⟨89730646697764114539984917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 59820431131842743026656611 89730646697764114539984917)
                ·
                  refine ⟨4206124063957692869061793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 89730646697764114539984917 4206124063957692869061793)
                  ·
                    refine ⟨3154593047968269651796345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4206124063957692869061793 3154593047968269651796345)
                    ·
                      refine ⟨2365944785976202238847259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3154593047968269651796345 2365944785976202238847259)
                      ·
                        rfl

theorem cell23_4607661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 1, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 1, 1, 6, 2, 2].length) (baseStart_4607661 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4607661 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4607661 prefixEnd_4607661 := by exact prefixLift 4607661
  have htrace : WordTrace (prefixWord ++ tailWord_4607661) baseStart_4607661 baseEnd_4607661 := by
    simpa [prefixWord, tailWord_4607661, baseEnd_4607661] using wordTrace_append hprefix tailTrace_4607661
  have hstable : (prefixWord ++ tailWord_4607661).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4607661).length < 2 ^ (prefixWord ++ tailWord_4607661).sum := by decide
  have hdescent : baseEnd_4607661 < baseStart_4607661 := by decide
  rcases family_descends (prefixWord ++ tailWord_4607661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4607737 : List Nat := [1, 2, 1, 3, 1, 1, 1, 1, 5, 4, 3]
def baseStart_4607737 : Nat := 118140960795 + 4607737 * 2 ^ 59
def prefixEnd_4607737 : Nat := 4983230072969 + 3 ^ 40 * 4607737 * 2
def baseEnd_4607737 : Nat := 2365983810505943941496909

theorem tailTrace_4607737 : CollatzResearch.WordTrace tailWord_4607737 prefixEnd_4607737 2365983810505943941496909 := by
  unfold tailWord_4607737
  simp only [CollatzResearch.WordTrace]
  refine ⟨168057974907963262673309465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112038649938642175115539643 168057974907963262673309465)
  ·
    refine ⟨126043481180972447004982099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 168057974907963262673309465 126043481180972447004982099)
    ·
      refine ⟨189065221771458670507473149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 126043481180972447004982099 189065221771458670507473149)
      ·
        refine ⟨70899458164297001440302431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 189065221771458670507473149 70899458164297001440302431)
        ·
          refine ⟨106349187246445502160453647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 70899458164297001440302431 106349187246445502160453647)
          ·
            refine ⟨159523780869668253240680471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 106349187246445502160453647 159523780869668253240680471)
            ·
              refine ⟨239285671304502379861020707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 159523780869668253240680471 239285671304502379861020707)
              ·
                refine ⟨358928506956753569791531061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 239285671304502379861020707 358928506956753569791531061)
                ·
                  refine ⟨33649547527195647167956037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 358928506956753569791531061 33649547527195647167956037)
                  ·
                    refine ⟨6309290161349183843991757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 33649547527195647167956037 6309290161349183843991757)
                    ·
                      refine ⟨2365983810505943941496909, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6309290161349183843991757 2365983810505943941496909)
                      ·
                        rfl

theorem cell23_4607737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 1, 5, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 1, 5, 4, 3].length) (baseStart_4607737 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4607737 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4607737 prefixEnd_4607737 := by exact prefixLift 4607737
  have htrace : WordTrace (prefixWord ++ tailWord_4607737) baseStart_4607737 baseEnd_4607737 := by
    simpa [prefixWord, tailWord_4607737, baseEnd_4607737] using wordTrace_append hprefix tailTrace_4607737
  have hstable : (prefixWord ++ tailWord_4607737).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4607737).length < 2 ^ (prefixWord ++ tailWord_4607737).sum := by decide
  have hdescent : baseEnd_4607737 < baseStart_4607737 := by decide
  rcases family_descends (prefixWord ++ tailWord_4607737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4607778 : List Nat := [3, 3, 1, 1, 2, 1, 4, 3, 1, 4]
def baseStart_4607778 : Nat := 118140960795 + 4607778 * 2 ^ 59
def prefixEnd_4607778 : Nat := 4983230072969 + 3 ^ 40 * 4607778 * 2
def baseEnd_4607778 : Nat := 788668287737592760361407

theorem tailTrace_4607778 : CollatzResearch.WordTrace tailWord_4607778 prefixEnd_4607778 788668287737592760361407 := by
  unfold tailWord_4607778
  simp only [CollatzResearch.WordTrace]
  refine ⟨42014867575203681668887997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 112039646867209817783701325 42014867575203681668887997)
  ·
    refine ⟨15755575340701380625832999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 42014867575203681668887997 15755575340701380625832999)
    ·
      refine ⟨23633363011052070938749499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15755575340701380625832999 23633363011052070938749499)
      ·
        refine ⟨35450044516578106408124249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23633363011052070938749499 35450044516578106408124249)
        ·
          refine ⟨26587533387433579806093187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35450044516578106408124249 26587533387433579806093187)
          ·
            refine ⟨39881300081150369709139781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26587533387433579806093187 39881300081150369709139781)
            ·
              refine ⟨7477743765215694320463709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 39881300081150369709139781 7477743765215694320463709)
              ·
                refine ⟨2804153911955885370173891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7477743765215694320463709 2804153911955885370173891)
                ·
                  refine ⟨4206230867933828055260837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2804153911955885370173891 4206230867933828055260837)
                  ·
                    refine ⟨788668287737592760361407, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4206230867933828055260837 788668287737592760361407)
                    ·
                      rfl

theorem cell23_4607778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 4, 3, 1, 4].length) (baseStart_4607778 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4607778 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4607778 prefixEnd_4607778 := by exact prefixLift 4607778
  have htrace : WordTrace (prefixWord ++ tailWord_4607778) baseStart_4607778 baseEnd_4607778 := by
    simpa [prefixWord, tailWord_4607778, baseEnd_4607778] using wordTrace_append hprefix tailTrace_4607778
  have hstable : (prefixWord ++ tailWord_4607778).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4607778).length < 2 ^ (prefixWord ++ tailWord_4607778).sum := by decide
  have hdescent : baseEnd_4607778 < baseStart_4607778 := by decide
  rcases family_descends (prefixWord ++ tailWord_4607778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4607824 : List Nat := [2, 1, 1, 1, 1, 4, 1, 1, 1, 8, 2]
def baseStart_4607824 : Nat := 118140960795 + 4607824 * 2 ^ 59
def prefixEnd_4607824 : Nat := 4983230072969 + 3 ^ 40 * 4607824 * 2
def baseEnd_4607824 : Nat := 2366028483322885101109009

theorem tailTrace_4607824 : CollatzResearch.WordTrace tailWord_4607824 prefixEnd_4607824 2366028483322885101109009 := by
  unfold tailWord_4607824
  simp only [CollatzResearch.WordTrace]
  refine ⟨84030574029324038265863263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 112040765372432051021151017 84030574029324038265863263)
  ·
    refine ⟨126045861043986057398794895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84030574029324038265863263 126045861043986057398794895)
    ·
      refine ⟨189068791565979086098192343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 126045861043986057398794895 189068791565979086098192343)
      ·
        refine ⟨283603187348968629147288515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 189068791565979086098192343 283603187348968629147288515)
        ·
          refine ⟨425404781023452943720932773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 283603187348968629147288515 425404781023452943720932773)
          ·
            refine ⟨79763396441897426947674895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 425404781023452943720932773 79763396441897426947674895)
            ·
              refine ⟨119645094662846140421512343, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 79763396441897426947674895 119645094662846140421512343)
              ·
                refine ⟨179467641994269210632268515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 119645094662846140421512343 179467641994269210632268515)
                ·
                  refine ⟨269201462991403815948402773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 179467641994269210632268515 269201462991403815948402773)
                  ·
                    refine ⟨3154704644430513468145345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 269201462991403815948402773 3154704644430513468145345)
                    ·
                      refine ⟨2366028483322885101109009, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3154704644430513468145345 2366028483322885101109009)
                      ·
                        rfl

theorem cell23_4607824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 1, 1, 1, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 1, 1, 1, 8, 2].length) (baseStart_4607824 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4607824 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4607824 prefixEnd_4607824 := by exact prefixLift 4607824
  have htrace : WordTrace (prefixWord ++ tailWord_4607824) baseStart_4607824 baseEnd_4607824 := by
    simpa [prefixWord, tailWord_4607824, baseEnd_4607824] using wordTrace_append hprefix tailTrace_4607824
  have hstable : (prefixWord ++ tailWord_4607824).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4607824).length < 2 ^ (prefixWord ++ tailWord_4607824).sum := by decide
  have hdescent : baseEnd_4607824 < baseStart_4607824 := by decide
  rcases family_descends (prefixWord ++ tailWord_4607824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4607834 : List Nat := [3, 1, 1, 2, 1, 3, 1, 1, 6, 4]
def baseStart_4607834 : Nat := 118140960795 + 4607834 * 2 ^ 59
def prefixEnd_4607834 : Nat := 4983230072969 + 3 ^ 40 * 4607834 * 2
def baseEnd_4607834 : Nat := 788677872709810020661321

theorem tailTrace_4607834 : CollatzResearch.WordTrace tailWord_4607834 prefixEnd_4607834 788677872709810020661321 := by
  unfold tailWord_4607834
  simp only [CollatzResearch.WordTrace]
  refine ⟨42015378197152962059897639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 112041008525741232159727037 42015378197152962059897639)
  ·
    refine ⟨63023067295729443089846459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42015378197152962059897639 63023067295729443089846459)
    ·
      refine ⟨94534600943594164634769689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63023067295729443089846459 94534600943594164634769689)
      ·
        refine ⟨70900950707695623476077267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 94534600943594164634769689 70900950707695623476077267)
        ·
          refine ⟨106351426061543435214115901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 70900950707695623476077267 106351426061543435214115901)
          ·
            refine ⟨39881784773078788205293463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 106351426061543435214115901 39881784773078788205293463)
            ·
              refine ⟨59822677159618182307940195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39881784773078788205293463 59822677159618182307940195)
              ·
                refine ⟨89734015739427273461910293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 59822677159618182307940195 89734015739427273461910293)
                ·
                  refine ⟨4206281987785653443527045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 89734015739427273461910293 4206281987785653443527045)
                  ·
                    refine ⟨788677872709810020661321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4206281987785653443527045 788677872709810020661321)
                    ·
                      rfl

theorem cell23_4607834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 1, 1, 6, 4].length) (baseStart_4607834 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4607834 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4607834 prefixEnd_4607834 := by exact prefixLift 4607834
  have htrace : WordTrace (prefixWord ++ tailWord_4607834) baseStart_4607834 baseEnd_4607834 := by
    simpa [prefixWord, tailWord_4607834, baseEnd_4607834] using wordTrace_append hprefix tailTrace_4607834
  have hstable : (prefixWord ++ tailWord_4607834).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4607834).length < 2 ^ (prefixWord ++ tailWord_4607834).sum := by decide
  have hdescent : baseEnd_4607834 < baseStart_4607834 := by decide
  rcases family_descends (prefixWord ++ tailWord_4607834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4607861 : List Nat := [1, 3, 4, 1, 1, 1, 2, 2, 3, 2, 3]
def baseStart_4607861 : Nat := 118140960795 + 4607861 * 2 ^ 59
def prefixEnd_4607861 : Nat := 4983230072969 + 3 ^ 40 * 4607861 * 2
def baseEnd_4607861 : Nat := 2366047482107101456346339

theorem tailTrace_4607861 : CollatzResearch.WordTrace tailWord_4607861 prefixEnd_4607861 2366047482107101456346339 := by
  unfold tailWord_4607861
  simp only [CollatzResearch.WordTrace]
  refine ⟨168062497559514031850823437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112041665039676021233882291 168062497559514031850823437)
  ·
    refine ⟨63023436584817761944058789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 168062497559514031850823437 63023436584817761944058789)
    ·
      refine ⟨11816894359653330364511023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 63023436584817761944058789 11816894359653330364511023)
      ·
        refine ⟨17725341539479995546766535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11816894359653330364511023 17725341539479995546766535)
        ·
          refine ⟨26588012309219993320149803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17725341539479995546766535 26588012309219993320149803)
          ·
            refine ⟨39882018463829989980224705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26588012309219993320149803 39882018463829989980224705)
            ·
              refine ⟨29911513847872492485168529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 39882018463829989980224705 29911513847872492485168529)
              ·
                refine ⟨22433635385904369363876397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29911513847872492485168529 22433635385904369363876397)
                ·
                  refine ⟨8412613269714138511453649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22433635385904369363876397 8412613269714138511453649)
                  ·
                    refine ⟨6309459952285603883590237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8412613269714138511453649 6309459952285603883590237)
                    ·
                      refine ⟨2366047482107101456346339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6309459952285603883590237 2366047482107101456346339)
                      ·
                        rfl

theorem cell23_4607861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 2, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 2, 2, 3, 2, 3].length) (baseStart_4607861 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4607861 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4607861 prefixEnd_4607861 := by exact prefixLift 4607861
  have htrace : WordTrace (prefixWord ++ tailWord_4607861) baseStart_4607861 baseEnd_4607861 := by
    simpa [prefixWord, tailWord_4607861, baseEnd_4607861] using wordTrace_append hprefix tailTrace_4607861
  have hstable : (prefixWord ++ tailWord_4607861).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4607861).length < 2 ^ (prefixWord ++ tailWord_4607861).sum := by decide
  have hdescent : baseEnd_4607861 < baseStart_4607861 := by decide
  rcases family_descends (prefixWord ++ tailWord_4607861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4607867 : List Nat := [1, 1, 1, 1, 1, 5, 1, 1, 1, 4, 6]
def baseStart_4607867 : Nat := 118140960795 + 4607867 * 2 ^ 59
def prefixEnd_4607867 : Nat := 4983230072969 + 3 ^ 40 * 4607867 * 2
def baseEnd_4607867 : Nat := 2366050562991028432871311

theorem tailTrace_4607867 : CollatzResearch.WordTrace tailWord_4607867 prefixEnd_4607867 2366050562991028432871311 := by
  unfold tailWord_4607867
  simp only [CollatzResearch.WordTrace]
  refine ⟨168062716397492294875541855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112041810931661529917027903 168062716397492294875541855)
  ·
    refine ⟨252094074596238442313312783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 168062716397492294875541855 252094074596238442313312783)
    ·
      refine ⟨378141111894357663469969175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 252094074596238442313312783 378141111894357663469969175)
      ·
        refine ⟨567211667841536495204953763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 378141111894357663469969175 567211667841536495204953763)
        ·
          refine ⟨850817501762304742807430645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 567211667841536495204953763 850817501762304742807430645)
          ·
            refine ⟨79764140790216069638196623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 850817501762304742807430645 79764140790216069638196623)
            ·
              refine ⟨119646211185324104457294935, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 79764140790216069638196623 119646211185324104457294935)
              ·
                refine ⟨179469316777986156685942403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 119646211185324104457294935 179469316777986156685942403)
                ·
                  refine ⟨269203975166979235028913605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 179469316777986156685942403 269203975166979235028913605)
                  ·
                    refine ⟨50475745343808606567921301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 269203975166979235028913605 50475745343808606567921301)
                    ·
                      refine ⟨2366050562991028432871311, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 50475745343808606567921301 2366050562991028432871311)
                      ·
                        rfl

theorem cell23_4607867_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 1, 1, 1, 4, 6].length) (baseStart_4607867 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4607867 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4607867 prefixEnd_4607867 := by exact prefixLift 4607867
  have htrace : WordTrace (prefixWord ++ tailWord_4607867) baseStart_4607867 baseEnd_4607867 := by
    simpa [prefixWord, tailWord_4607867, baseEnd_4607867] using wordTrace_append hprefix tailTrace_4607867
  have hstable : (prefixWord ++ tailWord_4607867).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4607867).length < 2 ^ (prefixWord ++ tailWord_4607867).sum := by decide
  have hdescent : baseEnd_4607867 < baseStart_4607867 := by decide
  rcases family_descends (prefixWord ++ tailWord_4607867) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4607887 : List Nat := [1, 1, 2, 1, 1, 1, 1, 1, 4, 3, 7]
def baseStart_4607887 : Nat := 118140960795 + 4607887 * 2 ^ 59
def prefixEnd_4607887 : Nat := 4983230072969 + 3 ^ 40 * 4607887 * 2
def baseEnd_4607887 : Nat := 2366060832604118354621219

theorem tailTrace_4607887 : CollatzResearch.WordTrace tailWord_4607887 prefixEnd_4607887 2366060832604118354621219 := by
  unfold tailWord_4607887
  simp only [CollatzResearch.WordTrace]
  refine ⟨168063445857419838291269915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112042297238279892194179943 168063445857419838291269915)
  ·
    refine ⟨252095168786129757436904873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 168063445857419838291269915 252095168786129757436904873)
    ·
      refine ⟨189071376589597318077678655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 252095168786129757436904873 189071376589597318077678655)
      ·
        refine ⟨283607064884395977116517983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 189071376589597318077678655 283607064884395977116517983)
        ·
          refine ⟨425410597326593965674776975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 283607064884395977116517983 425410597326593965674776975)
          ·
            refine ⟨638115895989890948512165463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 425410597326593965674776975 638115895989890948512165463)
            ·
              refine ⟨957173843984836422768248195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 638115895989890948512165463 957173843984836422768248195)
              ·
                refine ⟨1435760765977254634152372293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 957173843984836422768248195 1435760765977254634152372293)
                ·
                  refine ⟨269205143620735243903569805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1435760765977254634152372293 269205143620735243903569805)
                  ·
                    refine ⟨100951928857775716463838677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 269205143620735243903569805 100951928857775716463838677)
                    ·
                      refine ⟨2366060832604118354621219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 100951928857775716463838677 2366060832604118354621219)
                      ·
                        rfl

theorem cell23_4607887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 4, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 4, 3, 7].length) (baseStart_4607887 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4607887 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4607887 prefixEnd_4607887 := by exact prefixLift 4607887
  have htrace : WordTrace (prefixWord ++ tailWord_4607887) baseStart_4607887 baseEnd_4607887 := by
    simpa [prefixWord, tailWord_4607887, baseEnd_4607887] using wordTrace_append hprefix tailTrace_4607887
  have hstable : (prefixWord ++ tailWord_4607887).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4607887).length < 2 ^ (prefixWord ++ tailWord_4607887).sum := by decide
  have hdescent : baseEnd_4607887 < baseStart_4607887 := by decide
  rcases family_descends (prefixWord ++ tailWord_4607887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4607902 : List Nat := [4, 3, 1, 3, 1, 1, 2, 2, 2, 4]
def baseStart_4607902 : Nat := 118140960795 + 4607902 * 2 ^ 59
def prefixEnd_4607902 : Nat := 4983230072969 + 3 ^ 40 * 4607902 * 2
def baseEnd_4607902 : Nat := 788689511604645265311217

theorem tailTrace_4607902 : CollatzResearch.WordTrace tailWord_4607902 prefixEnd_4607902 788689511604645265311217 := by
  unfold tailWord_4607902
  simp only [CollatzResearch.WordTrace]
  refine ⟨21007999119045686981633245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 112042661968243663902043973 21007999119045686981633245)
  ·
    refine ⟨7877999669642132618112467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21007999119045686981633245 7877999669642132618112467)
    ·
      refine ⟨11816999504463198927168701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7877999669642132618112467 11816999504463198927168701)
      ·
        refine ⟨4431374814173699597688263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11816999504463198927168701 4431374814173699597688263)
        ·
          refine ⟨6647062221260549396532395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4431374814173699597688263 6647062221260549396532395)
          ·
            refine ⟨9970593331890824094798593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6647062221260549396532395 9970593331890824094798593)
            ·
              refine ⟨7477944998918118071098945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9970593331890824094798593 7477944998918118071098945)
              ·
                refine ⟨5608458749188588553324209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7477944998918118071098945 5608458749188588553324209)
                ·
                  refine ⟨4206344061891441414993157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5608458749188588553324209 4206344061891441414993157)
                  ·
                    refine ⟨788689511604645265311217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4206344061891441414993157 788689511604645265311217)
                    ·
                      rfl

theorem cell23_4607902_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 1, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 1, 1, 2, 2, 2, 4].length) (baseStart_4607902 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4607902 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4607902 prefixEnd_4607902 := by exact prefixLift 4607902
  have htrace : WordTrace (prefixWord ++ tailWord_4607902) baseStart_4607902 baseEnd_4607902 := by
    simpa [prefixWord, tailWord_4607902, baseEnd_4607902] using wordTrace_append hprefix tailTrace_4607902
  have hstable : (prefixWord ++ tailWord_4607902).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4607902).length < 2 ^ (prefixWord ++ tailWord_4607902).sum := by decide
  have hdescent : baseEnd_4607902 < baseStart_4607902 := by decide
  rcases family_descends (prefixWord ++ tailWord_4607902) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4607908 : List Nat := [2, 3, 1, 2, 1, 3, 1, 4, 2, 1, 3]
def baseStart_4607908 : Nat := 118140960795 + 4607908 * 2 ^ 59
def prefixEnd_4607908 : Nat := 4983230072969 + 3 ^ 40 * 4607908 * 2
def baseEnd_4607908 : Nat := 2366071615697862772458623

theorem tailTrace_4607908 : CollatzResearch.WordTrace tailWord_4607908 prefixEnd_4607908 2366071615697862772458623 := by
  unfold tailWord_4607908
  simp only [CollatzResearch.WordTrace]
  refine ⟨84032105895171879438892189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 112042807860229172585189585 84032105895171879438892189)
  ·
    refine ⟨31512039710689454789584571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 84032105895171879438892189 31512039710689454789584571)
    ·
      refine ⟨47268059566034182184376857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31512039710689454789584571 47268059566034182184376857)
      ·
        refine ⟨35451044674525636638282643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47268059566034182184376857 35451044674525636638282643)
        ·
          refine ⟨53176567011788454957423965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35451044674525636638282643 53176567011788454957423965)
          ·
            refine ⟨19941212629420670609033987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 53176567011788454957423965 19941212629420670609033987)
            ·
              refine ⟨29911818944131005913550981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19941212629420670609033987 29911818944131005913550981)
              ·
                refine ⟨5608466052024563608790809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 29911818944131005913550981 5608466052024563608790809)
                ·
                  refine ⟨4206349539018422706593107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5608466052024563608790809 4206349539018422706593107)
                  ·
                    refine ⟨6309524308527634059889661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4206349539018422706593107 6309524308527634059889661)
                    ·
                      refine ⟨2366071615697862772458623, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6309524308527634059889661 2366071615697862772458623)
                      ·
                        rfl

theorem cell23_4607908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 1, 4, 2, 1, 3].length) (baseStart_4607908 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4607908 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4607908 prefixEnd_4607908 := by exact prefixLift 4607908
  have htrace : WordTrace (prefixWord ++ tailWord_4607908) baseStart_4607908 baseEnd_4607908 := by
    simpa [prefixWord, tailWord_4607908, baseEnd_4607908] using wordTrace_append hprefix tailTrace_4607908
  have hstable : (prefixWord ++ tailWord_4607908).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4607908).length < 2 ^ (prefixWord ++ tailWord_4607908).sum := by decide
  have hdescent : baseEnd_4607908 < baseStart_4607908 := by decide
  rcases family_descends (prefixWord ++ tailWord_4607908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4607931 : List Nat := [1, 1, 1, 1, 1, 2, 2, 7, 1, 4, 2]
def baseStart_4607931 : Nat := 118140960795 + 4607931 * 2 ^ 59
def prefixEnd_4607931 : Nat := 4983230072969 + 3 ^ 40 * 4607931 * 2
def baseEnd_4607931 : Nat := 2366083425752916182471017

theorem tailTrace_4607931 : CollatzResearch.WordTrace tailWord_4607931 prefixEnd_4607931 2366083425752916182471017 := by
  unfold tailWord_4607931
  simp only [CollatzResearch.WordTrace]
  refine ⟨168065050669260433805871647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112043367112840289203914431 168065050669260433805871647)
  ·
    refine ⟨252097576003890650708807471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 168065050669260433805871647 252097576003890650708807471)
    ·
      refine ⟨378146364005835976063211207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 252097576003890650708807471 378146364005835976063211207)
      ·
        refine ⟨567219546008753964094816811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 378146364005835976063211207 567219546008753964094816811)
        ·
          refine ⟨850829319013130946142225217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 567219546008753964094816811 850829319013130946142225217)
          ·
            refine ⟨638121989259848209606668913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 850829319013130946142225217 638121989259848209606668913)
            ·
              refine ⟨478591491944886157205001685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 638121989259848209606668913 478591491944886157205001685)
              ·
                refine ⟨11216988092458269309492227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 478591491944886157205001685 11216988092458269309492227)
                ·
                  refine ⟨16825482138687403964238341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11216988092458269309492227 16825482138687403964238341)
                  ·
                    refine ⟨3154777901003888243294689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16825482138687403964238341 3154777901003888243294689)
                    ·
                      refine ⟨2366083425752916182471017, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3154777901003888243294689 2366083425752916182471017)
                      ·
                        rfl

theorem cell23_4607931_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 7, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 7, 1, 4, 2].length) (baseStart_4607931 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4607931 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4607931 prefixEnd_4607931 := by exact prefixLift 4607931
  have htrace : WordTrace (prefixWord ++ tailWord_4607931) baseStart_4607931 baseEnd_4607931 := by
    simpa [prefixWord, tailWord_4607931, baseEnd_4607931] using wordTrace_append hprefix tailTrace_4607931
  have hstable : (prefixWord ++ tailWord_4607931).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4607931).length < 2 ^ (prefixWord ++ tailWord_4607931).sum := by decide
  have hdescent : baseEnd_4607931 < baseStart_4607931 := by decide
  rcases family_descends (prefixWord ++ tailWord_4607931) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4607948 : List Nat := [2, 2, 1, 4, 1, 2, 2, 2, 1, 4, 2]
def baseStart_4607948 : Nat := 118140960795 + 4607948 * 2 ^ 59
def prefixEnd_4607948 : Nat := 4983230072969 + 3 ^ 40 * 4607948 * 2
def baseEnd_4607948 : Nat := 2366092154924042615958439

theorem tailTrace_4607948 : CollatzResearch.WordTrace tailWord_4607948 prefixEnd_4607948 2366092154924042615958439 := by
  unfold tailWord_4607948
  simp only [CollatzResearch.WordTrace]
  refine ⟨84032835355099422854620249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 112043780473465897139493665 84032835355099422854620249)
  ·
    refine ⟨63024626516324567140965187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 84032835355099422854620249 63024626516324567140965187)
    ·
      refine ⟨94536939774486850711447781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63024626516324567140965187 94536939774486850711447781)
      ·
        refine ⟨17725676207716284508396459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 94536939774486850711447781 17725676207716284508396459)
        ·
          refine ⟨26588514311574426762594689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17725676207716284508396459 26588514311574426762594689)
          ·
            refine ⟨19941385733680820071946017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26588514311574426762594689 19941385733680820071946017)
            ·
              refine ⟨14956039300260615053959513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19941385733680820071946017 14956039300260615053959513)
              ·
                refine ⟨11217029475195461290469635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14956039300260615053959513 11217029475195461290469635)
                ·
                  refine ⟨16825544212793191935704453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11217029475195461290469635 16825544212793191935704453)
                  ·
                    refine ⟨3154789539898723487944585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16825544212793191935704453 3154789539898723487944585)
                    ·
                      refine ⟨2366092154924042615958439, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3154789539898723487944585 2366092154924042615958439)
                      ·
                        rfl

theorem cell23_4607948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 2, 2, 1, 4, 2].length) (baseStart_4607948 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4607948 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4607948 prefixEnd_4607948 := by exact prefixLift 4607948
  have htrace : WordTrace (prefixWord ++ tailWord_4607948) baseStart_4607948 baseEnd_4607948 := by
    simpa [prefixWord, tailWord_4607948, baseEnd_4607948] using wordTrace_append hprefix tailTrace_4607948
  have hstable : (prefixWord ++ tailWord_4607948).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4607948).length < 2 ^ (prefixWord ++ tailWord_4607948).sum := by decide
  have hdescent : baseEnd_4607948 < baseStart_4607948 := by decide
  rcases family_descends (prefixWord ++ tailWord_4607948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4607971 : List Nat := [1, 1, 1, 6, 1, 3, 2, 1, 7]
def baseStart_4607971 : Nat := 118140960795 + 4607971 * 2 ^ 59
def prefixEnd_4607971 : Nat := 4983230072969 + 3 ^ 40 * 4607971 * 2
def baseEnd_4607971 : Nat := 262900440553232891774537

theorem tailTrace_4607971 : CollatzResearch.WordTrace tailWord_4607971 prefixEnd_4607971 262900440553232891774537 := by
  unfold tailWord_4607971
  simp only [CollatzResearch.WordTrace]
  refine ⟨168066509589115520637327767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112044339726077013758218511 168066509589115520637327767)
  ·
    refine ⟨252099764383673280955991651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 168066509589115520637327767 252099764383673280955991651)
    ·
      refine ⟨378149646575509921433987477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 252099764383673280955991651 378149646575509921433987477)
      ·
        refine ⟨17725764683227027567218163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 378149646575509921433987477 17725764683227027567218163)
        ·
          refine ⟨26588647024840541350827245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17725764683227027567218163 26588647024840541350827245)
          ·
            refine ⟨9970742634315203006560217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26588647024840541350827245 9970742634315203006560217)
            ·
              refine ⟨7478056975736402254920163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9970742634315203006560217 7478056975736402254920163)
              ·
                refine ⟨11217085463604603382380245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7478056975736402254920163 11217085463604603382380245)
                ·
                  refine ⟨262900440553232891774537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11217085463604603382380245 262900440553232891774537)
                  ·
                    rfl

theorem cell23_4607971_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 3, 2, 1, 7].length) (baseStart_4607971 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4607971 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4607971 prefixEnd_4607971 := by exact prefixLift 4607971
  have htrace : WordTrace (prefixWord ++ tailWord_4607971) baseStart_4607971 baseEnd_4607971 := by
    simpa [prefixWord, tailWord_4607971, baseEnd_4607971] using wordTrace_append hprefix tailTrace_4607971
  have hstable : (prefixWord ++ tailWord_4607971).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4607971).length < 2 ^ (prefixWord ++ tailWord_4607971).sum := by decide
  have hdescent : baseEnd_4607971 < baseStart_4607971 := by decide
  rcases family_descends (prefixWord ++ tailWord_4607971) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4607984 : List Nat := [2, 1, 1, 1, 3, 2, 3, 2, 1, 7]
def baseStart_4607984 : Nat := 118140960795 + 4607984 * 2 ^ 59
def prefixEnd_4607984 : Nat := 4983230072969 + 3 ^ 40 * 4607984 * 2
def baseEnd_4607984 : Nat := 788703546742534825036091

theorem tailTrace_4607984 : CollatzResearch.WordTrace tailWord_4607984 prefixEnd_4607984 788703546742534825036091 := by
  unfold tailWord_4607984
  simp only [CollatzResearch.WordTrace]
  refine ⟨84033491869034211928775503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 112044655825378949238367337 84033491869034211928775503)
  ·
    refine ⟨126050237803551317893163255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84033491869034211928775503 126050237803551317893163255)
    ·
      refine ⟨189075356705326976839744883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 126050237803551317893163255 189075356705326976839744883)
      ·
        refine ⟨283613035057990465259617325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 189075356705326976839744883 283613035057990465259617325)
        ·
          refine ⟨106354888146746424472356497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 283613035057990465259617325 106354888146746424472356497)
          ·
            refine ⟨79766166110059818354267373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 106354888146746424472356497 79766166110059818354267373)
            ·
              refine ⟨29912312291272431882850265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 79766166110059818354267373 29912312291272431882850265)
              ·
                refine ⟨22434234218454323912137699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29912312291272431882850265 22434234218454323912137699)
                ·
                  refine ⟨33651351327681485868206549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22434234218454323912137699 33651351327681485868206549)
                  ·
                    refine ⟨788703546742534825036091, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 33651351327681485868206549 788703546742534825036091)
                    ·
                      rfl

theorem cell23_4607984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 3, 2, 1, 7].length) (baseStart_4607984 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4607984 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4607984 prefixEnd_4607984 := by exact prefixLift 4607984
  have htrace : WordTrace (prefixWord ++ tailWord_4607984) baseStart_4607984 baseEnd_4607984 := by
    simpa [prefixWord, tailWord_4607984, baseEnd_4607984] using wordTrace_append hprefix tailTrace_4607984
  have hstable : (prefixWord ++ tailWord_4607984).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4607984).length < 2 ^ (prefixWord ++ tailWord_4607984).sum := by decide
  have hdescent : baseEnd_4607984 < baseStart_4607984 := by decide
  rcases family_descends (prefixWord ++ tailWord_4607984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4607994 : List Nat := [3, 1, 1, 1, 1, 2, 1, 1, 5, 2, 5]
def baseStart_4607994 : Nat := 118140960795 + 4607994 * 2 ^ 59
def prefixEnd_4607994 : Nat := 4983230072969 + 3 ^ 40 * 4607994 * 2
def baseEnd_4607994 : Nat := 2366115775034149435983227

theorem tailTrace_4607994 : CollatzResearch.WordTrace tailWord_4607994 prefixEnd_4607994 2366115775034149435983227 := by
  unfold tailWord_4607994
  simp only [CollatzResearch.WordTrace]
  refine ⟨42016837117008048891353759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 112044898978688130376943357 42016837117008048891353759)
  ·
    refine ⟨63025255675512073337030639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42016837117008048891353759 63025255675512073337030639)
    ·
      refine ⟨94537883513268110005545959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63025255675512073337030639 94537883513268110005545959)
      ·
        refine ⟨141806825269902165008318939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 94537883513268110005545959 141806825269902165008318939)
        ·
          refine ⟨212710237904853247512478409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 141806825269902165008318939 212710237904853247512478409)
          ·
            refine ⟨159532678428639935634358807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 212710237904853247512478409 159532678428639935634358807)
            ·
              refine ⟨239299017642959903451538211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 159532678428639935634358807 239299017642959903451538211)
              ·
                refine ⟨358948526464439855177307317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 239299017642959903451538211 358948526464439855177307317)
                ·
                  refine ⟨33651424356041236422872561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 358948526464439855177307317 33651424356041236422872561)
                  ·
                    refine ⟨25238568267030927317154421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 33651424356041236422872561 25238568267030927317154421)
                    ·
                      refine ⟨2366115775034149435983227, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25238568267030927317154421 2366115775034149435983227)
                      ·
                        rfl

theorem cell23_4607994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 1, 5, 2, 5].length) (baseStart_4607994 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4607994 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4607994 prefixEnd_4607994 := by exact prefixLift 4607994
  have htrace : WordTrace (prefixWord ++ tailWord_4607994) baseStart_4607994 baseEnd_4607994 := by
    simpa [prefixWord, tailWord_4607994, baseEnd_4607994] using wordTrace_append hprefix tailTrace_4607994
  have hstable : (prefixWord ++ tailWord_4607994).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4607994).length < 2 ^ (prefixWord ++ tailWord_4607994).sum := by decide
  have hdescent : baseEnd_4607994 < baseStart_4607994 := by decide
  rcases family_descends (prefixWord ++ tailWord_4607994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4608001 : List Nat := [1, 2, 4, 1, 2, 1, 2, 3, 2, 5]
def baseStart_4608001 : Nat := 118140960795 + 4608001 * 2 ^ 59
def prefixEnd_4608001 : Nat := 4983230072969 + 3 ^ 40 * 4608001 * 2
def baseEnd_4608001 : Nat := 788706456466243636198565

theorem tailTrace_4608001 : CollatzResearch.WordTrace tailWord_4608001 prefixEnd_4608001 788706456466243636198565 := by
  unfold tailWord_4608001
  simp only [CollatzResearch.WordTrace]
  refine ⟨168067603779006835760919857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112045069186004557173946571 168067603779006835760919857)
  ·
    refine ⟨126050702834255126820689893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 168067603779006835760919857 126050702834255126820689893)
    ·
      refine ⟨23634506781422836278879355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 126050702834255126820689893 23634506781422836278879355)
      ·
        refine ⟨35451760172134254418319033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23634506781422836278879355 35451760172134254418319033)
        ·
          refine ⟨26588820129100690813739275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35451760172134254418319033 26588820129100690813739275)
          ·
            refine ⟨39883230193651036220608913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26588820129100690813739275 39883230193651036220608913)
            ·
              refine ⟨29912422645238277165456685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 39883230193651036220608913 29912422645238277165456685)
              ·
                refine ⟨11217158491964353937046257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 29912422645238277165456685 11217158491964353937046257)
                ·
                  refine ⟨8412868868973265452784693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11217158491964353937046257 8412868868973265452784693)
                  ·
                    refine ⟨788706456466243636198565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8412868868973265452784693 788706456466243636198565)
                    ·
                      rfl

theorem cell23_4608001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 2, 3, 2, 5].length) (baseStart_4608001 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4608001 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4608001 prefixEnd_4608001 := by exact prefixLift 4608001
  have htrace : WordTrace (prefixWord ++ tailWord_4608001) baseStart_4608001 baseEnd_4608001 := by
    simpa [prefixWord, tailWord_4608001, baseEnd_4608001] using wordTrace_append hprefix tailTrace_4608001
  have hstable : (prefixWord ++ tailWord_4608001).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4608001).length < 2 ^ (prefixWord ++ tailWord_4608001).sum := by decide
  have hdescent : baseEnd_4608001 < baseStart_4608001 := by decide
  rcases family_descends (prefixWord ++ tailWord_4608001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4608044 : List Nat := [2, 2, 1, 1, 1, 2, 2, 2, 10]
def baseStart_4608044 : Nat := 118140960795 + 4608044 * 2 ^ 59
def prefixEnd_4608044 : Nat := 4983230072969 + 3 ^ 40 * 4608044 * 2
def baseEnd_4608044 : Nat := 262904605451874915595333

theorem tailTrace_4608044 : CollatzResearch.WordTrace tailWord_4608044 prefixEnd_4608044 262904605451874915595333 := by
  unfold tailWord_4608044
  simp only [CollatzResearch.WordTrace]
  refine ⟨84034586058925527052367593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 112046114745234036069823457 84034586058925527052367593)
  ·
    refine ⟨63025939544194145289275695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 84034586058925527052367593 63025939544194145289275695)
    ·
      refine ⟨94538909316291217933913543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63025939544194145289275695 94538909316291217933913543)
      ·
        refine ⟨141808363974436826900870315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 94538909316291217933913543 141808363974436826900870315)
        ·
          refine ⟨212712545961655240351305473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 141808363974436826900870315 212712545961655240351305473)
          ·
            refine ⟨159534409471241430263479105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 212712545961655240351305473 159534409471241430263479105)
            ·
              refine ⟨119650807103431072697609329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 159534409471241430263479105 119650807103431072697609329)
              ·
                refine ⟨89738105327573304523206997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 119650807103431072697609329 89738105327573304523206997)
                ·
                  refine ⟨262904605451874915595333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 89738105327573304523206997 262904605451874915595333)
                  ·
                    rfl

theorem cell23_4608044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 10].length) (baseStart_4608044 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4608044 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4608044 prefixEnd_4608044 := by exact prefixLift 4608044
  have htrace : WordTrace (prefixWord ++ tailWord_4608044) baseStart_4608044 baseEnd_4608044 := by
    simpa [prefixWord, tailWord_4608044, baseEnd_4608044] using wordTrace_append hprefix tailTrace_4608044
  have hstable : (prefixWord ++ tailWord_4608044).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4608044).length < 2 ^ (prefixWord ++ tailWord_4608044).sum := by decide
  have hdescent : baseEnd_4608044 < baseStart_4608044 := by decide
  rcases family_descends (prefixWord ++ tailWord_4608044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4608078 : List Nat := [4, 1, 1, 1, 1, 5, 2, 2, 6]
def baseStart_4608078 : Nat := 118140960795 + 4608078 * 2 ^ 59
def prefixEnd_4608078 : Nat := 4983230072969 + 3 ^ 40 * 4608078 * 2
def baseEnd_4608078 : Nat := 262906545267680789703649

theorem tailTrace_4608078 : CollatzResearch.WordTrace tailWord_4608078 prefixEnd_4608078 262906545267680789703649 := by
  unfold tailWord_4608078
  simp only [CollatzResearch.WordTrace]
  refine ⟨21008801524965984738934111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 112046941466485251940981925 21008801524965984738934111)
  ·
    refine ⟨31513202287448977108401167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21008801524965984738934111 31513202287448977108401167)
    ·
      refine ⟨47269803431173465662601751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31513202287448977108401167 47269803431173465662601751)
      ·
        refine ⟨70904705146760198493902627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47269803431173465662601751 70904705146760198493902627)
        ·
          refine ⟨106357057720140297740853941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 70904705146760198493902627 106357057720140297740853941)
          ·
            refine ⟨9970974161263152913205057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 106357057720140297740853941 9970974161263152913205057)
            ·
              refine ⟨7478230620947364684903793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9970974161263152913205057 7478230620947364684903793)
              ·
                refine ⟨5608672965710523513677845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7478230620947364684903793 5608672965710523513677845)
                ·
                  refine ⟨262906545267680789703649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5608672965710523513677845 262906545267680789703649)
                  ·
                    rfl

theorem cell23_4608078_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 5, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 5, 2, 2, 6].length) (baseStart_4608078 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4608078 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4608078 prefixEnd_4608078 := by exact prefixLift 4608078
  have htrace : WordTrace (prefixWord ++ tailWord_4608078) baseStart_4608078 baseEnd_4608078 := by
    simpa [prefixWord, tailWord_4608078, baseEnd_4608078] using wordTrace_append hprefix tailTrace_4608078
  have hstable : (prefixWord ++ tailWord_4608078).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4608078).length < 2 ^ (prefixWord ++ tailWord_4608078).sum := by decide
  have hdescent : baseEnd_4608078 < baseStart_4608078 := by decide
  rcases family_descends (prefixWord ++ tailWord_4608078) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4608082 : List Nat := [3, 2, 2, 1, 4, 1, 1, 4, 1, 4]
def baseStart_4608082 : Nat := 118140960795 + 4608082 * 2 ^ 59
def prefixEnd_4608082 : Nat := 4983230072969 + 3 ^ 40 * 4608082 * 2
def baseEnd_4608082 : Nat := 788720320443915030560941

theorem tailTrace_4608082 : CollatzResearch.WordTrace tailWord_4608082 prefixEnd_4608082 788720320443915030560941 := by
  unfold tailWord_4608082
  simp only [CollatzResearch.WordTrace]
  refine ⟨42017639522928346648654625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 112047038727808924396412333 42017639522928346648654625)
  ·
    refine ⟨31513229642196259986490969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42017639522928346648654625 31513229642196259986490969)
    ·
      refine ⟨23634922231647194989868227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31513229642196259986490969 23634922231647194989868227)
      ·
        refine ⟨35452383347470792484802341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23634922231647194989868227 35452383347470792484802341)
        ·
          refine ⟨6647321877650773590900439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 35452383347470792484802341 6647321877650773590900439)
          ·
            refine ⟨9970982816476160386350659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6647321877650773590900439 9970982816476160386350659)
            ·
              refine ⟨14956474224714240579525989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9970982816476160386350659 14956474224714240579525989)
              ·
                refine ⟨2804338917133920108661123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14956474224714240579525989 2804338917133920108661123)
                ·
                  refine ⟨4206508375700880162991685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2804338917133920108661123 4206508375700880162991685)
                  ·
                    refine ⟨788720320443915030560941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4206508375700880162991685 788720320443915030560941)
                    ·
                      rfl

theorem cell23_4608082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 4, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 4, 1, 1, 4, 1, 4].length) (baseStart_4608082 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4608082 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4608082 prefixEnd_4608082 := by exact prefixLift 4608082
  have htrace : WordTrace (prefixWord ++ tailWord_4608082) baseStart_4608082 baseEnd_4608082 := by
    simpa [prefixWord, tailWord_4608082, baseEnd_4608082] using wordTrace_append hprefix tailTrace_4608082
  have hstable : (prefixWord ++ tailWord_4608082).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4608082).length < 2 ^ (prefixWord ++ tailWord_4608082).sum := by decide
  have hdescent : baseEnd_4608082 < baseStart_4608082 := by decide
  rcases family_descends (prefixWord ++ tailWord_4608082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4608125 : List Nat := [1, 4, 1, 1, 3, 2, 4, 1, 1, 5]
def baseStart_4608125 : Nat := 118140960795 + 4608125 * 2 ^ 59
def prefixEnd_4608125 : Nat := 4983230072969 + 3 ^ 40 * 4608125 * 2
def baseEnd_4608125 : Nat := 788727680333296141148375

theorem tailTrace_4608125 : CollatzResearch.WordTrace tailWord_4608125 prefixEnd_4608125 788727680333296141148375 := by
  unfold tailWord_4608125
  simp only [CollatzResearch.WordTrace]
  refine ⟨168072126430557604938433829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112048084287038403292289219 168072126430557604938433829)
  ·
    refine ⟨31513523705729550925956343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 168072126430557604938433829 31513523705729550925956343)
    ·
      refine ⟨47270285558594326388934515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31513523705729550925956343 47270285558594326388934515)
      ·
        refine ⟨70905428337891489583401773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47270285558594326388934515 70905428337891489583401773)
        ·
          refine ⟨26589535626709308593775665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 70905428337891489583401773 26589535626709308593775665)
          ·
            refine ⟨19942151720031981445331749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26589535626709308593775665 19942151720031981445331749)
            ·
              refine ⟨3739153447505996520999703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 19942151720031981445331749 3739153447505996520999703)
              ·
                refine ⟨5608730171258994781499555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3739153447505996520999703 5608730171258994781499555)
                ·
                  refine ⟨8413095256888492172249333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5608730171258994781499555 8413095256888492172249333)
                  ·
                    refine ⟨788727680333296141148375, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8413095256888492172249333 788727680333296141148375)
                    ·
                      rfl

theorem cell23_4608125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 4, 1, 1, 5].length) (baseStart_4608125 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4608125 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4608125 prefixEnd_4608125 := by exact prefixLift 4608125
  have htrace : WordTrace (prefixWord ++ tailWord_4608125) baseStart_4608125 baseEnd_4608125 := by
    simpa [prefixWord, tailWord_4608125, baseEnd_4608125] using wordTrace_append hprefix tailTrace_4608125
  have hstable : (prefixWord ++ tailWord_4608125).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4608125).length < 2 ^ (prefixWord ++ tailWord_4608125).sum := by decide
  have hdescent : baseEnd_4608125 < baseStart_4608125 := by decide
  rcases family_descends (prefixWord ++ tailWord_4608125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4608162 : List Nat := [3, 3, 1, 3, 1, 2, 2, 2, 1, 1, 4]
def baseStart_4608162 : Nat := 118140960795 + 4608162 * 2 ^ 59
def prefixEnd_4608162 : Nat := 4983230072969 + 3 ^ 40 * 4608162 * 2
def baseEnd_4608162 : Nat := 2366202039784104778682455

theorem tailTrace_4608162 : CollatzResearch.WordTrace tailWord_4608162 prefixEnd_4608162 2366202039784104778682455 := by
  unfold tailWord_4608162
  simp only [CollatzResearch.WordTrace]
  refine ⟨42018368982855890064382685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 112048983954282373505020493 42018368982855890064382685)
  ·
    refine ⟨15756888368570958774143507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 42018368982855890064382685 15756888368570958774143507)
    ·
      refine ⟨23635332552856438161215261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15756888368570958774143507 23635332552856438161215261)
      ·
        refine ⟨8863249707321164310455723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23635332552856438161215261 8863249707321164310455723)
        ·
          refine ⟨13294874560981746465683585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8863249707321164310455723 13294874560981746465683585)
          ·
            refine ⟨9971155920736309849262689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13294874560981746465683585 9971155920736309849262689)
            ·
              refine ⟨7478366940552232386947017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9971155920736309849262689 7478366940552232386947017)
              ·
                refine ⟨5608775205414174290210263, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7478366940552232386947017 5608775205414174290210263)
                ·
                  refine ⟨8413162808121261435315395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5608775205414174290210263 8413162808121261435315395)
                  ·
                    refine ⟨12619744212181892152973093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8413162808121261435315395 12619744212181892152973093)
                    ·
                      refine ⟨2366202039784104778682455, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12619744212181892152973093 2366202039784104778682455)
                      ·
                        rfl

theorem cell23_4608162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 2, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 2, 2, 2, 1, 1, 4].length) (baseStart_4608162 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4608162 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4608162 prefixEnd_4608162 := by exact prefixLift 4608162
  have htrace : WordTrace (prefixWord ++ tailWord_4608162) baseStart_4608162 baseEnd_4608162 := by
    simpa [prefixWord, tailWord_4608162, baseEnd_4608162] using wordTrace_append hprefix tailTrace_4608162
  have hstable : (prefixWord ++ tailWord_4608162).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4608162).length < 2 ^ (prefixWord ++ tailWord_4608162).sum := by decide
  have hdescent : baseEnd_4608162 < baseStart_4608162 := by decide
  rcases family_descends (prefixWord ++ tailWord_4608162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4608165 : List Nat := [1, 3, 1, 2, 1, 3, 4, 2, 1, 2, 3]
def baseStart_4608165 : Nat := 118140960795 + 4608165 * 2 ^ 59
def prefixEnd_4608165 : Nat := 4983230072969 + 3 ^ 40 * 4608165 * 2
def baseEnd_4608165 : Nat := 2366203580226068266944941

theorem tailTrace_4608165 : CollatzResearch.WordTrace tailWord_4608165 prefixEnd_4608165 2366203580226068266944941 := by
  unfold tailWord_4608165
  simp only [CollatzResearch.WordTrace]
  refine ⟨168073585350412691769889949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112049056900275127846593299 168073585350412691769889949)
  ·
    refine ⟨63027594506404759413708731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 168073585350412691769889949 63027594506404759413708731)
    ·
      refine ⟨94541391759607139120563097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63027594506404759413708731 94541391759607139120563097)
      ·
        refine ⟨70906043819705354340422323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 94541391759607139120563097 70906043819705354340422323)
        ·
          refine ⟨106359065729558031510633485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 70906043819705354340422323 106359065729558031510633485)
          ·
            refine ⟨39884649648584261816487557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 106359065729558031510633485 39884649648584261816487557)
            ·
              refine ⟨7478371809109549090591417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 39884649648584261816487557 7478371809109549090591417)
              ·
                refine ⟨5608778856832161817943563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7478371809109549090591417 5608778856832161817943563)
                ·
                  refine ⟨8413168285248242726915345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5608778856832161817943563 8413168285248242726915345)
                  ·
                    refine ⟨6309876213936182045186509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8413168285248242726915345 6309876213936182045186509)
                    ·
                      refine ⟨2366203580226068266944941, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6309876213936182045186509 2366203580226068266944941)
                      ·
                        rfl

theorem cell23_4608165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 4, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 4, 2, 1, 2, 3].length) (baseStart_4608165 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4608165 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4608165 prefixEnd_4608165 := by exact prefixLift 4608165
  have htrace : WordTrace (prefixWord ++ tailWord_4608165) baseStart_4608165 baseEnd_4608165 := by
    simpa [prefixWord, tailWord_4608165, baseEnd_4608165] using wordTrace_append hprefix tailTrace_4608165
  have hstable : (prefixWord ++ tailWord_4608165).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4608165).length < 2 ^ (prefixWord ++ tailWord_4608165).sum := by decide
  have hdescent : baseEnd_4608165 < baseStart_4608165 := by decide
  rcases family_descends (prefixWord ++ tailWord_4608165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4608178 : List Nat := [3, 2, 1, 1, 1, 3, 2, 1, 3, 3, 3]
def baseStart_4608178 : Nat := 118140960795 + 4608178 * 2 ^ 59
def prefixEnd_4608178 : Nat := 4983230072969 + 3 ^ 40 * 4608178 * 2
def baseEnd_4608178 : Nat := 2366210255474576716082381

theorem tailTrace_4608178 : CollatzResearch.WordTrace tailWord_4608178 prefixEnd_4608178 2366210255474576716082381 := by
  unfold tailWord_4608178
  simp only [CollatzResearch.WordTrace]
  refine ⟨42018514874841398747528297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 112049372999577063326742125 42018514874841398747528297)
  ·
    refine ⟨31513886156131049060646223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42018514874841398747528297 31513886156131049060646223)
    ·
      refine ⟨47270829234196573590969335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31513886156131049060646223 47270829234196573590969335)
      ·
        refine ⟨70906243851294860386454003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47270829234196573590969335 70906243851294860386454003)
        ·
          refine ⟨106359365776942290579681005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 70906243851294860386454003 106359365776942290579681005)
          ·
            refine ⟨39884762166353358967380377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 106359365776942290579681005 39884762166353358967380377)
            ·
              refine ⟨29913571624765019225535283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 39884762166353358967380377 29913571624765019225535283)
              ·
                refine ⟨44870357437147528838302925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29913571624765019225535283 44870357437147528838302925)
                ·
                  refine ⟨16826384038930323314363597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 44870357437147528838302925 16826384038930323314363597)
                  ·
                    refine ⟨6309894014598871242886349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16826384038930323314363597 6309894014598871242886349)
                    ·
                      refine ⟨2366210255474576716082381, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6309894014598871242886349 2366210255474576716082381)
                      ·
                        rfl

theorem cell23_4608178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 2, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 2, 1, 3, 3, 3].length) (baseStart_4608178 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4608178 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4608178 prefixEnd_4608178 := by exact prefixLift 4608178
  have htrace : WordTrace (prefixWord ++ tailWord_4608178) baseStart_4608178 baseEnd_4608178 := by
    simpa [prefixWord, tailWord_4608178, baseEnd_4608178] using wordTrace_append hprefix tailTrace_4608178
  have hstable : (prefixWord ++ tailWord_4608178).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4608178).length < 2 ^ (prefixWord ++ tailWord_4608178).sum := by decide
  have hdescent : baseEnd_4608178 < baseStart_4608178 := by decide
  rcases family_descends (prefixWord ++ tailWord_4608178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4608191 : List Nat := [1, 1, 2, 2, 2, 2, 1, 1, 4, 2, 5]
def baseStart_4608191 : Nat := 118140960795 + 4608191 * 2 ^ 59
def prefixEnd_4608191 : Nat := 4983230072969 + 3 ^ 40 * 4608191 * 2
def baseEnd_4608191 : Nat := 2366216930723085165219821

theorem tailTrace_4608191 : CollatzResearch.WordTrace tailWord_4608191 prefixEnd_4608191 2366216930723085165219821 := by
  unfold tailWord_4608191
  simp only [CollatzResearch.WordTrace]
  refine ⟨168074533648318498210336427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112049689098878998806890951 168074533648318498210336427)
  ·
    refine ⟨252111800472477747315504641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 168074533648318498210336427 252111800472477747315504641)
    ·
      refine ⟨189083850354358310486628481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 252111800472477747315504641 189083850354358310486628481)
      ·
        refine ⟨141812887765768732864971361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 189083850354358310486628481 141812887765768732864971361)
        ·
          refine ⟨106359665824326549648728521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 141812887765768732864971361 106359665824326549648728521)
          ·
            refine ⟨79769749368244912236546391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 106359665824326549648728521 79769749368244912236546391)
            ·
              refine ⟨119654624052367368354819587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 79769749368244912236546391 119654624052367368354819587)
              ·
                refine ⟨179481936078551052532229381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 119654624052367368354819587 179481936078551052532229381)
                ·
                  refine ⟨33652863014728322349793009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 179481936078551052532229381 33652863014728322349793009)
                  ·
                    refine ⟨25239647261046241762344757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 33652863014728322349793009 25239647261046241762344757)
                    ·
                      refine ⟨2366216930723085165219821, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25239647261046241762344757 2366216930723085165219821)
                      ·
                        rfl

theorem cell23_4608191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 1, 1, 4, 2, 5].length) (baseStart_4608191 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4608191 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4608191 prefixEnd_4608191 := by exact prefixLift 4608191
  have htrace : WordTrace (prefixWord ++ tailWord_4608191) baseStart_4608191 baseEnd_4608191 := by
    simpa [prefixWord, tailWord_4608191, baseEnd_4608191] using wordTrace_append hprefix tailTrace_4608191
  have hstable : (prefixWord ++ tailWord_4608191).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4608191).length < 2 ^ (prefixWord ++ tailWord_4608191).sum := by decide
  have hdescent : baseEnd_4608191 < baseStart_4608191 := by decide
  rcases family_descends (prefixWord ++ tailWord_4608191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4608235 : List Nat := [1, 1, 1, 1, 2, 5, 3, 2, 1, 4, 2]
def baseStart_4608235 : Nat := 118140960795 + 4608235 * 2 ^ 59
def prefixEnd_4608235 : Nat := 4983230072969 + 3 ^ 40 * 4608235 * 2
def baseEnd_4608235 : Nat := 2366239523871882993069619

theorem tailTrace_4608235 : CollatzResearch.WordTrace tailWord_4608235 prefixEnd_4608235 2366239523871882993069619 := by
  unfold tailWord_4608235
  simp only [CollatzResearch.WordTrace]
  refine ⟨168076138460159093724938159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112050758973439395816625439 168076138460159093724938159)
  ·
    refine ⟨252114207690238640587407239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 168076138460159093724938159 252114207690238640587407239)
    ·
      refine ⟨378171311535357960881110859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 252114207690238640587407239 378171311535357960881110859)
      ·
        refine ⟨567256967303036941321666289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 378171311535357960881110859 567256967303036941321666289)
        ·
          refine ⟨425442725477277705991249717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 567256967303036941321666289 425442725477277705991249717)
          ·
            refine ⟨39885255513494784936679661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 425442725477277705991249717 39885255513494784936679661)
            ·
              refine ⟨14956970817560544351254873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 39885255513494784936679661 14956970817560544351254873)
              ·
                refine ⟨11217728113170408263441155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14956970817560544351254873 11217728113170408263441155)
                ·
                  refine ⟨16826592169755612395161733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11217728113170408263441155 16826592169755612395161733)
                  ·
                    refine ⟨3154986031829177324092825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16826592169755612395161733 3154986031829177324092825)
                    ·
                      refine ⟨2366239523871882993069619, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3154986031829177324092825 2366239523871882993069619)
                      ·
                        rfl

theorem cell23_4608235_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 3, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 3, 2, 1, 4, 2].length) (baseStart_4608235 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4608235 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4608235 prefixEnd_4608235 := by exact prefixLift 4608235
  have htrace : WordTrace (prefixWord ++ tailWord_4608235) baseStart_4608235 baseEnd_4608235 := by
    simpa [prefixWord, tailWord_4608235, baseEnd_4608235] using wordTrace_append hprefix tailTrace_4608235
  have hstable : (prefixWord ++ tailWord_4608235).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4608235).length < 2 ^ (prefixWord ++ tailWord_4608235).sum := by decide
  have hdescent : baseEnd_4608235 < baseStart_4608235 := by decide
  rcases family_descends (prefixWord ++ tailWord_4608235) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4608239 : List Nat := [1, 1, 2, 1, 6, 2, 3, 1, 1, 3, 2]
def baseStart_4608239 : Nat := 118140960795 + 4608239 * 2 ^ 59
def prefixEnd_4608239 : Nat := 4983230072969 + 3 ^ 40 * 4608239 * 2
def baseEnd_4608239 : Nat := 2366241577794500977419601

theorem tailTrace_4608239 : CollatzResearch.WordTrace tailWord_4608239 prefixEnd_4608239 2366241577794500977419601 := by
  unfold tailWord_4608239
  simp only [CollatzResearch.WordTrace]
  refine ⟨168076284352144602408083771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112050856234763068272055847 168076284352144602408083771)
  ·
    refine ⟨252114426528216903612125657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 168076284352144602408083771 252114426528216903612125657)
    ·
      refine ⟨189085819896162677709094243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 252114426528216903612125657 189085819896162677709094243)
      ·
        refine ⟨283628729844244016563641365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 189085819896162677709094243 283628729844244016563641365)
        ·
          refine ⟨13295096711448938276420689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 283628729844244016563641365 13295096711448938276420689)
          ·
            refine ⟨9971322533586703707315517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13295096711448938276420689 9971322533586703707315517)
            ·
              refine ⟨3739245950095013890243319, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9971322533586703707315517 3739245950095013890243319)
              ·
                refine ⟨5608868925142520835364979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3739245950095013890243319 5608868925142520835364979)
                ·
                  refine ⟨8413303387713781253047469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5608868925142520835364979 8413303387713781253047469)
                  ·
                    refine ⟨3154988770392667969892801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8413303387713781253047469 3154988770392667969892801)
                    ·
                      refine ⟨2366241577794500977419601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3154988770392667969892801 2366241577794500977419601)
                      ·
                        rfl

theorem cell23_4608239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 2, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 2, 3, 1, 1, 3, 2].length) (baseStart_4608239 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4608239 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4608239 prefixEnd_4608239 := by exact prefixLift 4608239
  have htrace : WordTrace (prefixWord ++ tailWord_4608239) baseStart_4608239 baseEnd_4608239 := by
    simpa [prefixWord, tailWord_4608239, baseEnd_4608239] using wordTrace_append hprefix tailTrace_4608239
  have hstable : (prefixWord ++ tailWord_4608239).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4608239).length < 2 ^ (prefixWord ++ tailWord_4608239).sum := by decide
  have hdescent : baseEnd_4608239 < baseStart_4608239 := by decide
  rcases family_descends (prefixWord ++ tailWord_4608239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4608292 : List Nat := [2, 3, 1, 3, 1, 3, 2, 3, 5]
def baseStart_4608292 : Nat := 118140960795 + 4608292 * 2 ^ 59
def prefixEnd_4608292 : Nat := 4983230072969 + 3 ^ 40 * 4608292 * 2
def baseEnd_4608292 : Nat := 262918754696576585561873

theorem tailTrace_4608292 : CollatzResearch.WordTrace tailWord_4608292 prefixEnd_4608292 262918754696576585561873 := by
  unfold tailWord_4608292
  simp only [CollatzResearch.WordTrace]
  refine ⟨84039108710476296229881565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 112052144947301728306508753 84039108710476296229881565)
  ·
    refine ⟨31514665766428611086205587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 84039108710476296229881565 31514665766428611086205587)
    ·
      refine ⟨47271998649642916629308381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31514665766428611086205587 47271998649642916629308381)
      ·
        refine ⟨17726999493616093735990643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 47271998649642916629308381 17726999493616093735990643)
        ·
          refine ⟨26590499240424140603985965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17726999493616093735990643 26590499240424140603985965)
          ·
            refine ⟨9971437215159052726494737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26590499240424140603985965 9971437215159052726494737)
            ·
              refine ⟨7478577911369289544871053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9971437215159052726494737 7478577911369289544871053)
              ·
                refine ⟨2804466716763483579326645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7478577911369289544871053 2804466716763483579326645)
                ·
                  refine ⟨262918754696576585561873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2804466716763483579326645 262918754696576585561873)
                  ·
                    rfl

theorem cell23_4608292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 3, 2, 3, 5].length) (baseStart_4608292 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4608292 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4608292 prefixEnd_4608292 := by exact prefixLift 4608292
  have htrace : WordTrace (prefixWord ++ tailWord_4608292) baseStart_4608292 baseEnd_4608292 := by
    simpa [prefixWord, tailWord_4608292, baseEnd_4608292] using wordTrace_append hprefix tailTrace_4608292
  have hstable : (prefixWord ++ tailWord_4608292).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4608292).length < 2 ^ (prefixWord ++ tailWord_4608292).sum := by decide
  have hdescent : baseEnd_4608292 < baseStart_4608292 := by decide
  rcases family_descends (prefixWord ++ tailWord_4608292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4608345 : List Nat := [1, 2, 1, 2, 2, 2, 1, 5, 2, 2, 3]
def baseStart_4608345 : Nat := 118140960795 + 4608345 * 2 ^ 59
def prefixEnd_4608345 : Nat := 4983230072969 + 3 ^ 40 * 4608345 * 2
def baseEnd_4608345 : Nat := 2366296006743877562694113

theorem tailTrace_4608345 : CollatzResearch.WordTrace tailWord_4608345 prefixEnd_4608345 2366296006743877562694113 := by
  unfold tailWord_4608345
  simp only [CollatzResearch.WordTrace]
  refine ⟨168080150489760582511442489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112053433659840388340961659 168080150489760582511442489)
  ·
    refine ⟨126060112867320436883581867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 168080150489760582511442489 126060112867320436883581867)
    ·
      refine ⟨189090169300980655325372801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 126060112867320436883581867 189090169300980655325372801)
      ·
        refine ⟨141817626975735491494029601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 189090169300980655325372801 141817626975735491494029601)
        ·
          refine ⟨106363220231801618620522201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 141817626975735491494029601 106363220231801618620522201)
          ·
            refine ⟨79772415173851213965391651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 106363220231801618620522201 79772415173851213965391651)
            ·
              refine ⟨119658622760776820948087477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 79772415173851213965391651 119658622760776820948087477)
              ·
                refine ⟨11217995883822826963883201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 119658622760776820948087477 11217995883822826963883201)
                ·
                  refine ⟨8413496912867120222912401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11217995883822826963883201 8413496912867120222912401)
                  ·
                    refine ⟨6310122684650340167184301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8413496912867120222912401 6310122684650340167184301)
                    ·
                      refine ⟨2366296006743877562694113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6310122684650340167184301 2366296006743877562694113)
                      ·
                        rfl

theorem cell23_4608345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 1, 5, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 1, 5, 2, 2, 3].length) (baseStart_4608345 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4608345 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4608345 prefixEnd_4608345 := by exact prefixLift 4608345
  have htrace : WordTrace (prefixWord ++ tailWord_4608345) baseStart_4608345 baseEnd_4608345 := by
    simpa [prefixWord, tailWord_4608345, baseEnd_4608345] using wordTrace_append hprefix tailTrace_4608345
  have hstable : (prefixWord ++ tailWord_4608345).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4608345).length < 2 ^ (prefixWord ++ tailWord_4608345).sum := by decide
  have hdescent : baseEnd_4608345 < baseStart_4608345 := by decide
  rcases family_descends (prefixWord ++ tailWord_4608345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4608362 : List Nat := [3, 1, 3, 3, 1, 1, 1, 1, 4, 2, 3]
def baseStart_4608362 : Nat := 118140960795 + 4608362 * 2 ^ 59
def prefixEnd_4608362 : Nat := 4983230072969 + 3 ^ 40 * 4608362 * 2
def baseEnd_4608362 : Nat := 2366304735915003996181535

theorem tailTrace_4608362 : CollatzResearch.WordTrace tailWord_4608362 prefixEnd_4608362 2366304735915003996181535 := by
  unfold tailWord_4608362
  simp only [CollatzResearch.WordTrace]
  refine ⟨42020192632674748603702835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 112053847020465996276540893 42020192632674748603702835)
  ·
    refine ⟨63030288949012122905554253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42020192632674748603702835 63030288949012122905554253)
    ·
      refine ⟨23636358355879546089582845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 63030288949012122905554253 23636358355879546089582845)
      ·
        refine ⟨8863634383454829783593567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23636358355879546089582845 8863634383454829783593567)
        ·
          refine ⟨13295451575182244675390351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8863634383454829783593567 13295451575182244675390351)
          ·
            refine ⟨19943177362773367013085527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13295451575182244675390351 19943177362773367013085527)
            ·
              refine ⟨29914766044160050519628291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19943177362773367013085527 29914766044160050519628291)
              ·
                refine ⟨44872149066240075779442437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29914766044160050519628291 44872149066240075779442437)
                ·
                  refine ⟨8413527949920014208645457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 44872149066240075779442437 8413527949920014208645457)
                  ·
                    refine ⟨6310145962440010656484093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8413527949920014208645457 6310145962440010656484093)
                    ·
                      refine ⟨2366304735915003996181535, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6310145962440010656484093 2366304735915003996181535)
                      ·
                        rfl

theorem cell23_4608362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 1, 1, 4, 2, 3].length) (baseStart_4608362 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4608362 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4608362 prefixEnd_4608362 := by exact prefixLift 4608362
  have htrace : WordTrace (prefixWord ++ tailWord_4608362) baseStart_4608362 baseEnd_4608362 := by
    simpa [prefixWord, tailWord_4608362, baseEnd_4608362] using wordTrace_append hprefix tailTrace_4608362
  have hstable : (prefixWord ++ tailWord_4608362).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4608362).length < 2 ^ (prefixWord ++ tailWord_4608362).sum := by decide
  have hdescent : baseEnd_4608362 < baseStart_4608362 := by decide
  rcases family_descends (prefixWord ++ tailWord_4608362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4608365 : List Nat := [1, 5, 1, 1, 1, 2, 2, 4, 6]
def baseStart_4608365 : Nat := 118140960795 + 4608365 * 2 ^ 59
def prefixEnd_4608365 : Nat := 4983230072969 + 3 ^ 40 * 4608365 * 2
def baseEnd_4608365 : Nat := 262922919595218609382669

theorem tailTrace_4608365 : CollatzResearch.WordTrace tailWord_4608365 prefixEnd_4608365 262922919595218609382669 := by
  unfold tailWord_4608365
  simp only [CollatzResearch.WordTrace]
  refine ⟨168080879949688125927170549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112053919966458750618113699 168080879949688125927170549)
  ·
    refine ⟨15757582495283261805672239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 168080879949688125927170549 15757582495283261805672239)
    ·
      refine ⟨23636373742924892708508359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15757582495283261805672239 23636373742924892708508359)
      ·
        refine ⟨35454560614387339062762539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23636373742924892708508359 35454560614387339062762539)
        ·
          refine ⟨53181840921581008594143809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35454560614387339062762539 53181840921581008594143809)
          ·
            refine ⟨39886380691185756445607857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 53181840921581008594143809 39886380691185756445607857)
            ·
              refine ⟨29914785518389317334205893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 39886380691185756445607857 29914785518389317334205893)
              ·
                refine ⟨5609022284697997000163605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 29914785518389317334205893 5609022284697997000163605)
                ·
                  refine ⟨262922919595218609382669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5609022284697997000163605 262922919595218609382669)
                  ·
                    rfl

theorem cell23_4608365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 2, 4, 6].length) (baseStart_4608365 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4608365 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4608365 prefixEnd_4608365 := by exact prefixLift 4608365
  have htrace : WordTrace (prefixWord ++ tailWord_4608365) baseStart_4608365 baseEnd_4608365 := by
    simpa [prefixWord, tailWord_4608365, baseEnd_4608365] using wordTrace_append hprefix tailTrace_4608365
  have hstable : (prefixWord ++ tailWord_4608365).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4608365).length < 2 ^ (prefixWord ++ tailWord_4608365).sum := by decide
  have hdescent : baseEnd_4608365 < baseStart_4608365 := by decide
  rcases family_descends (prefixWord ++ tailWord_4608365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4608392 : List Nat := [2, 1, 3, 3, 1, 1, 2, 1, 5, 1, 3]
def baseStart_4608392 : Nat := 118140960795 + 4608392 * 2 ^ 59
def prefixEnd_4608392 : Nat := 4983230072969 + 3 ^ 40 * 4608392 * 2
def baseEnd_4608392 : Nat := 2366320140334638878806397

theorem tailTrace_4608392 : CollatzResearch.WordTrace tailWord_4608392 prefixEnd_4608392 2366320140334638878806397 := by
  unfold tailWord_4608392
  simp only [CollatzResearch.WordTrace]
  refine ⟨84040932360295154769201715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 112054576480393539692268953 84040932360295154769201715)
  ·
    refine ⟨126061398540442732153802573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84040932360295154769201715 126061398540442732153802573)
    ·
      refine ⟨47273024452666024557675965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 126061398540442732153802573 47273024452666024557675965)
      ·
        refine ⟨17727384169749759209128487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 47273024452666024557675965 17727384169749759209128487)
        ·
          refine ⟨26591076254624638813692731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17727384169749759209128487 26591076254624638813692731)
          ·
            refine ⟨39886614381936958220539097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26591076254624638813692731 39886614381936958220539097)
            ·
              refine ⟨29914960786452718665404323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 39886614381936958220539097 29914960786452718665404323)
              ·
                refine ⟨44872441179679077998106485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29914960786452718665404323 44872441179679077998106485)
                ·
                  refine ⟨4206791360594913562322483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 44872441179679077998106485 4206791360594913562322483)
                  ·
                    refine ⟨6310187040892370343483725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4206791360594913562322483 6310187040892370343483725)
                    ·
                      refine ⟨2366320140334638878806397, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6310187040892370343483725 2366320140334638878806397)
                      ·
                        rfl

theorem cell23_4608392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 2, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 2, 1, 5, 1, 3].length) (baseStart_4608392 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4608392 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4608392 prefixEnd_4608392 := by exact prefixLift 4608392
  have htrace : WordTrace (prefixWord ++ tailWord_4608392) baseStart_4608392 baseEnd_4608392 := by
    simpa [prefixWord, tailWord_4608392, baseEnd_4608392] using wordTrace_append hprefix tailTrace_4608392
  have hstable : (prefixWord ++ tailWord_4608392).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4608392).length < 2 ^ (prefixWord ++ tailWord_4608392).sum := by decide
  have hdescent : baseEnd_4608392 < baseStart_4608392 := by decide
  rcases family_descends (prefixWord ++ tailWord_4608392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4608395 : List Nat := [1, 1, 1, 1, 4, 5, 1, 1, 3, 5]
def baseStart_4608395 : Nat := 118140960795 + 4608395 * 2 ^ 59
def prefixEnd_4608395 : Nat := 4983230072969 + 3 ^ 40 * 4608395 * 2
def baseEnd_4608395 : Nat := 788773893592200789022961

theorem tailTrace_4608395 : CollatzResearch.WordTrace tailWord_4608395 prefixEnd_4608395 788773893592200789022961 := by
  unfold tailWord_4608395
  simp only [CollatzResearch.WordTrace]
  refine ⟨168081974139579441050762639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112054649426386294033841759 168081974139579441050762639)
  ·
    refine ⟨252122961209369161576143959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 168081974139579441050762639 252122961209369161576143959)
    ·
      refine ⟨378184441814053742364215939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 252122961209369161576143959 378184441814053742364215939)
      ·
        refine ⟨567276662721080613546323909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 378184441814053742364215939 567276662721080613546323909)
        ·
          refine ⟨106364374260202615039935733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 567276662721080613546323909 106364374260202615039935733)
          ·
            refine ⟨9971660086893995159993975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 106364374260202615039935733 9971660086893995159993975)
            ·
              refine ⟨14957490130340992739990963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9971660086893995159993975 14957490130340992739990963)
              ·
                refine ⟨22436235195511489109986445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14957490130340992739990963 22436235195511489109986445)
                ·
                  refine ⟨8413588198316808416244917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22436235195511489109986445 8413588198316808416244917)
                  ·
                    refine ⟨788773893592200789022961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8413588198316808416244917 788773893592200789022961)
                    ·
                      rfl

theorem cell23_4608395_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 5, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 5, 1, 1, 3, 5].length) (baseStart_4608395 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4608395 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4608395 prefixEnd_4608395 := by exact prefixLift 4608395
  have htrace : WordTrace (prefixWord ++ tailWord_4608395) baseStart_4608395 baseEnd_4608395 := by
    simpa [prefixWord, tailWord_4608395, baseEnd_4608395] using wordTrace_append hprefix tailTrace_4608395
  have hstable : (prefixWord ++ tailWord_4608395).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4608395).length < 2 ^ (prefixWord ++ tailWord_4608395).sum := by decide
  have hdescent : baseEnd_4608395 < baseStart_4608395 := by decide
  rcases family_descends (prefixWord ++ tailWord_4608395) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4608409 : List Nat := [1, 2, 1, 2, 1, 4, 2, 5, 1, 1, 3]
def baseStart_4608409 : Nat := 118140960795 + 4608409 * 2 ^ 59
def prefixEnd_4608409 : Nat := 4983230072969 + 3 ^ 40 * 4608409 * 2
def baseEnd_4608409 : Nat := 2366328869505765312293819

theorem tailTrace_4608409 : CollatzResearch.WordTrace tailWord_4608409 prefixEnd_4608409 2366328869505765312293819 := by
  unfold tailWord_4608409
  simp only [CollatzResearch.WordTrace]
  refine ⟨168082484761528721441772281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112054989841019147627848187 168082484761528721441772281)
  ·
    refine ⟨126061863571146541081329211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 168082484761528721441772281 126061863571146541081329211)
    ·
      refine ⟨189092795356719811621993817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 126061863571146541081329211 189092795356719811621993817)
      ·
        refine ⟨141819596517539858716495363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 189092795356719811621993817 141819596517539858716495363)
        ·
          refine ⟨212729394776309788074743045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 141819596517539858716495363 212729394776309788074743045)
          ·
            refine ⟨39886761520558085264014321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 212729394776309788074743045 39886761520558085264014321)
            ·
              refine ⟨29915071140418563948010741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 39886761520558085264014321 29915071140418563948010741)
              ·
                refine ⟨2804537919414240370126007, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 29915071140418563948010741 2804537919414240370126007)
                ·
                  refine ⟨4206806879121360555189011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2804537919414240370126007 4206806879121360555189011)
                  ·
                    refine ⟨6310210318682040832783517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4206806879121360555189011 6310210318682040832783517)
                    ·
                      refine ⟨2366328869505765312293819, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6310210318682040832783517 2366328869505765312293819)
                      ·
                        rfl

theorem cell23_4608409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 2, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 2, 5, 1, 1, 3].length) (baseStart_4608409 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4608409 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4608409 prefixEnd_4608409 := by exact prefixLift 4608409
  have htrace : WordTrace (prefixWord ++ tailWord_4608409) baseStart_4608409 baseEnd_4608409 := by
    simpa [prefixWord, tailWord_4608409, baseEnd_4608409] using wordTrace_append hprefix tailTrace_4608409
  have hstable : (prefixWord ++ tailWord_4608409).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4608409).length < 2 ^ (prefixWord ++ tailWord_4608409).sum := by decide
  have hdescent : baseEnd_4608409 < baseStart_4608409 := by decide
  rcases family_descends (prefixWord ++ tailWord_4608409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4608425 : List Nat := [1, 2, 1, 1, 1, 1, 3, 5, 4, 4]
def baseStart_4608425 : Nat := 118140960795 + 4608425 * 2 ^ 59
def prefixEnd_4608425 : Nat := 4983230072969 + 3 ^ 40 * 4608425 * 2
def baseEnd_4608425 : Nat := 788779028398745749897915

theorem tailTrace_4608425 : CollatzResearch.WordTrace tailWord_4608425 prefixEnd_4608425 788779028398745749897915 := by
  unfold tailWord_4608425
  simp only [CollatzResearch.WordTrace]
  refine ⟨168083068329470756174354729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112055378886313837449569819 168083068329470756174354729)
  ·
    refine ⟨126062301247103067130766047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 168083068329470756174354729 126062301247103067130766047)
    ·
      refine ⟨189093451870654600696149071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 126062301247103067130766047 189093451870654600696149071)
      ·
        refine ⟨283640177805981901044223607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 189093451870654600696149071 283640177805981901044223607)
        ·
          refine ⟨425460266708972851566335411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 283640177805981901044223607 425460266708972851566335411)
          ·
            refine ⟨638190400063459277349503117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 425460266708972851566335411 638190400063459277349503117)
            ·
              refine ⟨239321400023797229006063669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 638190400063459277349503117 239321400023797229006063669)
              ·
                refine ⟨22436381252230990219318469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 239321400023797229006063669 22436381252230990219318469)
                ·
                  refine ⟨4206821484793310666122213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 22436381252230990219318469 4206821484793310666122213)
                  ·
                    refine ⟨788779028398745749897915, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4206821484793310666122213 788779028398745749897915)
                    ·
                      rfl

theorem cell23_4608425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 5, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 5, 4, 4].length) (baseStart_4608425 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4608425 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4608425 prefixEnd_4608425 := by exact prefixLift 4608425
  have htrace : WordTrace (prefixWord ++ tailWord_4608425) baseStart_4608425 baseEnd_4608425 := by
    simpa [prefixWord, tailWord_4608425, baseEnd_4608425] using wordTrace_append hprefix tailTrace_4608425
  have hstable : (prefixWord ++ tailWord_4608425).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4608425).length < 2 ^ (prefixWord ++ tailWord_4608425).sum := by decide
  have hdescent : baseEnd_4608425 < baseStart_4608425 := by decide
  rcases family_descends (prefixWord ++ tailWord_4608425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4608466 : List Nat := [3, 2, 2, 4, 1, 1, 1, 3, 1, 1, 4]
def baseStart_4608466 : Nat := 118140960795 + 4608466 * 2 ^ 59
def prefixEnd_4608466 : Nat := 4983230072969 + 3 ^ 40 * 4608466 * 2
def baseEnd_4608466 : Nat := 2366358137903071589281057

theorem tailTrace_4608466 : CollatzResearch.WordTrace tailWord_4608466 prefixEnd_4608466 2366358137903071589281057 := by
  unfold tailWord_4608466
  simp only [CollatzResearch.WordTrace]
  refine ⟨42021140930580555044149313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 112056375814881480117731501 42021140930580555044149313)
  ·
    refine ⟨31515855697935416283111985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42021140930580555044149313 31515855697935416283111985)
    ·
      refine ⟨23636891773451562212333989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31515855697935416283111985 23636891773451562212333989)
      ·
        refine ⟨4431917207522167914812623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 23636891773451562212333989 4431917207522167914812623)
        ·
          refine ⟨6647875811283251872218935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4431917207522167914812623 6647875811283251872218935)
          ·
            refine ⟨9971813716924877808328403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6647875811283251872218935 9971813716924877808328403)
            ·
              refine ⟨14957720575387316712492605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9971813716924877808328403 14957720575387316712492605)
              ·
                refine ⟨5609145215770243767184727, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14957720575387316712492605 5609145215770243767184727)
                ·
                  refine ⟨8413717823655365650777091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5609145215770243767184727 8413717823655365650777091)
                  ·
                    refine ⟨12620576735483048476165637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8413717823655365650777091 12620576735483048476165637)
                    ·
                      refine ⟨2366358137903071589281057, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12620576735483048476165637 2366358137903071589281057)
                      ·
                        rfl

theorem cell23_4608466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 1, 1, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 1, 1, 1, 3, 1, 1, 4].length) (baseStart_4608466 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4608466 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4608466 prefixEnd_4608466 := by exact prefixLift 4608466
  have htrace : WordTrace (prefixWord ++ tailWord_4608466) baseStart_4608466 baseEnd_4608466 := by
    simpa [prefixWord, tailWord_4608466, baseEnd_4608466] using wordTrace_append hprefix tailTrace_4608466
  have hstable : (prefixWord ++ tailWord_4608466).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4608466).length < 2 ^ (prefixWord ++ tailWord_4608466).sum := by decide
  have hdescent : baseEnd_4608466 < baseStart_4608466 := by decide
  rcases family_descends (prefixWord ++ tailWord_4608466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4608469 : List Nat := [1, 3, 2, 3, 1, 3, 1, 3, 1, 2, 3]
def baseStart_4608469 : Nat := 118140960795 + 4608469 * 2 ^ 59
def prefixEnd_4608469 : Nat := 4983230072969 + 3 ^ 40 * 4608469 * 2
def baseEnd_4608469 : Nat := 2366359678345035077543543

theorem tailTrace_4608469 : CollatzResearch.WordTrace tailWord_4608469 prefixEnd_4608469 2366359678345035077543543 := by
  unfold tailWord_4608469
  simp only [CollatzResearch.WordTrace]
  refine ⟨168084673141311351688956461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112056448760874234459304307 168084673141311351688956461)
  ·
    refine ⟨63031752427991756883358673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 168084673141311351688956461 63031752427991756883358673)
    ·
      refine ⟨47273814320993817662519005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 63031752427991756883358673 47273814320993817662519005)
      ·
        refine ⟨17727680370372681623444627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 47273814320993817662519005 17727680370372681623444627)
        ·
          refine ⟨26591520555559022435166941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17727680370372681623444627 26591520555559022435166941)
          ·
            refine ⟨9971820208334633413187603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26591520555559022435166941 9971820208334633413187603)
            ·
              refine ⟨14957730312501950119781405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9971820208334633413187603 14957730312501950119781405)
              ·
                refine ⟨5609148867188231294918027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14957730312501950119781405 5609148867188231294918027)
                ·
                  refine ⟨8413723300782346942377041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5609148867188231294918027 8413723300782346942377041)
                  ·
                    refine ⟨6310292475586760206782781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8413723300782346942377041 6310292475586760206782781)
                    ·
                      refine ⟨2366359678345035077543543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6310292475586760206782781 2366359678345035077543543)
                      ·
                        rfl

theorem cell23_4608469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 3, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 3, 1, 3, 1, 2, 3].length) (baseStart_4608469 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4608469 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4608469 prefixEnd_4608469 := by exact prefixLift 4608469
  have htrace : WordTrace (prefixWord ++ tailWord_4608469) baseStart_4608469 baseEnd_4608469 := by
    simpa [prefixWord, tailWord_4608469, baseEnd_4608469] using wordTrace_append hprefix tailTrace_4608469
  have hstable : (prefixWord ++ tailWord_4608469).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4608469).length < 2 ^ (prefixWord ++ tailWord_4608469).sum := by decide
  have hdescent : baseEnd_4608469 < baseStart_4608469 := by decide
  rcases family_descends (prefixWord ++ tailWord_4608469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4608505 : List Nat := [1, 2, 1, 3, 1, 2, 2, 2, 2, 3, 4]
def baseStart_4608505 : Nat := 118140960795 + 4608505 * 2 ^ 59
def prefixEnd_4608505 : Nat := 4983230072969 + 3 ^ 40 * 4608505 * 2
def baseEnd_4608505 : Nat := 2366378163648596936693377

theorem tailTrace_4608505 : CollatzResearch.WordTrace tailWord_4608505 prefixEnd_4608505 2366378163648596936693377 := by
  unfold tailWord_4608505
  simp only [CollatzResearch.WordTrace]
  refine ⟨168085986169180929837266969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112057324112787286558177979 168085986169180929837266969)
  ·
    refine ⟨126064489626885697377950227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 168085986169180929837266969 126064489626885697377950227)
    ·
      refine ⟨189096734440328546066925341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 126064489626885697377950227 189096734440328546066925341)
      ·
        refine ⟨70911275415123204775097003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 189096734440328546066925341 70911275415123204775097003)
        ·
          refine ⟨106366913122684807162645505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 70911275415123204775097003 106366913122684807162645505)
          ·
            refine ⟨79775184842013605371984129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 106366913122684807162645505 79775184842013605371984129)
            ·
              refine ⟨59831388631510204028988097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 79775184842013605371984129 59831388631510204028988097)
              ·
                refine ⟨44873541473632653021741073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 59831388631510204028988097 44873541473632653021741073)
                ·
                  refine ⟨33655156105224489766305805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 44873541473632653021741073 33655156105224489766305805)
                  ·
                    refine ⟨12620683539459183662364677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 33655156105224489766305805 12620683539459183662364677)
                    ·
                      refine ⟨2366378163648596936693377, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12620683539459183662364677 2366378163648596936693377)
                      ·
                        rfl

theorem cell23_4608505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 2, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 2, 2, 2, 3, 4].length) (baseStart_4608505 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4608505 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4608505 prefixEnd_4608505 := by exact prefixLift 4608505
  have htrace : WordTrace (prefixWord ++ tailWord_4608505) baseStart_4608505 baseEnd_4608505 := by
    simpa [prefixWord, tailWord_4608505, baseEnd_4608505] using wordTrace_append hprefix tailTrace_4608505
  have hstable : (prefixWord ++ tailWord_4608505).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4608505).length < 2 ^ (prefixWord ++ tailWord_4608505).sum := by decide
  have hdescent : baseEnd_4608505 < baseStart_4608505 := by decide
  rcases family_descends (prefixWord ++ tailWord_4608505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4608526 : List Nat := [4, 1, 1, 2, 3, 1, 2, 3, 1, 3, 2]
def baseStart_4608526 : Nat := 118140960795 + 4608526 * 2 ^ 59
def prefixEnd_4608526 : Nat := 4983230072969 + 3 ^ 40 * 4608526 * 2
def baseEnd_4608526 : Nat := 2366388946742341354530781

theorem tailTrace_4608526 : CollatzResearch.WordTrace tailWord_4608526 prefixEnd_4608526 2366388946742341354530781 := by
  unfold tailWord_4608526
  simp only [CollatzResearch.WordTrace]
  refine ⟨21010844012763106302972679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 112057834734736566949187621 21010844012763106302972679)
  ·
    refine ⟨31516266019144659454459019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21010844012763106302972679 31516266019144659454459019)
    ·
      refine ⟨47274399028716989181688529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31516266019144659454459019 47274399028716989181688529)
      ·
        refine ⟨35455799271537741886266397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47274399028716989181688529 35455799271537741886266397)
        ·
          refine ⟨13295924726826653207349899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 35455799271537741886266397 13295924726826653207349899)
          ·
            refine ⟨19943887090239979811024849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13295924726826653207349899 19943887090239979811024849)
            ·
              refine ⟨14957915317679984858268637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19943887090239979811024849 14957915317679984858268637)
              ·
                refine ⟨5609218244129994321850739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14957915317679984858268637 5609218244129994321850739)
                ·
                  refine ⟨8413827366194991482776109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5609218244129994321850739 8413827366194991482776109)
                  ·
                    refine ⟨3155185262323121806041041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8413827366194991482776109 3155185262323121806041041)
                    ·
                      refine ⟨2366388946742341354530781, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3155185262323121806041041 2366388946742341354530781)
                      ·
                        rfl

theorem cell23_4608526_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 2, 3, 1, 3, 2].length) (baseStart_4608526 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4608526 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4608526 prefixEnd_4608526 := by exact prefixLift 4608526
  have htrace : WordTrace (prefixWord ++ tailWord_4608526) baseStart_4608526 baseEnd_4608526 := by
    simpa [prefixWord, tailWord_4608526, baseEnd_4608526] using wordTrace_append hprefix tailTrace_4608526
  have hstable : (prefixWord ++ tailWord_4608526).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4608526).length < 2 ^ (prefixWord ++ tailWord_4608526).sum := by decide
  have hdescent : baseEnd_4608526 < baseStart_4608526 := by decide
  rcases family_descends (prefixWord ++ tailWord_4608526) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4608596 : List Nat := [2, 4, 1, 1, 1, 3, 4, 2, 5]
def baseStart_4608596 : Nat := 118140960795 + 4608596 * 2 ^ 59
def prefixEnd_4608596 : Nat := 4983230072969 + 3 ^ 40 * 4608596 * 2
def baseEnd_4608596 : Nat := 262936098932017342295051

theorem tailTrace_4608596 : CollatzResearch.WordTrace tailWord_4608596 prefixEnd_4608596 262936098932017342295051 := by
  unfold tailWord_4608596
  simp only [CollatzResearch.WordTrace]
  refine ⟨84044652605925626189414821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 112059536807900834919219761 84044652605925626189414821)
  ·
    refine ⟨15758372363611054910515279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 84044652605925626189414821 15758372363611054910515279)
    ·
      refine ⟨23637558545416582365772919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15758372363611054910515279 23637558545416582365772919)
      ·
        refine ⟨35456337818124873548659379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23637558545416582365772919 35456337818124873548659379)
        ·
          refine ⟨53184506727187310322989069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35456337818124873548659379 53184506727187310322989069)
          ·
            refine ⟨19944190022695241371120901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 53184506727187310322989069 19944190022695241371120901)
            ·
              refine ⟨3739535629255357757085169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 19944190022695241371120901 3739535629255357757085169)
              ·
                refine ⟨2804651721941518317813877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3739535629255357757085169 2804651721941518317813877)
                ·
                  refine ⟨262936098932017342295051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2804651721941518317813877 262936098932017342295051)
                  ·
                    rfl

theorem cell23_4608596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 4, 2, 5].length) (baseStart_4608596 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4608596 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4608596 prefixEnd_4608596 := by exact prefixLift 4608596
  have htrace : WordTrace (prefixWord ++ tailWord_4608596) baseStart_4608596 baseEnd_4608596 := by
    simpa [prefixWord, tailWord_4608596, baseEnd_4608596] using wordTrace_append hprefix tailTrace_4608596
  have hstable : (prefixWord ++ tailWord_4608596).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4608596).length < 2 ^ (prefixWord ++ tailWord_4608596).sum := by decide
  have hdescent : baseEnd_4608596 < baseStart_4608596 := by decide
  rcases family_descends (prefixWord ++ tailWord_4608596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4608612 : List Nat := [2, 3, 1, 1, 2, 2, 2, 2, 1, 3, 4]
def baseStart_4608612 : Nat := 118140960795 + 4608612 * 2 ^ 59
def prefixEnd_4608612 : Nat := 4983230072969 + 3 ^ 40 * 4608612 * 2
def baseEnd_4608612 : Nat := 2366433106078628018055385

theorem tailTrace_4608612 : CollatzResearch.WordTrace tailWord_4608612 prefixEnd_4608612 2366433106078628018055385 := by
  unfold tailWord_4608612
  simp only [CollatzResearch.WordTrace]
  refine ⟨84044944389896643555706045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 112059925853195524740941393 84044944389896643555706045)
  ·
    refine ⟨31516854146211241333389767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 84044944389896643555706045 31516854146211241333389767)
    ·
      refine ⟨47275281219316862000084651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31516854146211241333389767 47275281219316862000084651)
      ·
        refine ⟨70912921828975293000126977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47275281219316862000084651 70912921828975293000126977)
        ·
          refine ⟨53184691371731469750095233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 70912921828975293000126977 53184691371731469750095233)
          ·
            refine ⟨39888518528798602312571425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 53184691371731469750095233 39888518528798602312571425)
            ·
              refine ⟨29916388896598951734428569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 39888518528798602312571425 29916388896598951734428569)
              ·
                refine ⟨22437291672449213800821427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29916388896598951734428569 22437291672449213800821427)
                ·
                  refine ⟨33655937508673820701232141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22437291672449213800821427 33655937508673820701232141)
                  ·
                    refine ⟨12620976565752682762962053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 33655937508673820701232141 12620976565752682762962053)
                    ·
                      refine ⟨2366433106078628018055385, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12620976565752682762962053 2366433106078628018055385)
                      ·
                        rfl

theorem cell23_4608612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 2, 2, 1, 3, 4].length) (baseStart_4608612 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4608612 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4608612 prefixEnd_4608612 := by exact prefixLift 4608612
  have htrace : WordTrace (prefixWord ++ tailWord_4608612) baseStart_4608612 baseEnd_4608612 := by
    simpa [prefixWord, tailWord_4608612, baseEnd_4608612] using wordTrace_append hprefix tailTrace_4608612
  have hstable : (prefixWord ++ tailWord_4608612).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4608612).length < 2 ^ (prefixWord ++ tailWord_4608612).sum := by decide
  have hdescent : baseEnd_4608612 < baseStart_4608612 := by decide
  rcases family_descends (prefixWord ++ tailWord_4608612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4608626 : List Nat := [3, 2, 1, 2, 4, 2, 1, 1, 2, 5]
def baseStart_4608626 : Nat := 118140960795 + 4608626 * 2 ^ 59
def prefixEnd_4608626 : Nat := 4983230072969 + 3 ^ 40 * 4608626 * 2
def baseEnd_4608626 : Nat := 788813431602596987760107

theorem tailTrace_4608626 : CollatzResearch.WordTrace tailWord_4608626 prefixEnd_4608626 788813431602596987760107 := by
  unfold tailWord_4608626
  simp only [CollatzResearch.WordTrace]
  refine ⟨42022599850435641875605433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 112060266267828378334947821 42022599850435641875605433)
  ·
    refine ⟨31516949887826731406704075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42022599850435641875605433 31516949887826731406704075)
    ·
      refine ⟨47275424831740097110056113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31516949887826731406704075 47275424831740097110056113)
      ·
        refine ⟨35456568623805072832542085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47275424831740097110056113 35456568623805072832542085)
        ·
          refine ⟨6648106616963451156101641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 35456568623805072832542085 6648106616963451156101641)
          ·
            refine ⟨4986079962722588367076231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6648106616963451156101641 4986079962722588367076231)
            ·
              refine ⟨7479119944083882550614347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4986079962722588367076231 7479119944083882550614347)
              ·
                refine ⟨11218679916125823825921521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7479119944083882550614347 11218679916125823825921521)
                ·
                  refine ⟨8414009937094367869441141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11218679916125823825921521 8414009937094367869441141)
                  ·
                    refine ⟨788813431602596987760107, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8414009937094367869441141 788813431602596987760107)
                    ·
                      rfl

theorem cell23_4608626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 4, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 4, 2, 1, 1, 2, 5].length) (baseStart_4608626 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4608626 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4608626 prefixEnd_4608626 := by exact prefixLift 4608626
  have htrace : WordTrace (prefixWord ++ tailWord_4608626) baseStart_4608626 baseEnd_4608626 := by
    simpa [prefixWord, tailWord_4608626, baseEnd_4608626] using wordTrace_append hprefix tailTrace_4608626
  have hstable : (prefixWord ++ tailWord_4608626).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4608626).length < 2 ^ (prefixWord ++ tailWord_4608626).sum := by decide
  have hdescent : baseEnd_4608626 < baseStart_4608626 := by decide
  rcases family_descends (prefixWord ++ tailWord_4608626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4608632 : List Nat := [2, 1, 2, 1, 1, 1, 2, 5, 1, 4, 3]
def baseStart_4608632 : Nat := 118140960795 + 4608632 * 2 ^ 59
def prefixEnd_4608632 : Nat := 4983230072969 + 3 ^ 40 * 4608632 * 2
def baseEnd_4608632 : Nat := 2366443375691717939805293

theorem tailTrace_4608632 : CollatzResearch.WordTrace tailWord_4608632 prefixEnd_4608632 2366443375691717939805293 := by
  unfold tailWord_4608632
  simp only [CollatzResearch.WordTrace]
  refine ⟨84045309119860415263570075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 112060412159813887018093433 84045309119860415263570075)
  ·
    refine ⟨126067963679790622895355113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84045309119860415263570075 126067963679790622895355113)
    ·
      refine ⟨94550972759842967171516335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 126067963679790622895355113 94550972759842967171516335)
      ·
        refine ⟨141826459139764450757274503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 94550972759842967171516335 141826459139764450757274503)
        ·
          refine ⟨212739688709646676135911755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 141826459139764450757274503 212739688709646676135911755)
          ·
            refine ⟨319109533064470014203867633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 212739688709646676135911755 319109533064470014203867633)
            ·
              refine ⟨239332149798352510652900725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 319109533064470014203867633 239332149798352510652900725)
              ·
                refine ⟨22437389043595547873709443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 239332149798352510652900725 22437389043595547873709443)
                ·
                  refine ⟨33656083565393321810564165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22437389043595547873709443 33656083565393321810564165)
                  ·
                    refine ⟨6310515668511247839480781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 33656083565393321810564165 6310515668511247839480781)
                    ·
                      refine ⟨2366443375691717939805293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6310515668511247839480781 2366443375691717939805293)
                      ·
                        rfl

theorem cell23_4608632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 5, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 5, 1, 4, 3].length) (baseStart_4608632 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4608632 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4608632 prefixEnd_4608632 := by exact prefixLift 4608632
  have htrace : WordTrace (prefixWord ++ tailWord_4608632) baseStart_4608632 baseEnd_4608632 := by
    simpa [prefixWord, tailWord_4608632, baseEnd_4608632] using wordTrace_append hprefix tailTrace_4608632
  have hstable : (prefixWord ++ tailWord_4608632).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4608632).length < 2 ^ (prefixWord ++ tailWord_4608632).sum := by decide
  have hdescent : baseEnd_4608632 < baseStart_4608632 := by decide
  rcases family_descends (prefixWord ++ tailWord_4608632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4608652 : List Nat := [2, 2, 1, 2, 1, 1, 2, 6, 6]
def baseStart_4608652 : Nat := 118140960795 + 4608652 * 2 ^ 59
def prefixEnd_4608652 : Nat := 4983230072969 + 3 ^ 40 * 4608652 * 2
def baseEnd_4608652 : Nat := 262939293922756429061689

theorem tailTrace_4608652 : CollatzResearch.WordTrace tailWord_4608652 prefixEnd_4608652 262939293922756429061689 := by
  unfold tailWord_4608652
  simp only [CollatzResearch.WordTrace]
  refine ⟨84045673849824186971434105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 112060898466432249295245473 84045673849824186971434105)
  ·
    refine ⟨63034255387368140228575579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 84045673849824186971434105 63034255387368140228575579)
    ·
      refine ⟨94551383081052210342863369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63034255387368140228575579 94551383081052210342863369)
      ·
        refine ⟨70913537310789157757147527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 94551383081052210342863369 70913537310789157757147527)
        ·
          refine ⟨106370305966183736635721291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 70913537310789157757147527 106370305966183736635721291)
          ·
            refine ⟨159555458949275604953581937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 106370305966183736635721291 159555458949275604953581937)
            ·
              refine ⟨119666594211956703715186453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 159555458949275604953581937 119666594211956703715186453)
              ·
                refine ⟨5609371603685470486649365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 119666594211956703715186453 5609371603685470486649365)
                ·
                  refine ⟨262939293922756429061689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5609371603685470486649365 262939293922756429061689)
                  ·
                    rfl

theorem cell23_4608652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 2, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 2, 6, 6].length) (baseStart_4608652 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4608652 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4608652 prefixEnd_4608652 := by exact prefixLift 4608652
  have htrace : WordTrace (prefixWord ++ tailWord_4608652) baseStart_4608652 baseEnd_4608652 := by
    simpa [prefixWord, tailWord_4608652, baseEnd_4608652] using wordTrace_append hprefix tailTrace_4608652
  have hstable : (prefixWord ++ tailWord_4608652).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4608652).length < 2 ^ (prefixWord ++ tailWord_4608652).sum := by decide
  have hdescent : baseEnd_4608652 < baseStart_4608652 := by decide
  rcases family_descends (prefixWord ++ tailWord_4608652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4608736 : List Nat := [2, 1, 1, 3, 1, 2, 1, 3, 5, 2, 2]
def baseStart_4608736 : Nat := 118140960795 + 4608736 * 2 ^ 59
def prefixEnd_4608736 : Nat := 4983230072969 + 3 ^ 40 * 4608736 * 2
def baseEnd_4608736 : Nat := 2366496777679785532904815

theorem tailTrace_4608736 : CollatzResearch.WordTrace tailWord_4608736 prefixEnd_4608736 2366496777679785532904815 := by
  unfold tailWord_4608736
  simp only [CollatzResearch.WordTrace]
  refine ⟨84047205715672028144463031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 112062940954229370859284041 84047205715672028144463031)
  ·
    refine ⟨126070808573508042216694547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84047205715672028144463031 126070808573508042216694547)
    ·
      refine ⟨189106212860262063325041821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 126070808573508042216694547 189106212860262063325041821)
      ·
        refine ⟨70914829822598273746890683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 189106212860262063325041821 70914829822598273746890683)
        ·
          refine ⟨106372244733897410620336025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 70914829822598273746890683 106372244733897410620336025)
          ·
            refine ⟨79779183550423057965252019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 106372244733897410620336025 79779183550423057965252019)
            ·
              refine ⟨119668775325634586947878029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 79779183550423057965252019 119668775325634586947878029)
              ·
                refine ⟨44875790747112970105454261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 119668775325634586947878029 44875790747112970105454261)
                ·
                  refine ⟨4207105382541840947386337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 44875790747112970105454261 4207105382541840947386337)
                  ·
                    refine ⟨3155329036906380710539753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4207105382541840947386337 3155329036906380710539753)
                    ·
                      refine ⟨2366496777679785532904815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3155329036906380710539753 2366496777679785532904815)
                      ·
                        rfl

theorem cell23_4608736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 1, 3, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 1, 3, 5, 2, 2].length) (baseStart_4608736 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4608736 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4608736 prefixEnd_4608736 := by exact prefixLift 4608736
  have htrace : WordTrace (prefixWord ++ tailWord_4608736) baseStart_4608736 baseEnd_4608736 := by
    simpa [prefixWord, tailWord_4608736, baseEnd_4608736] using wordTrace_append hprefix tailTrace_4608736
  have hstable : (prefixWord ++ tailWord_4608736).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4608736).length < 2 ^ (prefixWord ++ tailWord_4608736).sum := by decide
  have hdescent : baseEnd_4608736 < baseStart_4608736 := by decide
  rcases family_descends (prefixWord ++ tailWord_4608736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4608769 : List Nat := [1, 2, 4, 1, 1, 1, 1, 1, 5, 3, 3]
def baseStart_4608769 : Nat := 118140960795 + 4608769 * 2 ^ 59
def prefixEnd_4608769 : Nat := 4983230072969 + 3 ^ 40 * 4608769 * 2
def baseEnd_4608769 : Nat := 2366513722541383903792163

theorem tailTrace_4608769 : CollatzResearch.WordTrace tailWord_4608769 prefixEnd_4608769 2366513722541383903792163 := by
  unfold tailWord_4608769
  simp only [CollatzResearch.WordTrace]
  refine ⟨168095615040224502924877361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112063743360149668616584907 168095615040224502924877361)
  ·
    refine ⟨126071711280168377193658021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 168095615040224502924877361 126071711280168377193658021)
    ·
      refine ⟨23638445865031570723810879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 126071711280168377193658021 23638445865031570723810879)
      ·
        refine ⟨35457668797547356085716319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23638445865031570723810879 35457668797547356085716319)
        ·
          refine ⟨53186503196321034128574479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35457668797547356085716319 53186503196321034128574479)
          ·
            refine ⟨79779754794481551192861719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53186503196321034128574479 79779754794481551192861719)
            ·
              refine ⟨119669632191722326789292579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 79779754794481551192861719 119669632191722326789292579)
              ·
                refine ⟨179504448287583490183938869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 119669632191722326789292579 179504448287583490183938869)
                ·
                  refine ⟨16828542026960952204744269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 179504448287583490183938869 16828542026960952204744269)
                  ·
                    refine ⟨6310703260110357076779101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16828542026960952204744269 6310703260110357076779101)
                    ·
                      refine ⟨2366513722541383903792163, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6310703260110357076779101 2366513722541383903792163)
                      ·
                        rfl

theorem cell23_4608769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 1, 1, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 1, 1, 5, 3, 3].length) (baseStart_4608769 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4608769 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4608769 prefixEnd_4608769 := by exact prefixLift 4608769
  have htrace : WordTrace (prefixWord ++ tailWord_4608769) baseStart_4608769 baseEnd_4608769 := by
    simpa [prefixWord, tailWord_4608769, baseEnd_4608769] using wordTrace_append hprefix tailTrace_4608769
  have hstable : (prefixWord ++ tailWord_4608769).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4608769).length < 2 ^ (prefixWord ++ tailWord_4608769).sum := by decide
  have hdescent : baseEnd_4608769 < baseStart_4608769 := by decide
  rcases family_descends (prefixWord ++ tailWord_4608769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4608819 : List Nat := [1, 1, 1, 2, 6, 1, 1, 2, 2, 6]
def baseStart_4608819 : Nat := 118140960795 + 4608819 * 2 ^ 59
def prefixEnd_4608819 : Nat := 4983230072969 + 3 ^ 40 * 4608819 * 2
def baseEnd_4608819 : Nat := 788846465524702902722311

theorem tailTrace_4608819 : CollatzResearch.WordTrace tailWord_4608819 prefixEnd_4608819 788846465524702902722311 := by
  unfold tailWord_4608819
  simp only [CollatzResearch.WordTrace]
  refine ⟨168097438690043361464197511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112064959126695574309465007 168097438690043361464197511)
  ·
    refine ⟨252146158035065042196296267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 168097438690043361464197511 252146158035065042196296267)
    ·
      refine ⟨378219237052597563294444401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 252146158035065042196296267 378219237052597563294444401)
      ·
        refine ⟨283664427789448172470833301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 378219237052597563294444401 283664427789448172470833301)
        ·
          refine ⟨13296770052630383084570311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 283664427789448172470833301 13296770052630383084570311)
          ·
            refine ⟨19945155078945574626855467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13296770052630383084570311 19945155078945574626855467)
            ·
              refine ⟨29917732618418361940283201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19945155078945574626855467 29917732618418361940283201)
              ·
                refine ⟨22438299463813771455212401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29917732618418361940283201 22438299463813771455212401)
                ·
                  refine ⟨16828724597860328591409301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22438299463813771455212401 16828724597860328591409301)
                  ·
                    refine ⟨788846465524702902722311, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16828724597860328591409301 788846465524702902722311)
                    ·
                      rfl

theorem cell23_4608819_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 1, 2, 2, 6].length) (baseStart_4608819 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4608819 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4608819 prefixEnd_4608819 := by exact prefixLift 4608819
  have htrace : WordTrace (prefixWord ++ tailWord_4608819) baseStart_4608819 baseEnd_4608819 := by
    simpa [prefixWord, tailWord_4608819, baseEnd_4608819] using wordTrace_append hprefix tailTrace_4608819
  have hstable : (prefixWord ++ tailWord_4608819).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4608819).length < 2 ^ (prefixWord ++ tailWord_4608819).sum := by decide
  have hdescent : baseEnd_4608819 < baseStart_4608819 := by decide
  rcases family_descends (prefixWord ++ tailWord_4608819) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4608820 : List Nat := [2, 5, 1, 1, 3, 1, 1, 1, 4, 1, 3]
def baseStart_4608820 : Nat := 118140960795 + 4608820 * 2 ^ 59
def prefixEnd_4608820 : Nat := 4983230072969 + 3 ^ 40 * 4608820 * 2
def baseEnd_4608820 : Nat := 2366539910054763204254429

theorem tailTrace_4608820 : CollatzResearch.WordTrace tailWord_4608820 prefixEnd_4608820 2366539910054763204254429 := by
  unfold tailWord_4608820
  simp only [CollatzResearch.WordTrace]
  refine ⟨84048737581519869317491957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 112064983442026492423322609 84048737581519869317491957)
  ·
    refine ⟨7879569148267487748514871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 84048737581519869317491957 7879569148267487748514871)
    ·
      refine ⟨11819353722401231622772307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7879569148267487748514871 11819353722401231622772307)
      ·
        refine ⟨17729030583601847434158461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11819353722401231622772307 17729030583601847434158461)
        ·
          refine ⟨6648386468850692787809423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17729030583601847434158461 6648386468850692787809423)
          ·
            refine ⟨9972579703276039181714135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6648386468850692787809423 9972579703276039181714135)
            ·
              refine ⟨14958869554914058772571203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9972579703276039181714135 14958869554914058772571203)
              ·
                refine ⟨22438304332371088158856805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14958869554914058772571203 22438304332371088158856805)
                ·
                  refine ⟨4207182062319579029785651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 22438304332371088158856805 4207182062319579029785651)
                  ·
                    refine ⟨6310773093479368544678477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4207182062319579029785651 6310773093479368544678477)
                    ·
                      refine ⟨2366539910054763204254429, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6310773093479368544678477 2366539910054763204254429)
                      ·
                        rfl

theorem cell23_4608820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 3, 1, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 3, 1, 1, 1, 4, 1, 3].length) (baseStart_4608820 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4608820 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4608820 prefixEnd_4608820 := by exact prefixLift 4608820
  have htrace : WordTrace (prefixWord ++ tailWord_4608820) baseStart_4608820 baseEnd_4608820 := by
    simpa [prefixWord, tailWord_4608820, baseEnd_4608820] using wordTrace_append hprefix tailTrace_4608820
  have hstable : (prefixWord ++ tailWord_4608820).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4608820).length < 2 ^ (prefixWord ++ tailWord_4608820).sum := by decide
  have hdescent : baseEnd_4608820 < baseStart_4608820 := by decide
  rcases family_descends (prefixWord ++ tailWord_4608820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4608860 : List Nat := [2, 2, 4, 2, 1, 1, 1, 2, 4, 2, 2]
def baseStart_4608860 : Nat := 118140960795 + 4608860 * 2 ^ 59
def prefixEnd_4608860 : Nat := 4983230072969 + 3 ^ 40 * 4608860 * 2
def baseEnd_4608860 : Nat := 2366560449280943047754245

theorem tailTrace_4608860 : CollatzResearch.WordTrace tailWord_4608860 prefixEnd_4608860 2366560449280943047754245 := by
  unfold tailWord_4608860
  simp only [CollatzResearch.WordTrace]
  refine ⟨84049467041447412733220017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 112065956055263216977626689 84049467041447412733220017)
  ·
    refine ⟨63037100281085559549915013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 84049467041447412733220017 63037100281085559549915013)
    ·
      refine ⟨11819456302703542415609065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 63037100281085559549915013 11819456302703542415609065)
      ·
        refine ⟨8864592227027656811706799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11819456302703542415609065 8864592227027656811706799)
        ·
          refine ⟨13296888340541485217560199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8864592227027656811706799 13296888340541485217560199)
          ·
            refine ⟨19945332510812227826340299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13296888340541485217560199 19945332510812227826340299)
            ·
              refine ⟨29917998766218341739510449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19945332510812227826340299 29917998766218341739510449)
              ·
                refine ⟨22438499074663756304632837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29917998766218341739510449 22438499074663756304632837)
                ·
                  refine ⟨4207218576499454307118657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 22438499074663756304632837 4207218576499454307118657)
                  ·
                    refine ⟨3155413932374590730338993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4207218576499454307118657 3155413932374590730338993)
                    ·
                      refine ⟨2366560449280943047754245, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3155413932374590730338993 2366560449280943047754245)
                      ·
                        rfl

theorem cell23_4608860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 1, 2, 4, 2, 2].length) (baseStart_4608860 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4608860 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4608860 prefixEnd_4608860 := by exact prefixLift 4608860
  have htrace : WordTrace (prefixWord ++ tailWord_4608860) baseStart_4608860 baseEnd_4608860 := by
    simpa [prefixWord, tailWord_4608860, baseEnd_4608860] using wordTrace_append hprefix tailTrace_4608860
  have hstable : (prefixWord ++ tailWord_4608860).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4608860).length < 2 ^ (prefixWord ++ tailWord_4608860).sum := by decide
  have hdescent : baseEnd_4608860 < baseStart_4608860 := by decide
  rcases family_descends (prefixWord ++ tailWord_4608860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4608889 : List Nat := [1, 2, 1, 3, 2, 3, 1, 1, 1, 1, 7]
def baseStart_4608889 : Nat := 118140960795 + 4608889 * 2 ^ 59
def prefixEnd_4608889 : Nat := 4983230072969 + 3 ^ 40 * 4608889 * 2
def baseEnd_4608889 : Nat := 2366575340219923434291611

theorem tailTrace_4608889 : CollatzResearch.WordTrace tailWord_4608889 prefixEnd_4608889 2366575340219923434291611 := by
  unfold tailWord_4608889
  simp only [CollatzResearch.WordTrace]
  refine ⟨168099991799789763419245721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112066661199859842279497147 168099991799789763419245721)
  ·
    refine ⟨126074993849842322564434291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 168099991799789763419245721 126074993849842322564434291)
    ·
      refine ⟨189112490774763483846651437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 126074993849842322564434291 189112490774763483846651437)
      ·
        refine ⟨70917184040536306442494289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 189112490774763483846651437 70917184040536306442494289)
        ·
          refine ⟨53187888030402229831870717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 70917184040536306442494289 53187888030402229831870717)
          ·
            refine ⟨19945458011400836186951519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 53187888030402229831870717 19945458011400836186951519)
            ·
              refine ⟨29918187017101254280427279, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19945458011400836186951519 29918187017101254280427279)
              ·
                refine ⟨44877280525651881420640919, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29918187017101254280427279 44877280525651881420640919)
                ·
                  refine ⟨67315920788477822130961379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 44877280525651881420640919 67315920788477822130961379)
                  ·
                    refine ⟨100973881182716733196442069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 67315920788477822130961379 100973881182716733196442069)
                    ·
                      refine ⟨2366575340219923434291611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 100973881182716733196442069 2366575340219923434291611)
                      ·
                        rfl

theorem cell23_4608889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 1, 1, 1, 1, 7].length) (baseStart_4608889 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4608889 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4608889 prefixEnd_4608889 := by exact prefixLift 4608889
  have htrace : WordTrace (prefixWord ++ tailWord_4608889) baseStart_4608889 baseEnd_4608889 := by
    simpa [prefixWord, tailWord_4608889, baseEnd_4608889] using wordTrace_append hprefix tailTrace_4608889
  have hstable : (prefixWord ++ tailWord_4608889).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4608889).length < 2 ^ (prefixWord ++ tailWord_4608889).sum := by decide
  have hdescent : baseEnd_4608889 < baseStart_4608889 := by decide
  rcases family_descends (prefixWord ++ tailWord_4608889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4608894 : List Nat := [4, 2, 3, 1, 2, 1, 1, 3, 2, 2, 2]
def baseStart_4608894 : Nat := 118140960795 + 4608894 * 2 ^ 59
def prefixEnd_4608894 : Nat := 4983230072969 + 3 ^ 40 * 4608894 * 2
def baseEnd_4608894 : Nat := 2366577907623195914729089

theorem tailTrace_4608894 : CollatzResearch.WordTrace tailWord_4608894 prefixEnd_4608894 2366577907623195914729089 := by
  unfold tailWord_4608894
  simp only [CollatzResearch.WordTrace]
  refine ⟨21012521770596456159147217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 112066782776514432848785157 21012521770596456159147217)
  ·
    refine ⟨15759391327947342119360413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21012521770596456159147217 15759391327947342119360413)
    ·
      refine ⟨5909771747980253294760155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15759391327947342119360413 5909771747980253294760155)
      ·
        refine ⟨8864657621970379942140233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5909771747980253294760155 8864657621970379942140233)
        ·
          refine ⟨6648493216477784956605175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8864657621970379942140233 6648493216477784956605175)
          ·
            refine ⟨9972739824716677434907763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6648493216477784956605175 9972739824716677434907763)
            ·
              refine ⟨14959109737075016152361645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9972739824716677434907763 14959109737075016152361645)
              ·
                refine ⟨5609666151403131057135617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14959109737075016152361645 5609666151403131057135617)
                ·
                  refine ⟨4207249613552348292851713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5609666151403131057135617 4207249613552348292851713)
                  ·
                    refine ⟨3155437210164261219638785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4207249613552348292851713 3155437210164261219638785)
                    ·
                      refine ⟨2366577907623195914729089, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3155437210164261219638785 2366577907623195914729089)
                      ·
                        rfl

theorem cell23_4608894_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 2, 1, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 2, 1, 1, 3, 2, 2, 2].length) (baseStart_4608894 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4608894 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4608894 prefixEnd_4608894 := by exact prefixLift 4608894
  have htrace : WordTrace (prefixWord ++ tailWord_4608894) baseStart_4608894 baseEnd_4608894 := by
    simpa [prefixWord, tailWord_4608894, baseEnd_4608894] using wordTrace_append hprefix tailTrace_4608894
  have hstable : (prefixWord ++ tailWord_4608894).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4608894).length < 2 ^ (prefixWord ++ tailWord_4608894).sum := by decide
  have hdescent : baseEnd_4608894 < baseStart_4608894 := by decide
  rcases family_descends (prefixWord ++ tailWord_4608894) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4608959 : List Nat := [1, 1, 2, 2, 2, 1, 2, 1, 3, 2, 6]
def baseStart_4608959 : Nat := 118140960795 + 4608959 * 2 ^ 59
def prefixEnd_4608959 : Nat := 4983230072969 + 3 ^ 40 * 4608959 * 2
def baseEnd_4608959 : Nat := 2366611283865738160416289

theorem tailTrace_4608959 : CollatzResearch.WordTrace tailWord_4608959 prefixEnd_4608959 2366611283865738160416289 := by
  unfold tailWord_4608959
  simp only [CollatzResearch.WordTrace]
  refine ⟨168102544909536165374293931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112068363273024110249529287 168102544909536165374293931)
  ·
    refine ⟨252153817364304248061440897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 168102544909536165374293931 252153817364304248061440897)
    ·
      refine ⟨189115363023228186046080673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 252153817364304248061440897 189115363023228186046080673)
      ·
        refine ⟨141836522267421139534560505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 189115363023228186046080673 141836522267421139534560505)
        ·
          refine ⟨106377391700565854650920379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 141836522267421139534560505 106377391700565854650920379)
          ·
            refine ⟨159566087550848781976380569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 106377391700565854650920379 159566087550848781976380569)
            ·
              refine ⟨119674565663136586482285427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 159566087550848781976380569 119674565663136586482285427)
              ·
                refine ⟨179511848494704879723428141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 119674565663136586482285427 179511848494704879723428141)
                ·
                  refine ⟨67316943185514329896285553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 179511848494704879723428141 67316943185514329896285553)
                  ·
                    refine ⟨50487707389135747422214165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 67316943185514329896285553 50487707389135747422214165)
                    ·
                      refine ⟨2366611283865738160416289, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 50487707389135747422214165 2366611283865738160416289)
                      ·
                        rfl

theorem cell23_4608959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 2, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 2, 1, 3, 2, 6].length) (baseStart_4608959 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4608959 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4608959 prefixEnd_4608959 := by exact prefixLift 4608959
  have htrace : WordTrace (prefixWord ++ tailWord_4608959) baseStart_4608959 baseEnd_4608959 := by
    simpa [prefixWord, tailWord_4608959, baseEnd_4608959] using wordTrace_append hprefix tailTrace_4608959
  have hstable : (prefixWord ++ tailWord_4608959).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4608959).length < 2 ^ (prefixWord ++ tailWord_4608959).sum := by decide
  have hdescent : baseEnd_4608959 < baseStart_4608959 := by decide
  rcases family_descends (prefixWord ++ tailWord_4608959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4608993 : List Nat := [1, 2, 3, 1, 2, 1, 1, 3, 4, 3, 2]
def baseStart_4608993 : Nat := 118140960795 + 4608993 * 2 ^ 59
def prefixEnd_4608993 : Nat := 4983230072969 + 3 ^ 40 * 4608993 * 2
def baseEnd_4608993 : Nat := 2366628742207991027391133

theorem tailTrace_4608993 : CollatzResearch.WordTrace tailWord_4608993 prefixEnd_4608993 2366628742207991027391133 := by
  unfold tailWord_4608993
  simp only [CollatzResearch.WordTrace]
  refine ⟨168103784991412989181031633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112069189994275326120687755 168103784991412989181031633)
  ·
    refine ⟨126077838743559741885773725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 168103784991412989181031633 126077838743559741885773725)
    ·
      refine ⟨47279189528834903207165147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 126077838743559741885773725 47279189528834903207165147)
      ·
        refine ⟨70918784293252354810747721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47279189528834903207165147 70918784293252354810747721)
        ·
          refine ⟨53189088219939266108060791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 70918784293252354810747721 53189088219939266108060791)
          ·
            refine ⟨79783632329908899162091187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53189088219939266108060791 79783632329908899162091187)
            ·
              refine ⟨119675448494863348743136781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 79783632329908899162091187 119675448494863348743136781)
              ·
                refine ⟨44878293185573755778676293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 119675448494863348743136781 44878293185573755778676293)
                ·
                  refine ⟨8414679972295079208501805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 44878293185573755778676293 8414679972295079208501805)
                  ·
                    refine ⟨3155504989610654703188177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8414679972295079208501805 3155504989610654703188177)
                    ·
                      refine ⟨2366628742207991027391133, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3155504989610654703188177 2366628742207991027391133)
                      ·
                        rfl

theorem cell23_4608993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 1, 3, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 1, 3, 4, 3, 2].length) (baseStart_4608993 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4608993 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4608993 prefixEnd_4608993 := by exact prefixLift 4608993
  have htrace : WordTrace (prefixWord ++ tailWord_4608993) baseStart_4608993 baseEnd_4608993 := by
    simpa [prefixWord, tailWord_4608993, baseEnd_4608993] using wordTrace_append hprefix tailTrace_4608993
  have hstable : (prefixWord ++ tailWord_4608993).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4608993).length < 2 ^ (prefixWord ++ tailWord_4608993).sum := by decide
  have hdescent : baseEnd_4608993 < baseStart_4608993 := by decide
  rcases family_descends (prefixWord ++ tailWord_4608993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4609034 : List Nat := [3, 1, 2, 2, 3, 3, 1, 3, 1, 1, 3]
def baseStart_4609034 : Nat := 118140960795 + 4609034 * 2 ^ 59
def prefixEnd_4609034 : Nat := 4983230072969 + 3 ^ 40 * 4609034 * 2
def baseEnd_4609034 : Nat := 2366649794914825366978445

theorem tailTrace_4609034 : CollatzResearch.WordTrace tailWord_4609034 prefixEnd_4609034 2366649794914825366978445 := by
  unfold tailWord_4609034
  simp only [CollatzResearch.WordTrace]
  refine ⟨42026320096066113295818539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 112070186922842968788849437 42026320096066113295818539)
  ·
    refine ⟨63039480144099169943727809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42026320096066113295818539 63039480144099169943727809)
    ·
      refine ⟨47279610108074377457795857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 63039480144099169943727809 47279610108074377457795857)
      ·
        refine ⟨35459707581055783093346893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47279610108074377457795857 35459707581055783093346893)
        ·
          refine ⟨13297390342895918660005085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 35459707581055783093346893 13297390342895918660005085)
          ·
            refine ⟨4986521378585969497501907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13297390342895918660005085 4986521378585969497501907)
            ·
              refine ⟨7479782067878954246252861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4986521378585969497501907 7479782067878954246252861)
              ·
                refine ⟨2804918275454607842344823, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7479782067878954246252861 2804918275454607842344823)
                ·
                  refine ⟨4207377413181911763517235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2804918275454607842344823 4207377413181911763517235)
                  ·
                    refine ⟨6311066119772867645275853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4207377413181911763517235 6311066119772867645275853)
                    ·
                      refine ⟨2366649794914825366978445, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6311066119772867645275853 2366649794914825366978445)
                      ·
                        rfl

theorem cell23_4609034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 3, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 3, 1, 3, 1, 1, 3].length) (baseStart_4609034 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4609034 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4609034 prefixEnd_4609034 := by exact prefixLift 4609034
  have htrace : WordTrace (prefixWord ++ tailWord_4609034) baseStart_4609034 baseEnd_4609034 := by
    simpa [prefixWord, tailWord_4609034, baseEnd_4609034] using wordTrace_append hprefix tailTrace_4609034
  have hstable : (prefixWord ++ tailWord_4609034).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4609034).length < 2 ^ (prefixWord ++ tailWord_4609034).sum := by decide
  have hdescent : baseEnd_4609034 < baseStart_4609034 := by decide
  rcases family_descends (prefixWord ++ tailWord_4609034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4609057 : List Nat := [1, 2, 3, 2, 3, 1, 3, 1, 3, 2, 2]
def baseStart_4609057 : Nat := 118140960795 + 4609057 * 2 ^ 59
def prefixEnd_4609057 : Nat := 4983230072969 + 3 ^ 40 * 4609057 * 2
def baseEnd_4609057 : Nat := 2366661604969878776990839

theorem tailTrace_4609057 : CollatzResearch.WordTrace tailWord_4609057 prefixEnd_4609057 2366661604969878776990839 := by
  unfold tailWord_4609057
  simp only [CollatzResearch.WordTrace]
  refine ⟨168106119263181128111361425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112070746175454085407574283 168106119263181128111361425)
  ·
    refine ⟨126079589447385846083521069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 168106119263181128111361425 126079589447385846083521069)
    ·
      refine ⟨47279846042769692281320401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 126079589447385846083521069 47279846042769692281320401)
      ·
        refine ⟨35459884532077269210990301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47279846042769692281320401 35459884532077269210990301)
        ·
          refine ⟨13297456699528975954121363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 35459884532077269210990301 13297456699528975954121363)
          ·
            refine ⟨19946185049293463931182045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13297456699528975954121363 19946185049293463931182045)
            ·
              refine ⟨7479819393485048974193267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19946185049293463931182045 7479819393485048974193267)
              ·
                refine ⟨11219729090227573461289901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7479819393485048974193267 11219729090227573461289901)
                ·
                  refine ⟨4207398408835340047983713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11219729090227573461289901 4207398408835340047983713)
                  ·
                    refine ⟨3155548806626505035987785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4207398408835340047983713 3155548806626505035987785)
                    ·
                      refine ⟨2366661604969878776990839, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3155548806626505035987785 2366661604969878776990839)
                      ·
                        rfl

theorem cell23_4609057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 3, 1, 3, 2, 2].length) (baseStart_4609057 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4609057 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4609057 prefixEnd_4609057 := by exact prefixLift 4609057
  have htrace : WordTrace (prefixWord ++ tailWord_4609057) baseStart_4609057 baseEnd_4609057 := by
    simpa [prefixWord, tailWord_4609057, baseEnd_4609057] using wordTrace_append hprefix tailTrace_4609057
  have hstable : (prefixWord ++ tailWord_4609057).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4609057).length < 2 ^ (prefixWord ++ tailWord_4609057).sum := by decide
  have hdescent : baseEnd_4609057 < baseStart_4609057 := by decide
  rcases family_descends (prefixWord ++ tailWord_4609057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4609063 : List Nat := [1, 1, 7, 1, 1, 1, 1, 10]
def baseStart_4609063 : Nat := 118140960795 + 4609063 * 2 ^ 59
def prefixEnd_4609063 : Nat := 4983230072969 + 3 ^ 40 * 4609063 * 2
def baseEnd_4609063 : Nat := 87654247624215027907993

theorem tailTrace_4609063 : CollatzResearch.WordTrace tailWord_4609063 prefixEnd_4609063 87654247624215027907993 := by
  unfold tailWord_4609063
  simp only [CollatzResearch.WordTrace]
  refine ⟨168106338101159391136079843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112070892067439594090719895 168106338101159391136079843)
  ·
    refine ⟨252159507151739086704119765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 168106338101159391136079843 252159507151739086704119765)
    ·
      refine ⟨5909988448868884844627807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 252159507151739086704119765 5909988448868884844627807)
      ·
        refine ⟨8864982673303327266941711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5909988448868884844627807 8864982673303327266941711)
        ·
          refine ⟨13297474009954990900412567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8864982673303327266941711 13297474009954990900412567)
          ·
            refine ⟨19946211014932486350618851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13297474009954990900412567 19946211014932486350618851)
            ·
              refine ⟨29919316522398729525928277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19946211014932486350618851 29919316522398729525928277)
              ·
                refine ⟨87654247624215027907993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 29919316522398729525928277 87654247624215027907993)
                ·
                  rfl

theorem cell23_4609063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 1, 10].length) (baseStart_4609063 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4609063 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4609063 prefixEnd_4609063 := by exact prefixLift 4609063
  have htrace : WordTrace (prefixWord ++ tailWord_4609063) baseStart_4609063 baseEnd_4609063 := by
    simpa [prefixWord, tailWord_4609063, baseEnd_4609063] using wordTrace_append hprefix tailTrace_4609063
  have hstable : (prefixWord ++ tailWord_4609063).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4609063).length < 2 ^ (prefixWord ++ tailWord_4609063).sum := by decide
  have hdescent : baseEnd_4609063 < baseStart_4609063 := by decide
  rcases family_descends (prefixWord ++ tailWord_4609063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4609073 : List Nat := [1, 2, 2, 3, 1, 2, 2, 3, 1, 3, 3]
def baseStart_4609073 : Nat := 118140960795 + 4609073 * 2 ^ 59
def prefixEnd_4609073 : Nat := 4983230072969 + 3 ^ 40 * 4609073 * 2
def baseEnd_4609073 : Nat := 2366669820660350714390765

theorem tailTrace_4609073 : CollatzResearch.WordTrace tailWord_4609073 prefixEnd_4609073 2366669820660350714390765 := by
  unfold tailWord_4609073
  simp only [CollatzResearch.WordTrace]
  refine ⟨168106702831123162843943873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112071135220748775229295915 168106702831123162843943873)
  ·
    refine ⟨126080027123342372132957905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 168106702831123162843943873 126080027123342372132957905)
    ·
      refine ⟨94560020342506779099718429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 126080027123342372132957905 94560020342506779099718429)
      ·
        refine ⟨35460007628440042162394411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 94560020342506779099718429 35460007628440042162394411)
        ·
          refine ⟨53190011442660063243591617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35460007628440042162394411 53190011442660063243591617)
          ·
            refine ⟨39892508581995047432693713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 53190011442660063243591617 39892508581995047432693713)
            ·
              refine ⟨29919381436496285574520285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 39892508581995047432693713 29919381436496285574520285)
              ·
                refine ⟨11219768038686107090445107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 29919381436496285574520285 11219768038686107090445107)
                ·
                  refine ⟨16829652058029160635667661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11219768038686107090445107 16829652058029160635667661)
                  ·
                    refine ⟨6311119521760935238375373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16829652058029160635667661 6311119521760935238375373)
                    ·
                      refine ⟨2366669820660350714390765, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6311119521760935238375373 2366669820660350714390765)
                      ·
                        rfl

theorem cell23_4609073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 2, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 2, 3, 1, 3, 3].length) (baseStart_4609073 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4609073 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4609073 prefixEnd_4609073 := by exact prefixLift 4609073
  have htrace : WordTrace (prefixWord ++ tailWord_4609073) baseStart_4609073 baseEnd_4609073 := by
    simpa [prefixWord, tailWord_4609073, baseEnd_4609073] using wordTrace_append hprefix tailTrace_4609073
  have hstable : (prefixWord ++ tailWord_4609073).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4609073).length < 2 ^ (prefixWord ++ tailWord_4609073).sum := by decide
  have hdescent : baseEnd_4609073 < baseStart_4609073 := by decide
  rcases family_descends (prefixWord ++ tailWord_4609073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4609170 : List Nat := [3, 2, 3, 1, 1, 3, 2, 1, 7]
def baseStart_4609170 : Nat := 118140960795 + 4609170 * 2 ^ 59
def prefixEnd_4609170 : Nat := 4983230072969 + 3 ^ 40 * 4609170 * 2
def baseEnd_4609170 : Nat := 262968847587092981653091

theorem tailTrace_4609170 : CollatzResearch.WordTrace tailWord_4609170 prefixEnd_4609170 262968847587092981653091 := by
  unfold tailWord_4609170
  simp only [CollatzResearch.WordTrace]
  refine ⟨42027560177942937102556241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 112073493807847832273483309 42027560177942937102556241)
  ·
    refine ⟨31520670133457202826917181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42027560177942937102556241 31520670133457202826917181)
    ·
      refine ⟨11820251300046451060093943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31520670133457202826917181 11820251300046451060093943)
      ·
        refine ⟨17730376950069676590140915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11820251300046451060093943 17730376950069676590140915)
        ·
          refine ⟨26595565425104514885211373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17730376950069676590140915 26595565425104514885211373)
          ·
            refine ⟨9973337034414193081954265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26595565425104514885211373 9973337034414193081954265)
            ·
              refine ⟨7480002775810644811465699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9973337034414193081954265 7480002775810644811465699)
              ·
                refine ⟨11220004163715967217198549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7480002775810644811465699 11220004163715967217198549)
                ·
                  refine ⟨262968847587092981653091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11220004163715967217198549 262968847587092981653091)
                  ·
                    rfl

theorem cell23_4609170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 3, 2, 1, 7].length) (baseStart_4609170 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4609170 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4609170 prefixEnd_4609170 := by exact prefixLift 4609170
  have htrace : WordTrace (prefixWord ++ tailWord_4609170) baseStart_4609170 baseEnd_4609170 := by
    simpa [prefixWord, tailWord_4609170, baseEnd_4609170] using wordTrace_append hprefix tailTrace_4609170
  have hstable : (prefixWord ++ tailWord_4609170).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4609170).length < 2 ^ (prefixWord ++ tailWord_4609170).sum := by decide
  have hdescent : baseEnd_4609170 < baseStart_4609170 := by decide
  rcases family_descends (prefixWord ++ tailWord_4609170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4609180 : List Nat := [2, 2, 3, 2, 1, 2, 2, 1, 2, 3, 3]
def baseStart_4609180 : Nat := 118140960795 + 4609180 * 2 ^ 59
def prefixEnd_4609180 : Nat := 4983230072969 + 3 ^ 40 * 4609180 * 2
def baseEnd_4609180 : Nat := 2366724763090381795752773

theorem tailTrace_4609180 : CollatzResearch.WordTrace tailWord_4609180 prefixEnd_4609180 2366724763090381795752773 := by
  unfold tailWord_4609180
  simp only [CollatzResearch.WordTrace]
  refine ⟨84055302720867760059044497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 112073736961157013412059329 84055302720867760059044497)
  ·
    refine ⟨63041477040650820044283373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 84055302720867760059044497 63041477040650820044283373)
    ·
      refine ⟨23640553890244057516606265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 63041477040650820044283373 23640553890244057516606265)
      ·
        refine ⟨17730415417683043137454699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23640553890244057516606265 17730415417683043137454699)
        ·
          refine ⟨26595623126524564706182049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17730415417683043137454699 26595623126524564706182049)
          ·
            refine ⟨19946717344893423529636537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26595623126524564706182049 19946717344893423529636537)
            ·
              refine ⟨14960038008670067647227403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19946717344893423529636537 14960038008670067647227403)
              ·
                refine ⟨22440057013005101470841105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14960038008670067647227403 22440057013005101470841105)
                ·
                  refine ⟨16830042759753826103130829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22440057013005101470841105 16830042759753826103130829)
                  ·
                    refine ⟨6311266034907684788674061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16830042759753826103130829 6311266034907684788674061)
                    ·
                      refine ⟨2366724763090381795752773, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6311266034907684788674061 2366724763090381795752773)
                      ·
                        rfl

theorem cell23_4609180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 2, 1, 2, 3, 3].length) (baseStart_4609180 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4609180 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4609180 prefixEnd_4609180 := by exact prefixLift 4609180
  have htrace : WordTrace (prefixWord ++ tailWord_4609180) baseStart_4609180 baseEnd_4609180 := by
    simpa [prefixWord, tailWord_4609180, baseEnd_4609180] using wordTrace_append hprefix tailTrace_4609180
  have hstable : (prefixWord ++ tailWord_4609180).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4609180).length < 2 ^ (prefixWord ++ tailWord_4609180).sum := by decide
  have hdescent : baseEnd_4609180 < baseStart_4609180 := by decide
  rcases family_descends (prefixWord ++ tailWord_4609180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4609203 : List Nat := [1, 1, 1, 2, 3, 2, 4, 1, 1, 3, 4]
def baseStart_4609203 : Nat := 118140960795 + 4609203 * 2 ^ 59
def prefixEnd_4609203 : Nat := 4983230072969 + 3 ^ 40 * 4609203 * 2
def baseEnd_4609203 : Nat := 2366736573145435205765167

theorem tailTrace_4609203 : CollatzResearch.WordTrace tailWord_4609203 prefixEnd_4609203 2366736573145435205765167 := by
  unfold tailWord_4609203
  simp only [CollatzResearch.WordTrace]
  refine ⟨168111444320652195046176263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112074296213768130030784175 168111444320652195046176263)
  ·
    refine ⟨252167166480978292569264395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 168111444320652195046176263 252167166480978292569264395)
    ·
      refine ⟨378250749721467438853896593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 252167166480978292569264395 378250749721467438853896593)
      ·
        refine ⟨283688062291100579140422445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 378250749721467438853896593 283688062291100579140422445)
        ·
          refine ⟨106383023359162717177658417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 283688062291100579140422445 106383023359162717177658417)
          ·
            refine ⟨79787267519372037883243813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 106383023359162717177658417 79787267519372037883243813)
            ·
              refine ⟨14960112659882257103108215, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 79787267519372037883243813 14960112659882257103108215)
              ·
                refine ⟨22440168989823385654662323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14960112659882257103108215 22440168989823385654662323)
                ·
                  refine ⟨33660253484735078481993485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22440168989823385654662323 33660253484735078481993485)
                  ·
                    refine ⟨12622595056775654430747557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 33660253484735078481993485 12622595056775654430747557)
                    ·
                      refine ⟨2366736573145435205765167, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12622595056775654430747557 2366736573145435205765167)
                      ·
                        rfl

theorem cell23_4609203_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 4, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 4, 1, 1, 3, 4].length) (baseStart_4609203 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4609203 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4609203 prefixEnd_4609203 := by exact prefixLift 4609203
  have htrace : WordTrace (prefixWord ++ tailWord_4609203) baseStart_4609203 baseEnd_4609203 := by
    simpa [prefixWord, tailWord_4609203, baseEnd_4609203] using wordTrace_append hprefix tailTrace_4609203
  have hstable : (prefixWord ++ tailWord_4609203).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4609203).length < 2 ^ (prefixWord ++ tailWord_4609203).sum := by decide
  have hdescent : baseEnd_4609203 < baseStart_4609203 := by decide
  rcases family_descends (prefixWord ++ tailWord_4609203) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4609217 : List Nat := [1, 2, 6, 1, 1, 2, 1, 2, 2, 5]
def baseStart_4609217 : Nat := 118140960795 + 4609217 * 2 ^ 59
def prefixEnd_4609217 : Nat := 4983230072969 + 3 ^ 40 * 4609217 * 2
def baseEnd_4609217 : Nat := 788914587291532716996701

theorem tailTrace_4609217 : CollatzResearch.WordTrace tailWord_4609217 prefixEnd_4609217 788914587291532716996701 := by
  unfold tailWord_4609217
  simp only [CollatzResearch.WordTrace]
  refine ⟨168111954942601475437185905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112074636628400983624790603 168111954942601475437185905)
  ·
    refine ⟨126083966206951106577889429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 168111954942601475437185905 126083966206951106577889429)
    ·
      refine ⟨5910185915950833120838567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 126083966206951106577889429 5910185915950833120838567)
      ·
        refine ⟨8865278873926249681257851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5910185915950833120838567 8865278873926249681257851)
        ·
          refine ⟨13297918310889374521886777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8865278873926249681257851 13297918310889374521886777)
          ·
            refine ⟨9973438733167030891415083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13297918310889374521886777 9973438733167030891415083)
            ·
              refine ⟨14960158099750546337122625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9973438733167030891415083 14960158099750546337122625)
              ·
                refine ⟨11220118574812909752841969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14960158099750546337122625 11220118574812909752841969)
                ·
                  refine ⟨8415088931109682314631477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11220118574812909752841969 8415088931109682314631477)
                  ·
                    refine ⟨788914587291532716996701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8415088931109682314631477 788914587291532716996701)
                    ·
                      rfl

theorem cell23_4609217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 2, 1, 2, 2, 5].length) (baseStart_4609217 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4609217 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4609217 prefixEnd_4609217 := by exact prefixLift 4609217
  have htrace : WordTrace (prefixWord ++ tailWord_4609217) baseStart_4609217 baseEnd_4609217 := by
    simpa [prefixWord, tailWord_4609217, baseEnd_4609217] using wordTrace_append hprefix tailTrace_4609217
  have hstable : (prefixWord ++ tailWord_4609217).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4609217).length < 2 ^ (prefixWord ++ tailWord_4609217).sum := by decide
  have hdescent : baseEnd_4609217 < baseStart_4609217 := by decide
  rcases family_descends (prefixWord ++ tailWord_4609217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4609280 : List Nat := [2, 1, 1, 2, 1, 1, 3, 2, 3, 5, 2]
def baseStart_4609280 : Nat := 118140960795 + 4609280 * 2 ^ 59
def prefixEnd_4609280 : Nat := 4983230072969 + 3 ^ 40 * 4609280 * 2
def baseEnd_4609280 : Nat := 2366776111155831404502313

theorem tailTrace_4609280 : CollatzResearch.WordTrace tailWord_4609280 prefixEnd_4609280 2366776111155831404502313 := by
  unfold tailWord_4609280
  simp only [CollatzResearch.WordTrace]
  refine ⟨84057126370686618598364647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 112076168494248824797819529 84057126370686618598364647)
  ·
    refine ⟨126085689556029927897546971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84057126370686618598364647 126085689556029927897546971)
    ·
      refine ⟨189128534334044891846320457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 126085689556029927897546971 189128534334044891846320457)
      ·
        refine ⟨141846400750533668884740343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 189128534334044891846320457 141846400750533668884740343)
        ·
          refine ⟨212769601125800503327110515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 141846400750533668884740343 212769601125800503327110515)
          ·
            refine ⟨319154401688700754990665773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 212769601125800503327110515 319154401688700754990665773)
            ·
              refine ⟨119682900633262783121499665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 319154401688700754990665773 119682900633262783121499665)
              ·
                refine ⟨89762175474947087341124749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 119682900633262783121499665 89762175474947087341124749)
                ·
                  refine ⟨33660815803105157752921781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 89762175474947087341124749 33660815803105157752921781)
                  ·
                    refine ⟨3155701481541108539336417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 33660815803105157752921781 3155701481541108539336417)
                    ·
                      refine ⟨2366776111155831404502313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3155701481541108539336417 2366776111155831404502313)
                      ·
                        rfl

theorem cell23_4609280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 3, 2, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 3, 2, 3, 5, 2].length) (baseStart_4609280 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4609280 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4609280 prefixEnd_4609280 := by exact prefixLift 4609280
  have htrace : WordTrace (prefixWord ++ tailWord_4609280) baseStart_4609280 baseEnd_4609280 := by
    simpa [prefixWord, tailWord_4609280, baseEnd_4609280] using wordTrace_append hprefix tailTrace_4609280
  have hstable : (prefixWord ++ tailWord_4609280).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4609280).length < 2 ^ (prefixWord ++ tailWord_4609280).sum := by decide
  have hdescent : baseEnd_4609280 < baseStart_4609280 := by decide
  rcases family_descends (prefixWord ++ tailWord_4609280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4609281 : List Nat := [1, 2, 4, 1, 1, 5, 2, 2, 1, 4]
def baseStart_4609281 : Nat := 118140960795 + 4609281 * 2 ^ 59
def prefixEnd_4609281 : Nat := 4983230072969 + 3 ^ 40 * 4609281 * 2
def baseEnd_4609281 : Nat := 788925541545495300196603

theorem tailTrace_4609281 : CollatzResearch.WordTrace tailWord_4609281 prefixEnd_4609281 788925541545495300196603 := by
  unfold tailWord_4609281
  simp only [CollatzResearch.WordTrace]
  refine ⟨168114289214369614367515697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112076192809579742911677131 168114289214369614367515697)
  ·
    refine ⟨126085716910777210775636773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 168114289214369614367515697 126085716910777210775636773)
    ·
      refine ⟨23641071920770727020431895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 126085716910777210775636773 23641071920770727020431895)
      ·
        refine ⟨35461607881156090530647843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23641071920770727020431895 35461607881156090530647843)
        ·
          refine ⟨53192411821734135795971765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35461607881156090530647843 53192411821734135795971765)
          ·
            refine ⟨4986788608287575230872353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 53192411821734135795971765 4986788608287575230872353)
            ·
              refine ⟨3740091456215681423154265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4986788608287575230872353 3740091456215681423154265)
              ·
                refine ⟨2805068592161761067365699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3740091456215681423154265 2805068592161761067365699)
                ·
                  refine ⟨4207602888242641601048549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2805068592161761067365699 4207602888242641601048549)
                  ·
                    refine ⟨788925541545495300196603, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4207602888242641601048549 788925541545495300196603)
                    ·
                      rfl

theorem cell23_4609281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 5, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 5, 2, 2, 1, 4].length) (baseStart_4609281 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4609281 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4609281 prefixEnd_4609281 := by exact prefixLift 4609281
  have htrace : WordTrace (prefixWord ++ tailWord_4609281) baseStart_4609281 baseEnd_4609281 := by
    simpa [prefixWord, tailWord_4609281, baseEnd_4609281] using wordTrace_append hprefix tailTrace_4609281
  have hstable : (prefixWord ++ tailWord_4609281).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4609281).length < 2 ^ (prefixWord ++ tailWord_4609281).sum := by decide
  have hdescent : baseEnd_4609281 < baseStart_4609281 := by decide
  rcases family_descends (prefixWord ++ tailWord_4609281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4609314 : List Nat := [3, 3, 1, 1, 4, 1, 1, 1, 1, 5, 2]
def baseStart_4609314 : Nat := 118140960795 + 4609314 * 2 ^ 59
def prefixEnd_4609314 : Nat := 4983230072969 + 3 ^ 40 * 4609314 * 2
def baseEnd_4609314 : Nat := 2366793569498084271477157

theorem tailTrace_4609314 : CollatzResearch.WordTrace tailWord_4609314 prefixEnd_4609314 2366793569498084271477157 := by
  unfold tailWord_4609314
  simp only [CollatzResearch.WordTrace]
  refine ⟨42028873205812515250866749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 112076995215500040668977997 42028873205812515250866749)
  ·
    refine ⟨15760827452179693219075031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 42028873205812515250866749 15760827452179693219075031)
    ·
      refine ⟨23641241178269539828612547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15760827452179693219075031 23641241178269539828612547)
      ·
        refine ⟨35461861767404309742918821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23641241178269539828612547 35461861767404309742918821)
        ·
          refine ⟨6649099081388308076797279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 35461861767404309742918821 6649099081388308076797279)
          ·
            refine ⟨9973648622082462115195919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6649099081388308076797279 9973648622082462115195919)
            ·
              refine ⟨14960472933123693172793879, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9973648622082462115195919 14960472933123693172793879)
              ·
                refine ⟨22440709399685539759190819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14960472933123693172793879 22440709399685539759190819)
                ·
                  refine ⟨33661064099528309638786229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22440709399685539759190819 33661064099528309638786229)
                  ·
                    refine ⟨3155724759330779028636209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 33661064099528309638786229 3155724759330779028636209)
                    ·
                      refine ⟨2366793569498084271477157, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3155724759330779028636209 2366793569498084271477157)
                      ·
                        rfl

theorem cell23_4609314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 4, 1, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 4, 1, 1, 1, 1, 5, 2].length) (baseStart_4609314 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4609314 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4609314 prefixEnd_4609314 := by exact prefixLift 4609314
  have htrace : WordTrace (prefixWord ++ tailWord_4609314) baseStart_4609314 baseEnd_4609314 := by
    simpa [prefixWord, tailWord_4609314, baseEnd_4609314] using wordTrace_append hprefix tailTrace_4609314
  have hstable : (prefixWord ++ tailWord_4609314).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4609314).length < 2 ^ (prefixWord ++ tailWord_4609314).sum := by decide
  have hdescent : baseEnd_4609314 < baseStart_4609314 := by decide
  rcases family_descends (prefixWord ++ tailWord_4609314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4609327 : List Nat := [1, 1, 2, 1, 2, 1, 3, 1, 7, 2, 2]
def baseStart_4609327 : Nat := 118140960795 + 4609327 * 2 ^ 59
def prefixEnd_4609327 : Nat := 4983230072969 + 3 ^ 40 * 4609327 * 2
def baseEnd_4609327 : Nat := 2366800244746592720614597

theorem tailTrace_4609327 : CollatzResearch.WordTrace tailWord_4609327 prefixEnd_4609327 2366800244746592720614597 := by
  unfold tailWord_4609327
  simp only [CollatzResearch.WordTrace]
  refine ⟨168115966972202964223690235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112077311314801976149126823 168115966972202964223690235)
  ·
    refine ⟨252173950458304446335535353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 168115966972202964223690235 252173950458304446335535353)
    ·
      refine ⟨189130462843728334751651515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 252173950458304446335535353 189130462843728334751651515)
      ·
        refine ⟨283695694265592502127477273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 189130462843728334751651515 283695694265592502127477273)
        ·
          refine ⟨212771770699194376595607955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 283695694265592502127477273 212771770699194376595607955)
          ·
            refine ⟨319157656048791564893411933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 212771770699194376595607955 319157656048791564893411933)
            ·
              refine ⟨119684121018296836835029475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 319157656048791564893411933 119684121018296836835029475)
              ·
                refine ⟨179526181527445255252544213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 119684121018296836835029475 179526181527445255252544213)
                ·
                  refine ⟨4207644879549498169981505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 179526181527445255252544213 4207644879549498169981505)
                  ·
                    refine ⟨3155733659662123627486129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4207644879549498169981505 3155733659662123627486129)
                    ·
                      refine ⟨2366800244746592720614597, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3155733659662123627486129 2366800244746592720614597)
                      ·
                        rfl

theorem cell23_4609327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 3, 1, 7, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 3, 1, 7, 2, 2].length) (baseStart_4609327 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4609327 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4609327 prefixEnd_4609327 := by exact prefixLift 4609327
  have htrace : WordTrace (prefixWord ++ tailWord_4609327) baseStart_4609327 baseEnd_4609327 := by
    simpa [prefixWord, tailWord_4609327, baseEnd_4609327] using wordTrace_append hprefix tailTrace_4609327
  have hstable : (prefixWord ++ tailWord_4609327).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4609327).length < 2 ^ (prefixWord ++ tailWord_4609327).sum := by decide
  have hdescent : baseEnd_4609327 < baseStart_4609327 := by decide
  rcases family_descends (prefixWord ++ tailWord_4609327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4609344 : List Nat := [2, 1, 1, 2, 2, 1, 6, 1, 3, 2, 2]
def baseStart_4609344 : Nat := 118140960795 + 4609344 * 2 ^ 59
def prefixEnd_4609344 : Nat := 4983230072969 + 3 ^ 40 * 4609344 * 2
def baseEnd_4609344 : Nat := 2366808973917719154102019

theorem tailTrace_4609344 : CollatzResearch.WordTrace tailWord_4609344 prefixEnd_4609344 2366808973917719154102019 := by
  unfold tailWord_4609344
  simp only [CollatzResearch.WordTrace]
  refine ⟨84058293506570688063529543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 112077724675427584084706057 84058293506570688063529543)
  ·
    refine ⟨126087440259856032095294315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84058293506570688063529543 126087440259856032095294315)
    ·
      refine ⟨189131160389784048142941473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 126087440259856032095294315 189131160389784048142941473)
      ·
        refine ⟨141848370292338036107206105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 189131160389784048142941473 141848370292338036107206105)
        ·
          refine ⟨106386277719253527080404579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 141848370292338036107206105 106386277719253527080404579)
          ·
            refine ⟨159579416578880290620606869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 106386277719253527080404579 159579416578880290620606869)
            ·
              refine ⟨7480285152135013622840947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 159579416578880290620606869 7480285152135013622840947)
              ·
                refine ⟨11220427728202520434261421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7480285152135013622840947 11220427728202520434261421)
                ·
                  refine ⟨4207660398075945162848033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11220427728202520434261421 4207660398075945162848033)
                  ·
                    refine ⟨3155745298556958872136025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4207660398075945162848033 3155745298556958872136025)
                    ·
                      refine ⟨2366808973917719154102019, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3155745298556958872136025 2366808973917719154102019)
                      ·
                        rfl

theorem cell23_4609344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 6, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 6, 1, 3, 2, 2].length) (baseStart_4609344 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4609344 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4609344 prefixEnd_4609344 := by exact prefixLift 4609344
  have htrace : WordTrace (prefixWord ++ tailWord_4609344) baseStart_4609344 baseEnd_4609344 := by
    simpa [prefixWord, tailWord_4609344, baseEnd_4609344] using wordTrace_append hprefix tailTrace_4609344
  have hstable : (prefixWord ++ tailWord_4609344).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4609344).length < 2 ^ (prefixWord ++ tailWord_4609344).sum := by decide
  have hdescent : baseEnd_4609344 < baseStart_4609344 := by decide
  rcases family_descends (prefixWord ++ tailWord_4609344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4609364 : List Nat := [2, 4, 1, 1, 2, 1, 4, 2, 1, 2, 3]
def baseStart_4609364 : Nat := 118140960795 + 4609364 * 2 ^ 59
def prefixEnd_4609364 : Nat := 4983230072969 + 3 ^ 40 * 4609364 * 2
def baseEnd_4609364 : Nat := 2366819243530809075851927

theorem tailTrace_4609364 : CollatzResearch.WordTrace tailWord_4609364 prefixEnd_4609364 2366819243530809075851927 := by
  unfold tailWord_4609364
  simp only [CollatzResearch.WordTrace]
  refine ⟨84058658236534459771393573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 112078210982045946361858097 84058658236534459771393573)
  ·
    refine ⟨15760998419350211207136295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 84058658236534459771393573 15760998419350211207136295)
    ·
      refine ⟨23641497629025316810704443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15760998419350211207136295 23641497629025316810704443)
      ·
        refine ⟨35462246443537975216056665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23641497629025316810704443 35462246443537975216056665)
        ·
          refine ⟨26596684832653481412042499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35462246443537975216056665 26596684832653481412042499)
          ·
            refine ⟨39895027248980222118063749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26596684832653481412042499 39895027248980222118063749)
            ·
              refine ⟨7480317609183791647136953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 39895027248980222118063749 7480317609183791647136953)
              ·
                refine ⟨5610238206887843735352715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7480317609183791647136953 5610238206887843735352715)
                ·
                  refine ⟨8415357310331765603029073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5610238206887843735352715 8415357310331765603029073)
                  ·
                    refine ⟨6311517982748824202271805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8415357310331765603029073 6311517982748824202271805)
                    ·
                      refine ⟨2366819243530809075851927, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6311517982748824202271805 2366819243530809075851927)
                      ·
                        rfl

theorem cell23_4609364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 4, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 4, 2, 1, 2, 3].length) (baseStart_4609364 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4609364 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4609364 prefixEnd_4609364 := by exact prefixLift 4609364
  have htrace : WordTrace (prefixWord ++ tailWord_4609364) baseStart_4609364 baseEnd_4609364 := by
    simpa [prefixWord, tailWord_4609364, baseEnd_4609364] using wordTrace_append hprefix tailTrace_4609364
  have hstable : (prefixWord ++ tailWord_4609364).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4609364).length < 2 ^ (prefixWord ++ tailWord_4609364).sum := by decide
  have hdescent : baseEnd_4609364 < baseStart_4609364 := by decide
  rcases family_descends (prefixWord ++ tailWord_4609364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4609367 : List Nat := [1, 1, 3, 2, 3, 4, 2, 7]
def baseStart_4609367 : Nat := 118140960795 + 4609367 * 2 ^ 59
def prefixEnd_4609367 : Nat := 4983230072969 + 3 ^ 40 * 4609367 * 2
def baseEnd_4609367 : Nat := 87660029036028613485719

theorem tailTrace_4609367 : CollatzResearch.WordTrace tailWord_4609367 prefixEnd_4609367 87660029036028613485719 := by
  unfold tailWord_4609367
  simp only [CollatzResearch.WordTrace]
  refine ⟨168117425892058051055146355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112078283928038700703430903 168117425892058051055146355)
  ·
    refine ⟨252176138838087076582719533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 168117425892058051055146355 252176138838087076582719533)
    ·
      refine ⟨94566052064282653718519825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 252176138838087076582719533 94566052064282653718519825)
      ·
        refine ⟨70924539048211990288889869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 94566052064282653718519825 70924539048211990288889869)
        ·
          refine ⟨26596702143079496358333701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 70924539048211990288889869 26596702143079496358333701)
          ·
            refine ⟨4986881651827405567187569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 26596702143079496358333701 4986881651827405567187569)
            ·
              refine ⟨3740161238870554175390677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4986881651827405567187569 3740161238870554175390677)
              ·
                refine ⟨87660029036028613485719, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3740161238870554175390677 87660029036028613485719)
                ·
                  rfl

theorem cell23_4609367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 4, 2, 7].length) (baseStart_4609367 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4609367 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4609367 prefixEnd_4609367 := by exact prefixLift 4609367
  have htrace : WordTrace (prefixWord ++ tailWord_4609367) baseStart_4609367 baseEnd_4609367 := by
    simpa [prefixWord, tailWord_4609367, baseEnd_4609367] using wordTrace_append hprefix tailTrace_4609367
  have hstable : (prefixWord ++ tailWord_4609367).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4609367).length < 2 ^ (prefixWord ++ tailWord_4609367).sum := by decide
  have hdescent : baseEnd_4609367 < baseStart_4609367 := by decide
  rcases family_descends (prefixWord ++ tailWord_4609367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4609394 : List Nat := [3, 2, 1, 2, 1, 2, 2, 4, 2, 1, 3]
def baseStart_4609394 : Nat := 118140960795 + 4609394 * 2 ^ 59
def prefixEnd_4609394 : Nat := 4983230072969 + 3 ^ 40 * 4609394 * 2
def baseEnd_4609394 : Nat := 2366834647950443958476789

theorem tailTrace_4609394 : CollatzResearch.WordTrace tailWord_4609394 prefixEnd_4609394 2366834647950443958476789 := by
  unfold tailWord_4609394
  simp only [CollatzResearch.WordTrace]
  refine ⟨42029602665740058666594809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 112078940441973489777586157 42029602665740058666594809)
  ·
    refine ⟨31522201999305043999946107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42029602665740058666594809 31522201999305043999946107)
    ·
      refine ⟨47283302998957565999919161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31522201999305043999946107 47283302998957565999919161)
      ·
        refine ⟨35462477249218174499939371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47283302998957565999919161 35462477249218174499939371)
        ·
          refine ⟨53193715873827261749909057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35462477249218174499939371 53193715873827261749909057)
          ·
            refine ⟨39895286905370446312431793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 53193715873827261749909057 39895286905370446312431793)
            ·
              refine ⟨29921465179027834734323845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 39895286905370446312431793 29921465179027834734323845)
              ·
                refine ⟨5610274721067719012685721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 29921465179027834734323845 5610274721067719012685721)
                ·
                  refine ⟨4207706040800789259514291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5610274721067719012685721 4207706040800789259514291)
                  ·
                    refine ⟨6311559061201183889271437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4207706040800789259514291 6311559061201183889271437)
                    ·
                      refine ⟨2366834647950443958476789, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6311559061201183889271437 2366834647950443958476789)
                      ·
                        rfl

theorem cell23_4609394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 2, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 2, 4, 2, 1, 3].length) (baseStart_4609394 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4609394 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4609394 prefixEnd_4609394 := by exact prefixLift 4609394
  have htrace : WordTrace (prefixWord ++ tailWord_4609394) baseStart_4609394 baseEnd_4609394 := by
    simpa [prefixWord, tailWord_4609394, baseEnd_4609394] using wordTrace_append hprefix tailTrace_4609394
  have hstable : (prefixWord ++ tailWord_4609394).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4609394).length < 2 ^ (prefixWord ++ tailWord_4609394).sum := by decide
  have hdescent : baseEnd_4609394 < baseStart_4609394 := by decide
  rcases family_descends (prefixWord ++ tailWord_4609394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4609411 : List Nat := [1, 1, 1, 3, 5, 1, 4, 1, 2, 1, 3]
def baseStart_4609411 : Nat := 118140960795 + 4609411 * 2 ^ 59
def prefixEnd_4609411 : Nat := 4983230072969 + 3 ^ 40 * 4609411 * 2
def baseEnd_4609411 : Nat := 2366843377121570391964211

theorem tailTrace_4609411 : CollatzResearch.WordTrace tailWord_4609411 prefixEnd_4609411 2366843377121570391964211 := by
  unfold tailWord_4609411
  simp only [CollatzResearch.WordTrace]
  refine ⟨168119030703898646569748087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112079353802599097713165391 168119030703898646569748087)
  ·
    refine ⟨252178546055847969854622131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 168119030703898646569748087 252178546055847969854622131)
    ·
      refine ⟨378267819083771954781933197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 252178546055847969854622131 378267819083771954781933197)
      ·
        refine ⟨141850432156414483043224949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 378267819083771954781933197 141850432156414483043224949)
        ·
          refine ⟨13298478014663857785302339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 141850432156414483043224949 13298478014663857785302339)
          ·
            refine ⟨19947717021995786677953509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13298478014663857785302339 19947717021995786677953509)
            ·
              refine ⟨3740196941624210002116283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 19947717021995786677953509 3740196941624210002116283)
              ·
                refine ⟨5610295412436315003174425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3740196941624210002116283 5610295412436315003174425)
                ·
                  refine ⟨4207721559327236252380819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5610295412436315003174425 4207721559327236252380819)
                  ·
                    refine ⟨6311582338990854378571229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4207721559327236252380819 6311582338990854378571229)
                    ·
                      refine ⟨2366843377121570391964211, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6311582338990854378571229 2366843377121570391964211)
                      ·
                        rfl

theorem cell23_4609411_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 4, 1, 2, 1, 3].length) (baseStart_4609411 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4609411 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4609411 prefixEnd_4609411 := by exact prefixLift 4609411
  have htrace : WordTrace (prefixWord ++ tailWord_4609411) baseStart_4609411 baseEnd_4609411 := by
    simpa [prefixWord, tailWord_4609411, baseEnd_4609411] using wordTrace_append hprefix tailTrace_4609411
  have hstable : (prefixWord ++ tailWord_4609411).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4609411).length < 2 ^ (prefixWord ++ tailWord_4609411).sum := by decide
  have hdescent : baseEnd_4609411 < baseStart_4609411 := by decide
  rcases family_descends (prefixWord ++ tailWord_4609411) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4609420 : List Nat := [2, 2, 1, 2, 1, 3, 1, 1, 4, 1, 5]
def baseStart_4609420 : Nat := 118140960795 + 4609420 * 2 ^ 59
def prefixEnd_4609420 : Nat := 4983230072969 + 3 ^ 40 * 4609420 * 2
def baseEnd_4609420 : Nat := 2366847998447460856751669

theorem tailTrace_4609420 : CollatzResearch.WordTrace tailWord_4609420 prefixEnd_4609420 2366847998447460856751669 := by
  unfold tailWord_4609420
  simp only [CollatzResearch.WordTrace]
  refine ⟨84059679480433020553412857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 112079572640577360737883809 84059679480433020553412857)
  ·
    refine ⟨63044759610324765415059643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 84059679480433020553412857 63044759610324765415059643)
    ·
      refine ⟨94567139415487148122589465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63044759610324765415059643 94567139415487148122589465)
      ·
        refine ⟨70925354561615361091942099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 94567139415487148122589465 70925354561615361091942099)
        ·
          refine ⟨106388031842423041637913149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 70925354561615361091942099 106388031842423041637913149)
          ·
            refine ⟨39895511940908640614217431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 106388031842423041637913149 39895511940908640614217431)
            ·
              refine ⟨59843267911362960921326147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39895511940908640614217431 59843267911362960921326147)
              ·
                refine ⟨89764901867044441381989221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 59843267911362960921326147 89764901867044441381989221)
                ·
                  refine ⟨16830919100070832759122979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 89764901867044441381989221 16830919100070832759122979)
                  ·
                    refine ⟨25246378650106249138684469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16830919100070832759122979 25246378650106249138684469)
                    ·
                      refine ⟨2366847998447460856751669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25246378650106249138684469 2366847998447460856751669)
                      ·
                        rfl

theorem cell23_4609420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 1, 1, 4, 1, 5].length) (baseStart_4609420 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4609420 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4609420 prefixEnd_4609420 := by exact prefixLift 4609420
  have htrace : WordTrace (prefixWord ++ tailWord_4609420) baseStart_4609420 baseEnd_4609420 := by
    simpa [prefixWord, tailWord_4609420, baseEnd_4609420] using wordTrace_append hprefix tailTrace_4609420
  have hstable : (prefixWord ++ tailWord_4609420).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4609420).length < 2 ^ (prefixWord ++ tailWord_4609420).sum := by decide
  have hdescent : baseEnd_4609420 < baseStart_4609420 := by decide
  rcases family_descends (prefixWord ++ tailWord_4609420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4609434 : List Nat := [3, 1, 1, 4, 1, 1, 3, 2, 1, 4, 2]
def baseStart_4609434 : Nat := 118140960795 + 4609434 * 2 ^ 59
def prefixEnd_4609434 : Nat := 4983230072969 + 3 ^ 40 * 4609434 * 2
def baseEnd_4609434 : Nat := 2366855187176623801976605

theorem tailTrace_4609434 : CollatzResearch.WordTrace tailWord_4609434 prefixEnd_4609434 2366855187176623801976605 := by
  unfold tailWord_4609434
  simp only [CollatzResearch.WordTrace]
  refine ⟨42029967395703830374458839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 112079913055210214331890237 42029967395703830374458839)
  ·
    refine ⟨63044951093555745561688259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42029967395703830374458839 63044951093555745561688259)
    ·
      refine ⟨94567426640333618342532389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63044951093555745561688259 94567426640333618342532389)
      ·
        refine ⟨17731392495062553439224823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 94567426640333618342532389 17731392495062553439224823)
        ·
          refine ⟨26597088742593830158837235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17731392495062553439224823 26597088742593830158837235)
          ·
            refine ⟨39895633113890745238255853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26597088742593830158837235 39895633113890745238255853)
            ·
              refine ⟨14960862417709029464345945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 39895633113890745238255853 14960862417709029464345945)
              ·
                refine ⟨11220646813281772098259459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14960862417709029464345945 11220646813281772098259459)
                ·
                  refine ⟨16830970219922658147389189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11220646813281772098259459 16830970219922658147389189)
                  ·
                    refine ⟨3155806916235498402635473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16830970219922658147389189 3155806916235498402635473)
                    ·
                      refine ⟨2366855187176623801976605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3155806916235498402635473 2366855187176623801976605)
                      ·
                        rfl

theorem cell23_4609434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 3, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 3, 2, 1, 4, 2].length) (baseStart_4609434 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4609434 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4609434 prefixEnd_4609434 := by exact prefixLift 4609434
  have htrace : WordTrace (prefixWord ++ tailWord_4609434) baseStart_4609434 baseEnd_4609434 := by
    simpa [prefixWord, tailWord_4609434, baseEnd_4609434] using wordTrace_append hprefix tailTrace_4609434
  have hstable : (prefixWord ++ tailWord_4609434).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4609434).length < 2 ^ (prefixWord ++ tailWord_4609434).sum := by decide
  have hdescent : baseEnd_4609434 < baseStart_4609434 := by decide
  rcases family_descends (prefixWord ++ tailWord_4609434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4609437 : List Nat := [1, 4, 2, 1, 3, 1, 2, 1, 2, 1, 5]
def baseStart_4609437 : Nat := 118140960795 + 4609437 * 2 ^ 59
def prefixEnd_4609437 : Nat := 4983230072969 + 3 ^ 40 * 4609437 * 2
def baseEnd_4609437 : Nat := 2366856727618587290239091

theorem tailTrace_4609437 : CollatzResearch.WordTrace tailWord_4609437 prefixEnd_4609437 2366856727618587290239091 := by
  unfold tailWord_4609437
  simp only [CollatzResearch.WordTrace]
  refine ⟨168119979001804453010194565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112079986001202968673463043 168119979001804453010194565)
  ·
    refine ⟨31522496062838334939411481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 168119979001804453010194565 31522496062838334939411481)
    ·
      refine ⟨23641872047128751204558611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31522496062838334939411481 23641872047128751204558611)
      ·
        refine ⟨35462808070693126806837917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23641872047128751204558611 35462808070693126806837917)
        ·
          refine ⟨13298553026509922552564219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 35462808070693126806837917 13298553026509922552564219)
          ·
            refine ⟨19947829539764883828846329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13298553026509922552564219 19947829539764883828846329)
            ·
              refine ⟨14960872154823662871634747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19947829539764883828846329 14960872154823662871634747)
              ·
                refine ⟨22441308232235494307452121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14960872154823662871634747 22441308232235494307452121)
                ·
                  refine ⟨16830981174176620730589091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22441308232235494307452121 16830981174176620730589091)
                  ·
                    refine ⟨25246471761264931095883637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16830981174176620730589091 25246471761264931095883637)
                    ·
                      refine ⟨2366856727618587290239091, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25246471761264931095883637 2366856727618587290239091)
                      ·
                        rfl

theorem cell23_4609437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 2, 1, 2, 1, 5].length) (baseStart_4609437 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4609437 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4609437 prefixEnd_4609437 := by exact prefixLift 4609437
  have htrace : WordTrace (prefixWord ++ tailWord_4609437) baseStart_4609437 baseEnd_4609437 := by
    simpa [prefixWord, tailWord_4609437, baseEnd_4609437] using wordTrace_append hprefix tailTrace_4609437
  have hstable : (prefixWord ++ tailWord_4609437).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4609437).length < 2 ^ (prefixWord ++ tailWord_4609437).sum := by decide
  have hdescent : baseEnd_4609437 < baseStart_4609437 := by decide
  rcases family_descends (prefixWord ++ tailWord_4609437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4609447 : List Nat := [1, 1, 6, 1, 1, 1, 2, 2, 2, 2, 4]
def baseStart_4609447 : Nat := 118140960795 + 4609447 * 2 ^ 59
def prefixEnd_4609447 : Nat := 4983230072969 + 3 ^ 40 * 4609447 * 2
def baseEnd_4609447 : Nat := 2366861862425132251114045

theorem tailTrace_4609447 : CollatzResearch.WordTrace tailWord_4609447 prefixEnd_4609447 2366861862425132251114045 := by
  unfold tailWord_4609447
  simp only [CollatzResearch.WordTrace]
  refine ⟨168120343731768224718058595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112080229154512149812039063 168120343731768224718058595)
  ·
    refine ⟨252180515597652337077087893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 168120343731768224718058595 252180515597652337077087893)
    ·
      refine ⟨11820961668639953300488495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 252180515597652337077087893 11820961668639953300488495)
      ·
        refine ⟨17731442502959929950732743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11820961668639953300488495 17731442502959929950732743)
        ·
          refine ⟨26597163754439894926099115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17731442502959929950732743 26597163754439894926099115)
          ·
            refine ⟨39895745631659842389148673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26597163754439894926099115 39895745631659842389148673)
            ·
              refine ⟨29921809223744881791861505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 39895745631659842389148673 29921809223744881791861505)
              ·
                refine ⟨22441356917808661343896129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29921809223744881791861505 22441356917808661343896129)
                ·
                  refine ⟨16831017688356496007922097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22441356917808661343896129 16831017688356496007922097)
                  ·
                    refine ⟨12623263266267372005941573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16831017688356496007922097 12623263266267372005941573)
                    ·
                      refine ⟨2366861862425132251114045, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12623263266267372005941573 2366861862425132251114045)
                      ·
                        rfl

theorem cell23_4609447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 2, 2, 2, 2, 4].length) (baseStart_4609447 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4609447 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4609447 prefixEnd_4609447 := by exact prefixLift 4609447
  have htrace : WordTrace (prefixWord ++ tailWord_4609447) baseStart_4609447 baseEnd_4609447 := by
    simpa [prefixWord, tailWord_4609447, baseEnd_4609447] using wordTrace_append hprefix tailTrace_4609447
  have hstable : (prefixWord ++ tailWord_4609447).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4609447).length < 2 ^ (prefixWord ++ tailWord_4609447).sum := by decide
  have hdescent : baseEnd_4609447 < baseStart_4609447 := by decide
  rcases family_descends (prefixWord ++ tailWord_4609447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4609487 : List Nat := [1, 1, 2, 1, 1, 4, 5, 1, 2, 5]
def baseStart_4609487 : Nat := 118140960795 + 4609487 * 2 ^ 59
def prefixEnd_4609487 : Nat := 4983230072969 + 3 ^ 40 * 4609487 * 2
def baseEnd_4609487 : Nat := 788960800550437364871287

theorem tailTrace_4609487 : CollatzResearch.WordTrace tailWord_4609487 prefixEnd_4609487 788960800550437364871287 := by
  unfold tailWord_4609487
  simp only [CollatzResearch.WordTrace]
  refine ⟨168121802651623311549514715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112081201767748874366343143 168121802651623311549514715)
  ·
    refine ⟨252182703977434967324272073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 168121802651623311549514715 252182703977434967324272073)
    ·
      refine ⟨189137027983076225493204055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 252182703977434967324272073 189137027983076225493204055)
      ·
        refine ⟨283705541974614338239806083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 189137027983076225493204055 283705541974614338239806083)
        ·
          refine ⟨425558312961921507359709125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 283705541974614338239806083 425558312961921507359709125)
          ·
            refine ⟨79792183680360282629945461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 425558312961921507359709125 79792183680360282629945461)
            ·
              refine ⟨7480517220033776496557387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 79792183680360282629945461 7480517220033776496557387)
              ·
                refine ⟨11220775830050664744836081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7480517220033776496557387 11220775830050664744836081)
                ·
                  refine ⟨8415581872537998558627061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11220775830050664744836081 8415581872537998558627061)
                  ·
                    refine ⟨788960800550437364871287, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8415581872537998558627061 788960800550437364871287)
                    ·
                      rfl

theorem cell23_4609487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 5, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 5, 1, 2, 5].length) (baseStart_4609487 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4609487 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4609487 prefixEnd_4609487 := by exact prefixLift 4609487
  have htrace : WordTrace (prefixWord ++ tailWord_4609487) baseStart_4609487 baseEnd_4609487 := by
    simpa [prefixWord, tailWord_4609487, baseEnd_4609487] using wordTrace_append hprefix tailTrace_4609487
  have hstable : (prefixWord ++ tailWord_4609487).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4609487).length < 2 ^ (prefixWord ++ tailWord_4609487).sum := by decide
  have hdescent : baseEnd_4609487 < baseStart_4609487 := by decide
  rcases family_descends (prefixWord ++ tailWord_4609487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4609527 : List Nat := [1, 1, 3, 1, 1, 1, 1, 3, 6, 2, 3]
def baseStart_4609527 : Nat := 118140960795 + 4609527 * 2 ^ 59
def prefixEnd_4609527 : Nat := 4983230072969 + 3 ^ 40 * 4609527 * 2
def baseEnd_4609527 : Nat := 2366902940877491938113677

theorem tailTrace_4609527 : CollatzResearch.WordTrace tailWord_4609527 prefixEnd_4609527 2366902940877491938113677 := by
  unfold tailWord_4609527
  simp only [CollatzResearch.WordTrace]
  refine ⟨168123261571478398380970835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112082174380985598920647223 168123261571478398380970835)
  ·
    refine ⟨252184892357217597571456253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 168123261571478398380970835 252184892357217597571456253)
    ·
      refine ⟨94569334633956599089296095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 252184892357217597571456253 94569334633956599089296095)
      ·
        refine ⟨141854001950934898633944143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 94569334633956599089296095 141854001950934898633944143)
        ·
          refine ⟨212781002926402347950916215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 141854001950934898633944143 212781002926402347950916215)
          ·
            refine ⟨319171504389603521926374323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 212781002926402347950916215 319171504389603521926374323)
            ·
              refine ⟨478757256584405282889561485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 319171504389603521926374323 478757256584405282889561485)
              ·
                refine ⟨179533971219151981083585557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 478757256584405282889561485 179533971219151981083585557)
                ·
                  refine ⟨8415654900897749113293073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 179533971219151981083585557 8415654900897749113293073)
                  ·
                    refine ⟨6311741175673311834969805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8415654900897749113293073 6311741175673311834969805)
                    ·
                      refine ⟨2366902940877491938113677, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6311741175673311834969805 2366902940877491938113677)
                      ·
                        rfl

theorem cell23_4609527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 3, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 3, 6, 2, 3].length) (baseStart_4609527 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4609527 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4609527 prefixEnd_4609527 := by exact prefixLift 4609527
  have htrace : WordTrace (prefixWord ++ tailWord_4609527) baseStart_4609527 baseEnd_4609527 := by
    simpa [prefixWord, tailWord_4609527, baseEnd_4609527] using wordTrace_append hprefix tailTrace_4609527
  have hstable : (prefixWord ++ tailWord_4609527).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4609527).length < 2 ^ (prefixWord ++ tailWord_4609527).sum := by decide
  have hdescent : baseEnd_4609527 < baseStart_4609527 := by decide
  rcases family_descends (prefixWord ++ tailWord_4609527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4609542 : List Nat := [6, 2, 1, 1, 2, 2, 1, 3, 5]
def baseStart_4609542 : Nat := 118140960795 + 4609542 * 2 ^ 59
def prefixEnd_4609542 : Nat := 4983230072969 + 3 ^ 40 * 4609542 * 2
def baseEnd_4609542 : Nat := 262990071454145486602901

theorem tailTrace_4609542 : CollatzResearch.WordTrace tailWord_4609542 prefixEnd_4609542 262990071454145486602901 := by
  unfold tailWord_4609542
  simp only [CollatzResearch.WordTrace]
  refine ⟨5253869020825751748211465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 112082539110949370628511253 5253869020825751748211465)
  ·
    refine ⟨3940401765619313811158599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5253869020825751748211465 3940401765619313811158599)
    ·
      refine ⟨5910602648428970716737899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3940401765619313811158599 5910602648428970716737899)
      ·
        refine ⟨8865903972643456075106849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5910602648428970716737899 8865903972643456075106849)
        ·
          refine ⟨6649427979482592056330137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8865903972643456075106849 6649427979482592056330137)
          ·
            refine ⟨4987070984611944042247603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6649427979482592056330137 4987070984611944042247603)
            ·
              refine ⟨7480606476917916063371405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4987070984611944042247603 7480606476917916063371405)
              ·
                refine ⟨2805227428844218523764277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7480606476917916063371405 2805227428844218523764277)
                ·
                  refine ⟨262990071454145486602901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2805227428844218523764277 262990071454145486602901)
                  ·
                    rfl

theorem cell23_4609542_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 2, 2, 1, 3, 5].length) (baseStart_4609542 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4609542 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4609542 prefixEnd_4609542 := by exact prefixLift 4609542
  have htrace : WordTrace (prefixWord ++ tailWord_4609542) baseStart_4609542 baseEnd_4609542 := by
    simpa [prefixWord, tailWord_4609542, baseEnd_4609542] using wordTrace_append hprefix tailTrace_4609542
  have hstable : (prefixWord ++ tailWord_4609542).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4609542).length < 2 ^ (prefixWord ++ tailWord_4609542).sum := by decide
  have hdescent : baseEnd_4609542 < baseStart_4609542 := by decide
  rcases family_descends (prefixWord ++ tailWord_4609542) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4609584 : List Nat := [2, 1, 1, 1, 2, 3, 1, 1, 6, 3, 2]
def baseStart_4609584 : Nat := 118140960795 + 4609584 * 2 ^ 59
def prefixEnd_4609584 : Nat := 4983230072969 + 3 ^ 40 * 4609584 * 2
def baseEnd_4609584 : Nat := 2366932209274798215100915

theorem tailTrace_4609584 : CollatzResearch.WordTrace tailWord_4609584 prefixEnd_4609584 2366932209274798215100915 := by
  unfold tailWord_4609584
  simp only [CollatzResearch.WordTrace]
  refine ⟨84062670266135948557897903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 112083560354847931410530537 84062670266135948557897903)
  ·
    refine ⟨126094005399203922836846855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84062670266135948557897903 126094005399203922836846855)
    ·
      refine ⟨189141008098805884255270283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 126094005399203922836846855 189141008098805884255270283)
      ·
        refine ⟨283711512148208826382905425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 189141008098805884255270283 283711512148208826382905425)
        ·
          refine ⟨212783634111156619787179069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 283711512148208826382905425 212783634111156619787179069)
          ·
            refine ⟨79793862791683732420192151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 212783634111156619787179069 79793862791683732420192151)
            ·
              refine ⟨119690794187525598630288227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 79793862791683732420192151 119690794187525598630288227)
              ·
                refine ⟨179536191281288397945432341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 119690794187525598630288227 179536191281288397945432341)
                ·
                  refine ⟨8415758966310393653692141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 179536191281288397945432341 8415758966310393653692141)
                  ·
                    refine ⟨3155909612366397620134553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8415758966310393653692141 3155909612366397620134553)
                    ·
                      refine ⟨2366932209274798215100915, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3155909612366397620134553 2366932209274798215100915)
                      ·
                        rfl

theorem cell23_4609584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 1, 1, 6, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 1, 1, 6, 3, 2].length) (baseStart_4609584 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4609584 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4609584 prefixEnd_4609584 := by exact prefixLift 4609584
  have htrace : WordTrace (prefixWord ++ tailWord_4609584) baseStart_4609584 baseEnd_4609584 := by
    simpa [prefixWord, tailWord_4609584, baseEnd_4609584] using wordTrace_append hprefix tailTrace_4609584
  have hstable : (prefixWord ++ tailWord_4609584).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4609584).length < 2 ^ (prefixWord ++ tailWord_4609584).sum := by decide
  have hdescent : baseEnd_4609584 < baseStart_4609584 := by decide
  rcases family_descends (prefixWord ++ tailWord_4609584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4609648 : List Nat := [2, 1, 1, 1, 6, 2, 1, 2, 3, 2, 2]
def baseStart_4609648 : Nat := 118140960795 + 4609648 * 2 ^ 59
def prefixEnd_4609648 : Nat := 4983230072969 + 3 ^ 40 * 4609648 * 2
def baseEnd_4609648 : Nat := 2366965072036685964700621

theorem tailTrace_4609648 : CollatzResearch.WordTrace tailWord_4609648 prefixEnd_4609648 2366965072036685964700621 := by
  unfold tailWord_4609648
  simp only [CollatzResearch.WordTrace]
  refine ⟨84063837402020018023062799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 112085116536026690697417065 84063837402020018023062799)
  ·
    refine ⟨126095756103030027034594199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84063837402020018023062799 126095756103030027034594199)
    ·
      refine ⟨189143634154545040551891299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 126095756103030027034594199 189143634154545040551891299)
      ·
        refine ⟨283715451231817560827836949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 189143634154545040551891299 283715451231817560827836949)
        ·
          refine ⟨13299161776491448163804857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 283715451231817560827836949 13299161776491448163804857)
          ·
            refine ⟨9974371332368586122853643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13299161776491448163804857 9974371332368586122853643)
            ·
              refine ⟨14961556998552879184280465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9974371332368586122853643 14961556998552879184280465)
              ·
                refine ⟨11221167748914659388210349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14961556998552879184280465 11221167748914659388210349)
                ·
                  refine ⟨4207937905842997270578881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11221167748914659388210349 4207937905842997270578881)
                  ·
                    refine ⟨3155953429382247952934161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4207937905842997270578881 3155953429382247952934161)
                    ·
                      refine ⟨2366965072036685964700621, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3155953429382247952934161 2366965072036685964700621)
                      ·
                        rfl

theorem cell23_4609648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 2, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 2, 1, 2, 3, 2, 2].length) (baseStart_4609648 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4609648 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4609648 prefixEnd_4609648 := by exact prefixLift 4609648
  have htrace : WordTrace (prefixWord ++ tailWord_4609648) baseStart_4609648 baseEnd_4609648 := by
    simpa [prefixWord, tailWord_4609648, baseEnd_4609648] using wordTrace_append hprefix tailTrace_4609648
  have hstable : (prefixWord ++ tailWord_4609648).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4609648).length < 2 ^ (prefixWord ++ tailWord_4609648).sum := by decide
  have hdescent : baseEnd_4609648 < baseStart_4609648 := by decide
  rcases family_descends (prefixWord ++ tailWord_4609648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4609664 : List Nat := [2, 1, 1, 2, 1, 4, 1, 4, 1, 3, 3]
def baseStart_4609664 : Nat := 118140960795 + 4609664 * 2 ^ 59
def prefixEnd_4609664 : Nat := 4983230072969 + 3 ^ 40 * 4609664 * 2
def baseEnd_4609664 : Nat := 2366973287727157902100547

theorem tailTrace_4609664 : CollatzResearch.WordTrace tailWord_4609664 prefixEnd_4609664 2366973287727157902100547 := by
  unfold tailWord_4609664
  simp only [CollatzResearch.WordTrace]
  refine ⟨84064129185991035389354023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 112085505581321380519138697 84064129185991035389354023)
  ·
    refine ⟨126096193778986553084031035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84064129185991035389354023 126096193778986553084031035)
    ·
      refine ⟨189144290668479829626046553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 126096193778986553084031035 189144290668479829626046553)
      ·
        refine ⟨141858218001359872219534915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 189144290668479829626046553 141858218001359872219534915)
        ·
          refine ⟨212787327002039808329302373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 141858218001359872219534915 212787327002039808329302373)
          ·
            refine ⟨39897623812882464061744195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 212787327002039808329302373 39897623812882464061744195)
            ·
              refine ⟨59846435719323696092616293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39897623812882464061744195 59846435719323696092616293)
              ·
                refine ⟨11221206697373193017365555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 59846435719323696092616293 11221206697373193017365555)
                ·
                  refine ⟨16831810046059789526048333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11221206697373193017365555 16831810046059789526048333)
                  ·
                    refine ⟨6311928767272421072268125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16831810046059789526048333 6311928767272421072268125)
                    ·
                      refine ⟨2366973287727157902100547, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6311928767272421072268125 2366973287727157902100547)
                      ·
                        rfl

theorem cell23_4609664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 1, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 1, 4, 1, 3, 3].length) (baseStart_4609664 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4609664 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4609664 prefixEnd_4609664 := by exact prefixLift 4609664
  have htrace : WordTrace (prefixWord ++ tailWord_4609664) baseStart_4609664 baseEnd_4609664 := by
    simpa [prefixWord, tailWord_4609664, baseEnd_4609664] using wordTrace_append hprefix tailTrace_4609664
  have hstable : (prefixWord ++ tailWord_4609664).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4609664).length < 2 ^ (prefixWord ++ tailWord_4609664).sum := by decide
  have hdescent : baseEnd_4609664 < baseStart_4609664 := by decide
  rcases family_descends (prefixWord ++ tailWord_4609664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4609665 : List Nat := [1, 2, 4, 2, 1, 2, 1, 5, 1, 2, 2]
def baseStart_4609665 : Nat := 118140960795 + 4609665 * 2 ^ 59
def prefixEnd_4609665 : Nat := 4983230072969 + 3 ^ 40 * 4609665 * 2
def baseEnd_4609665 : Nat := 2366973801207812398188043

theorem tailTrace_4609665 : CollatzResearch.WordTrace tailWord_4609665 prefixEnd_4609665 2366973801207812398188043 := by
  unfold tailWord_4609665
  simp only [CollatzResearch.WordTrace]
  refine ⟨168128294844978447949494449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112085529896652298632996299 168128294844978447949494449)
  ·
    refine ⟨126096221133733835962120837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 168128294844978447949494449 126096221133733835962120837)
    ·
      refine ⟨23643041462575094242897657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 126096221133733835962120837 23643041462575094242897657)
      ·
        refine ⟨17732281096931320682173243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23643041462575094242897657 17732281096931320682173243)
        ·
          refine ⟨26598421645396981023259865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17732281096931320682173243 26598421645396981023259865)
          ·
            refine ⟨19948816234047735767444899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26598421645396981023259865 19948816234047735767444899)
            ·
              refine ⟨29923224351071603651167349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19948816234047735767444899 29923224351071603651167349)
              ·
                refine ⟨2805302282912962842296939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 29923224351071603651167349 2805302282912962842296939)
                ·
                  refine ⟨4207953424369444263445409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2805302282912962842296939 4207953424369444263445409)
                  ·
                    refine ⟨3155965068277083197584057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4207953424369444263445409 3155965068277083197584057)
                    ·
                      refine ⟨2366973801207812398188043, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3155965068277083197584057 2366973801207812398188043)
                      ·
                        rfl

theorem cell23_4609665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 1, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 1, 5, 1, 2, 2].length) (baseStart_4609665 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4609665 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4609665 prefixEnd_4609665 := by exact prefixLift 4609665
  have htrace : WordTrace (prefixWord ++ tailWord_4609665) baseStart_4609665 baseEnd_4609665 := by
    simpa [prefixWord, tailWord_4609665, baseEnd_4609665] using wordTrace_append hprefix tailTrace_4609665
  have hstable : (prefixWord ++ tailWord_4609665).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4609665).length < 2 ^ (prefixWord ++ tailWord_4609665).sum := by decide
  have hdescent : baseEnd_4609665 < baseStart_4609665 := by decide
  rcases family_descends (prefixWord ++ tailWord_4609665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4609668 : List Nat := [2, 3, 2, 1, 4, 1, 1, 3, 1, 2, 3]
def baseStart_4609668 : Nat := 118140960795 + 4609668 * 2 ^ 59
def prefixEnd_4609668 : Nat := 4983230072969 + 3 ^ 40 * 4609668 * 2
def baseEnd_4609668 : Nat := 2366975341649775886450529

theorem tailTrace_4609668 : CollatzResearch.WordTrace tailWord_4609668 prefixEnd_4609668 2366975341649775886450529 := by
  unfold tailWord_4609668
  simp only [CollatzResearch.WordTrace]
  refine ⟨84064202131983789730926829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 112085602842645052974569105 84064202131983789730926829)
  ·
    refine ⟨31524075799493921149097561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 84064202131983789730926829 31524075799493921149097561)
    ·
      refine ⟨23643056849620440861823171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31524075799493921149097561 23643056849620440861823171)
      ·
        refine ⟨35464585274430661292734757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23643056849620440861823171 35464585274430661292734757)
        ·
          refine ⟨6649609738955748992387767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 35464585274430661292734757 6649609738955748992387767)
          ·
            refine ⟨9974414608433623488581651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6649609738955748992387767 9974414608433623488581651)
            ·
              refine ⟨14961621912650435232872477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9974414608433623488581651 14961621912650435232872477)
              ·
                refine ⟨5610608217243913212327179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14961621912650435232872477 5610608217243913212327179)
                ·
                  refine ⟨8415912325865869818490769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5610608217243913212327179 8415912325865869818490769)
                  ·
                    refine ⟨6311934244399402363868077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8415912325865869818490769 6311934244399402363868077)
                    ·
                      refine ⟨2366975341649775886450529, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6311934244399402363868077 2366975341649775886450529)
                      ·
                        rfl

theorem cell23_4609668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 4, 1, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 4, 1, 1, 3, 1, 2, 3].length) (baseStart_4609668 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4609668 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4609668 prefixEnd_4609668 := by exact prefixLift 4609668
  have htrace : WordTrace (prefixWord ++ tailWord_4609668) baseStart_4609668 baseEnd_4609668 := by
    simpa [prefixWord, tailWord_4609668, baseEnd_4609668] using wordTrace_append hprefix tailTrace_4609668
  have hstable : (prefixWord ++ tailWord_4609668).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4609668).length < 2 ^ (prefixWord ++ tailWord_4609668).sum := by decide
  have hdescent : baseEnd_4609668 < baseStart_4609668 := by decide
  rcases family_descends (prefixWord ++ tailWord_4609668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4609681 : List Nat := [1, 2, 2, 1, 1, 1, 1, 8, 2, 1, 3]
def baseStart_4609681 : Nat := 118140960795 + 4609681 * 2 ^ 59
def prefixEnd_4609681 : Nat := 4983230072969 + 3 ^ 40 * 4609681 * 2
def baseEnd_4609681 : Nat := 2366982016898284335587969

theorem tailTrace_4609681 : CollatzResearch.WordTrace tailWord_4609681 prefixEnd_4609681 2366982016898284335587969 := by
  unfold tailWord_4609681
  simp only [CollatzResearch.WordTrace]
  refine ⟨168128878412920482682076897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112085918941946988454717931 168128878412920482682076897)
  ·
    refine ⟨126096658809690362011557673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 168128878412920482682076897 126096658809690362011557673)
    ·
      refine ⟨94572494107267771508668255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 126096658809690362011557673 94572494107267771508668255)
      ·
        refine ⟨141858741160901657263002383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 94572494107267771508668255 141858741160901657263002383)
        ·
          refine ⟨212788111741352485894503575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 141858741160901657263002383 212788111741352485894503575)
          ·
            refine ⟨319182167612028728841755363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 212788111741352485894503575 319182167612028728841755363)
            ·
              refine ⟨478773251418043093262633045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 319182167612028728841755363 478773251418043093262633045)
              ·
                refine ⟨5610624040055192499171481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 478773251418043093262633045 5610624040055192499171481)
                ·
                  refine ⟨4207968030041394374378611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5610624040055192499171481 4207968030041394374378611)
                  ·
                    refine ⟨6311952045062091561567917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4207968030041394374378611 6311952045062091561567917)
                    ·
                      refine ⟨2366982016898284335587969, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6311952045062091561567917 2366982016898284335587969)
                      ·
                        rfl

theorem cell23_4609681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 8, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 8, 2, 1, 3].length) (baseStart_4609681 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4609681 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4609681 prefixEnd_4609681 := by exact prefixLift 4609681
  have htrace : WordTrace (prefixWord ++ tailWord_4609681) baseStart_4609681 baseEnd_4609681 := by
    simpa [prefixWord, tailWord_4609681, baseEnd_4609681] using wordTrace_append hprefix tailTrace_4609681
  have hstable : (prefixWord ++ tailWord_4609681).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4609681).length < 2 ^ (prefixWord ++ tailWord_4609681).sum := by decide
  have hdescent : baseEnd_4609681 < baseStart_4609681 := by decide
  rcases family_descends (prefixWord ++ tailWord_4609681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4609695 : List Nat := [1, 1, 2, 7, 2, 1, 1, 1, 1, 2, 4]
def baseStart_4609695 : Nat := 118140960795 + 4609695 * 2 ^ 59
def prefixEnd_4609695 : Nat := 4983230072969 + 3 ^ 40 * 4609695 * 2
def baseEnd_4609695 : Nat := 2366989205627447280812905

theorem tailTrace_4609695 : CollatzResearch.WordTrace tailWord_4609695 prefixEnd_4609695 2366989205627447280812905 := by
  unfold tailWord_4609695
  simp only [CollatzResearch.WordTrace]
  refine ⟨168129389034869763073086539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112086259356579842048724359 168129389034869763073086539)
  ·
    refine ⟨252194083552304644609629809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 168129389034869763073086539 252194083552304644609629809)
    ·
      refine ⟨189145562664228483457222357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 252194083552304644609629809 189145562664228483457222357)
      ·
        refine ⟨4433099124942855081028649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 189145562664228483457222357 4433099124942855081028649)
        ·
          refine ⟨3324824343707141310771487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4433099124942855081028649 3324824343707141310771487)
          ·
            refine ⟨4987236515560711966157231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3324824343707141310771487 4987236515560711966157231)
            ·
              refine ⟨7480854773341067949235847, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4987236515560711966157231 7480854773341067949235847)
              ·
                refine ⟨11221282160011601923853771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7480854773341067949235847 11221282160011601923853771)
                ·
                  refine ⟨16831923240017402885780657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11221282160011601923853771 16831923240017402885780657)
                  ·
                    refine ⟨12623942430013052164335493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16831923240017402885780657 12623942430013052164335493)
                    ·
                      refine ⟨2366989205627447280812905, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12623942430013052164335493 2366989205627447280812905)
                      ·
                        rfl

theorem cell23_4609695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 2, 1, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 2, 1, 1, 1, 1, 2, 4].length) (baseStart_4609695 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4609695 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4609695 prefixEnd_4609695 := by exact prefixLift 4609695
  have htrace : WordTrace (prefixWord ++ tailWord_4609695) baseStart_4609695 baseEnd_4609695 := by
    simpa [prefixWord, tailWord_4609695, baseEnd_4609695] using wordTrace_append hprefix tailTrace_4609695
  have hstable : (prefixWord ++ tailWord_4609695).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4609695).length < 2 ^ (prefixWord ++ tailWord_4609695).sum := by decide
  have hdescent : baseEnd_4609695 < baseStart_4609695 := by decide
  rcases family_descends (prefixWord ++ tailWord_4609695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4609721 : List Nat := [1, 2, 1, 4, 1, 1, 2, 4, 1, 4, 2]
def baseStart_4609721 : Nat := 118140960795 + 4609721 * 2 ^ 59
def prefixEnd_4609721 : Nat := 4983230072969 + 3 ^ 40 * 4609721 * 2
def baseEnd_4609721 : Nat := 2367002556124464179087785

theorem tailTrace_4609721 : CollatzResearch.WordTrace tailWord_4609721 prefixEnd_4609721 2367002556124464179087785 := by
  unfold tailWord_4609721
  simp only [CollatzResearch.WordTrace]
  refine ⟨168130337332775569513533017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112086891555183713009022011 168130337332775569513533017)
  ·
    refine ⟨126097752999581677135149763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 168130337332775569513533017 126097752999581677135149763)
    ·
      refine ⟨189146629499372515702724645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 126097752999581677135149763 189146629499372515702724645)
      ·
        refine ⟨35464993031132346694260871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 189146629499372515702724645 35464993031132346694260871)
        ·
          refine ⟨53197489546698520041391307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35464993031132346694260871 53197489546698520041391307)
          ·
            refine ⟨79796234320047780062086961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53197489546698520041391307 79796234320047780062086961)
            ·
              refine ⟨59847175740035835046565221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 79796234320047780062086961 59847175740035835046565221)
              ·
                refine ⟨11221345451256719071230979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 59847175740035835046565221 11221345451256719071230979)
                ·
                  refine ⟨16832018176885078606846469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11221345451256719071230979 16832018176885078606846469)
                  ·
                    refine ⟨3156003408165952238783713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16832018176885078606846469 3156003408165952238783713)
                    ·
                      refine ⟨2367002556124464179087785, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3156003408165952238783713 2367002556124464179087785)
                      ·
                        rfl

theorem cell23_4609721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 2, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 2, 4, 1, 4, 2].length) (baseStart_4609721 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4609721 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4609721 prefixEnd_4609721 := by exact prefixLift 4609721
  have htrace : WordTrace (prefixWord ++ tailWord_4609721) baseStart_4609721 baseEnd_4609721 := by
    simpa [prefixWord, tailWord_4609721, baseEnd_4609721] using wordTrace_append hprefix tailTrace_4609721
  have hstable : (prefixWord ++ tailWord_4609721).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4609721).length < 2 ^ (prefixWord ++ tailWord_4609721).sum := by decide
  have hdescent : baseEnd_4609721 < baseStart_4609721 := by decide
  rcases family_descends (prefixWord ++ tailWord_4609721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4609724 : List Nat := [2, 2, 2, 3, 1, 2, 1, 1, 1, 3, 5]
def baseStart_4609724 : Nat := 118140960795 + 4609724 * 2 ^ 59
def prefixEnd_4609724 : Nat := 4983230072969 + 3 ^ 40 * 4609724 * 2
def baseEnd_4609724 : Nat := 2367004096566427667350271

theorem tailTrace_4609724 : CollatzResearch.WordTrace tailWord_4609724 prefixEnd_4609724 2367004096566427667350271 := by
  unfold tailWord_4609724
  simp only [CollatzResearch.WordTrace]
  refine ⟨84065223375882350512946113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 112086964501176467350594817 84065223375882350512946113)
  ·
    refine ⟨63048917531911762884709585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 84065223375882350512946113 63048917531911762884709585)
    ·
      refine ⟨47286688148933822163532189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 63048917531911762884709585 47286688148933822163532189)
      ·
        refine ⟨17732508055850183311324571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 47286688148933822163532189 17732508055850183311324571)
        ·
          refine ⟨26598762083775274966986857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17732508055850183311324571 26598762083775274966986857)
          ·
            refine ⟨19949071562831456225240143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26598762083775274966986857 19949071562831456225240143)
            ·
              refine ⟨29923607344247184337860215, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19949071562831456225240143 29923607344247184337860215)
              ·
                refine ⟨44885411016370776506790323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29923607344247184337860215 44885411016370776506790323)
                ·
                  refine ⟨67328116524556164760185485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 44885411016370776506790323 67328116524556164760185485)
                  ·
                    refine ⟨25248043696708561785069557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 67328116524556164760185485 25248043696708561785069557)
                    ·
                      refine ⟨2367004096566427667350271, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25248043696708561785069557 2367004096566427667350271)
                      ·
                        rfl

theorem cell23_4609724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 1, 1, 1, 3, 5].length) (baseStart_4609724 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4609724 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4609724 prefixEnd_4609724 := by exact prefixLift 4609724
  have htrace : WordTrace (prefixWord ++ tailWord_4609724) baseStart_4609724 baseEnd_4609724 := by
    simpa [prefixWord, tailWord_4609724, baseEnd_4609724] using wordTrace_append hprefix tailTrace_4609724
  have hstable : (prefixWord ++ tailWord_4609724).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4609724).length < 2 ^ (prefixWord ++ tailWord_4609724).sum := by decide
  have hdescent : baseEnd_4609724 < baseStart_4609724 := by decide
  rcases family_descends (prefixWord ++ tailWord_4609724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4609828 : List Nat := [2, 3, 1, 3, 2, 1, 3, 1, 2, 1, 4]
def baseStart_4609828 : Nat := 118140960795 + 4609828 * 2 ^ 59
def prefixEnd_4609828 : Nat := 4983230072969 + 3 ^ 40 * 4609828 * 2
def baseEnd_4609828 : Nat := 2367057498554495260449793

theorem tailTrace_4609828 : CollatzResearch.WordTrace tailWord_4609828 prefixEnd_4609828 2367057498554495260449793 := by
  unfold tailWord_4609828
  simp only [CollatzResearch.WordTrace]
  refine ⟨84067119971693963393839069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 112089493295591951191785425 84067119971693963393839069)
  ·
    refine ⟨31525169989385236272689651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 84067119971693963393839069 31525169989385236272689651)
    ·
      refine ⟨47287754984077854409034477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31525169989385236272689651 47287754984077854409034477)
      ·
        refine ⟨17732908119029195403387929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 47287754984077854409034477 17732908119029195403387929)
        ·
          refine ⟨13299681089271896552540947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17732908119029195403387929 13299681089271896552540947)
          ·
            refine ⟨19949521633907844828811421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13299681089271896552540947 19949521633907844828811421)
            ·
              refine ⟨7481070612715441810804283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19949521633907844828811421 7481070612715441810804283)
              ·
                refine ⟨11221605919073162716206425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7481070612715441810804283 11221605919073162716206425)
                ·
                  refine ⟨8416204439304872037154819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11221605919073162716206425 8416204439304872037154819)
                  ·
                    refine ⟨12624306658957308055732229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8416204439304872037154819 12624306658957308055732229)
                    ·
                      refine ⟨2367057498554495260449793, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12624306658957308055732229 2367057498554495260449793)
                      ·
                        rfl

theorem cell23_4609828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 3, 1, 2, 1, 4].length) (baseStart_4609828 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4609828 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4609828 prefixEnd_4609828 := by exact prefixLift 4609828
  have htrace : WordTrace (prefixWord ++ tailWord_4609828) baseStart_4609828 baseEnd_4609828 := by
    simpa [prefixWord, tailWord_4609828, baseEnd_4609828] using wordTrace_append hprefix tailTrace_4609828
  have hstable : (prefixWord ++ tailWord_4609828).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4609828).length < 2 ^ (prefixWord ++ tailWord_4609828).sum := by decide
  have hdescent : baseEnd_4609828 < baseStart_4609828 := by decide
  rcases family_descends (prefixWord ++ tailWord_4609828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4609862 : List Nat := [6, 1, 1, 2, 1, 1, 2, 1, 2, 4, 2]
def baseStart_4609862 : Nat := 118140960795 + 4609862 * 2 ^ 59
def prefixEnd_4609862 : Nat := 4983230072969 + 3 ^ 40 * 4609862 * 2
def baseEnd_4609862 : Nat := 2367074956896748127424637

theorem tailTrace_4609862 : CollatzResearch.WordTrace tailWord_4609862 prefixEnd_4609862 2367074956896748127424637 := by
  unfold tailWord_4609862
  simp only [CollatzResearch.WordTrace]
  refine ⟨5254233750789523456075495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 112090320016843167062943893 5254233750789523456075495)
  ·
    refine ⟨7881350626184285184113243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5254233750789523456075495 7881350626184285184113243)
    ·
      refine ⟨11822025939276427776169865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7881350626184285184113243 11822025939276427776169865)
      ·
        refine ⟨8866519454457320832127399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11822025939276427776169865 8866519454457320832127399)
        ·
          refine ⟨13299779181685981248191099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8866519454457320832127399 13299779181685981248191099)
          ·
            refine ⟨19949668772528971872286649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13299779181685981248191099 19949668772528971872286649)
            ·
              refine ⟨14962251579396728904214987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19949668772528971872286649 14962251579396728904214987)
              ·
                refine ⟨22443377369095093356322481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14962251579396728904214987 22443377369095093356322481)
                ·
                  refine ⟨16832533026821320017241861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22443377369095093356322481 16832533026821320017241861)
                  ·
                    refine ⟨3156099942528997503232849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16832533026821320017241861 3156099942528997503232849)
                    ·
                      refine ⟨2367074956896748127424637, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3156099942528997503232849 2367074956896748127424637)
                      ·
                        rfl

theorem cell23_4609862_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 2, 1, 2, 4, 2].length) (baseStart_4609862 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4609862 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4609862 prefixEnd_4609862 := by exact prefixLift 4609862
  have htrace : WordTrace (prefixWord ++ tailWord_4609862) baseStart_4609862 baseEnd_4609862 := by
    simpa [prefixWord, tailWord_4609862, baseEnd_4609862] using wordTrace_append hprefix tailTrace_4609862
  have hstable : (prefixWord ++ tailWord_4609862).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4609862).length < 2 ^ (prefixWord ++ tailWord_4609862).sum := by decide
  have hdescent : baseEnd_4609862 < baseStart_4609862 := by decide
  rcases family_descends (prefixWord ++ tailWord_4609862) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4609888 : List Nat := [2, 1, 1, 3, 3, 2, 2, 1, 1, 5, 2]
def baseStart_4609888 : Nat := 118140960795 + 4609888 * 2 ^ 59
def prefixEnd_4609888 : Nat := 4983230072969 + 3 ^ 40 * 4609888 * 2
def baseEnd_4609888 : Nat := 2367088307393765025699517

theorem tailTrace_4609888 : CollatzResearch.WordTrace tailWord_4609888 prefixEnd_4609888 2367088307393765025699517 := by
  unfold tailWord_4609888
  simp only [CollatzResearch.WordTrace]
  refine ⟨84068214161585278517431159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 112090952215447038023241545 84068214161585278517431159)
  ·
    refine ⟨126102321242377917776146739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84068214161585278517431159 126102321242377917776146739)
    ·
      refine ⟨189153481863566876664220109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 126102321242377917776146739 189153481863566876664220109)
      ·
        refine ⟨70932555698837578749082541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 189153481863566876664220109 70932555698837578749082541)
        ·
          refine ⟨26599708387064092030905953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 70932555698837578749082541 26599708387064092030905953)
          ·
            refine ⟨19949781290298069023179465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26599708387064092030905953 19949781290298069023179465)
            ·
              refine ⟨14962335967723551767384599, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19949781290298069023179465 14962335967723551767384599)
              ·
                refine ⟨22443503951585327651076899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14962335967723551767384599 22443503951585327651076899)
                ·
                  refine ⟨33665255927377991476615349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22443503951585327651076899 33665255927377991476615349)
                  ·
                    refine ⟨3156117743191686700932689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 33665255927377991476615349 3156117743191686700932689)
                    ·
                      refine ⟨2367088307393765025699517, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3156117743191686700932689 2367088307393765025699517)
                      ·
                        rfl

theorem cell23_4609888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 2, 1, 1, 5, 2].length) (baseStart_4609888 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4609888 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4609888 prefixEnd_4609888 := by exact prefixLift 4609888
  have htrace : WordTrace (prefixWord ++ tailWord_4609888) baseStart_4609888 baseEnd_4609888 := by
    simpa [prefixWord, tailWord_4609888, baseEnd_4609888] using wordTrace_append hprefix tailTrace_4609888
  have hstable : (prefixWord ++ tailWord_4609888).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4609888).length < 2 ^ (prefixWord ++ tailWord_4609888).sum := by decide
  have hdescent : baseEnd_4609888 < baseStart_4609888 := by decide
  rcases family_descends (prefixWord ++ tailWord_4609888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4609931 : List Nat := [1, 1, 1, 1, 4, 2, 1, 5, 1, 2, 4]
def baseStart_4609931 : Nat := 118140960795 + 4609931 * 2 ^ 59
def prefixEnd_4609931 : Nat := 4983230072969 + 3 ^ 40 * 4609931 * 2
def baseEnd_4609931 : Nat := 2367110387061908357461819

theorem tailTrace_4609931 : CollatzResearch.WordTrace tailWord_4609931 prefixEnd_4609931 2367110387061908357461819 := by
  unfold tailWord_4609931
  simp only [CollatzResearch.WordTrace]
  refine ⟨168137996662014775378677647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112091997774676516919118431 168137996662014775378677647)
  ·
    refine ⟨252206994993022163068016471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 168137996662014775378677647 252206994993022163068016471)
    ·
      refine ⟨378310492489533244602024707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 252206994993022163068016471 378310492489533244602024707)
      ·
        refine ⟨567465738734299866903037061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 378310492489533244602024707 567465738734299866903037061)
        ·
          refine ⟨106399826012681225044319449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 567465738734299866903037061 106399826012681225044319449)
          ·
            refine ⟨79799869509510918783239587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 106399826012681225044319449 79799869509510918783239587)
            ·
              refine ⟨119699804264266378174859381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 79799869509510918783239587 119699804264266378174859381)
              ·
                refine ⟨11221856649774972953893067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 119699804264266378174859381 11221856649774972953893067)
                ·
                  refine ⟨16832784974662459430839601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11221856649774972953893067 16832784974662459430839601)
                  ·
                    refine ⟨12624588730996844573129701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16832784974662459430839601 12624588730996844573129701)
                    ·
                      refine ⟨2367110387061908357461819, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12624588730996844573129701 2367110387061908357461819)
                      ·
                        rfl

theorem cell23_4609931_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 1, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 1, 5, 1, 2, 4].length) (baseStart_4609931 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4609931 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4609931 prefixEnd_4609931 := by exact prefixLift 4609931
  have htrace : WordTrace (prefixWord ++ tailWord_4609931) baseStart_4609931 baseEnd_4609931 := by
    simpa [prefixWord, tailWord_4609931, baseEnd_4609931] using wordTrace_append hprefix tailTrace_4609931
  have hstable : (prefixWord ++ tailWord_4609931).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4609931).length < 2 ^ (prefixWord ++ tailWord_4609931).sum := by decide
  have hdescent : baseEnd_4609931 < baseStart_4609931 := by decide
  rcases family_descends (prefixWord ++ tailWord_4609931) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4609948 : List Nat := [2, 2, 3, 3, 1, 1, 1, 1, 3, 2, 4]
def baseStart_4609948 : Nat := 118140960795 + 4609948 * 2 ^ 59
def prefixEnd_4609948 : Nat := 4983230072969 + 3 ^ 40 * 4609948 * 2
def baseEnd_4609948 : Nat := 2367119116233034790949241

theorem tailTrace_4609948 : CollatzResearch.WordTrace tailWord_4609948 prefixEnd_4609948 2367119116233034790949241 := by
  unfold tailWord_4609948
  simp only [CollatzResearch.WordTrace]
  refine ⟨84069308351476593641023249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 112092411135302124854697665 84069308351476593641023249)
  ·
    refine ⟨63051981263607445230767437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 84069308351476593641023249 63051981263607445230767437)
    ·
      refine ⟨23644492973852791961537789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 63051981263607445230767437 23644492973852791961537789)
      ·
        refine ⟨8866684865194796985576671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23644492973852791961537789 8866684865194796985576671)
        ·
          refine ⟨13300027297792195478365007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8866684865194796985576671 13300027297792195478365007)
          ·
            refine ⟨19950040946688293217547511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13300027297792195478365007 19950040946688293217547511)
            ·
              refine ⟨29925061420032439826321267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19950040946688293217547511 29925061420032439826321267)
              ·
                refine ⟨44887592130048659739481901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29925061420032439826321267 44887592130048659739481901)
                ·
                  refine ⟨16832847048768247402305713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 44887592130048659739481901 16832847048768247402305713)
                  ·
                    refine ⟨12624635286576185551729285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16832847048768247402305713 12624635286576185551729285)
                    ·
                      refine ⟨2367119116233034790949241, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12624635286576185551729285 2367119116233034790949241)
                      ·
                        rfl

theorem cell23_4609948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 1, 1, 3, 2, 4].length) (baseStart_4609948 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4609948 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4609948 prefixEnd_4609948 := by exact prefixLift 4609948
  have htrace : WordTrace (prefixWord ++ tailWord_4609948) baseStart_4609948 baseEnd_4609948 := by
    simpa [prefixWord, tailWord_4609948, baseEnd_4609948] using wordTrace_append hprefix tailTrace_4609948
  have hstable : (prefixWord ++ tailWord_4609948).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4609948).length < 2 ^ (prefixWord ++ tailWord_4609948).sum := by decide
  have hdescent : baseEnd_4609948 < baseStart_4609948 := by decide
  rcases family_descends (prefixWord ++ tailWord_4609948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4609952 : List Nat := [2, 1, 1, 4, 1, 1, 1, 7, 1, 2, 2]
def baseStart_4609952 : Nat := 118140960795 + 4609952 * 2 ^ 59
def prefixEnd_4609952 : Nat := 4983230072969 + 3 ^ 40 * 4609952 * 2
def baseEnd_4609952 : Nat := 2367121170155652775299223

theorem tailTrace_4609952 : CollatzResearch.WordTrace tailWord_4609952 prefixEnd_4609952 2367121170155652775299223 := by
  unfold tailWord_4609952
  simp only [CollatzResearch.WordTrace]
  refine ⟨84069381297469347982596055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 112092508396625797310128073 84069381297469347982596055)
  ·
    refine ⟨126104071946204021973894083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84069381297469347982596055 126104071946204021973894083)
    ·
      refine ⟨189156107919306032960841125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 126104071946204021973894083 189156107919306032960841125)
      ·
        refine ⟨35466770234869881180157711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 189156107919306032960841125 35466770234869881180157711)
        ·
          refine ⟨53200155352304821770236567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35466770234869881180157711 53200155352304821770236567)
          ·
            refine ⟨79800233028457232655354851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53200155352304821770236567 79800233028457232655354851)
            ·
              refine ⟨119700349542685848983032277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 79800233028457232655354851 119700349542685848983032277)
              ·
                refine ⟨2805476942406699585539819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 119700349542685848983032277 2805476942406699585539819)
                ·
                  refine ⟨4208215413610049378309729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2805476942406699585539819 4208215413610049378309729)
                  ·
                    refine ⟨3156161560207537033732297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4208215413610049378309729 3156161560207537033732297)
                    ·
                      refine ⟨2367121170155652775299223, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3156161560207537033732297 2367121170155652775299223)
                      ·
                        rfl

theorem cell23_4609952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 1, 7, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 1, 7, 1, 2, 2].length) (baseStart_4609952 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4609952 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4609952 prefixEnd_4609952 := by exact prefixLift 4609952
  have htrace : WordTrace (prefixWord ++ tailWord_4609952) baseStart_4609952 baseEnd_4609952 := by
    simpa [prefixWord, tailWord_4609952, baseEnd_4609952] using wordTrace_append hprefix tailTrace_4609952
  have hstable : (prefixWord ++ tailWord_4609952).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4609952).length < 2 ^ (prefixWord ++ tailWord_4609952).sum := by decide
  have hdescent : baseEnd_4609952 < baseStart_4609952 := by decide
  rcases family_descends (prefixWord ++ tailWord_4609952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4609969 : List Nat := [1, 2, 2, 4, 2, 2, 1, 4, 1, 2, 2]
def baseStart_4609969 : Nat := 118140960795 + 4609969 * 2 ^ 59
def prefixEnd_4609969 : Nat := 4983230072969 + 3 ^ 40 * 4609969 * 2
def baseEnd_4609969 : Nat := 2367129899326779208786645

theorem tailTrace_4609969 : CollatzResearch.WordTrace tailWord_4609969 prefixEnd_4609969 2367129899326779208786645 := by
  unfold tailWord_4609969
  simp only [CollatzResearch.WordTrace]
  refine ⟨168139382635877107868560961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112092921757251405245707307 168139382635877107868560961)
  ·
    refine ⟨126104536976907830901420721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 168139382635877107868560961 126104536976907830901420721)
    ·
      refine ⟨94578402732680873176065541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 126104536976907830901420721 94578402732680873176065541)
      ·
        refine ⟨17733450512377663720512289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 94578402732680873176065541 17733450512377663720512289)
        ·
          refine ⟨13300087884283247790384217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17733450512377663720512289 13300087884283247790384217)
          ·
            refine ⟨9975065913212435842788163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13300087884283247790384217 9975065913212435842788163)
            ·
              refine ⟨14962598869818653764182245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9975065913212435842788163 14962598869818653764182245)
              ·
                refine ⟨2805487288090997580784171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14962598869818653764182245 2805487288090997580784171)
                ·
                  refine ⟨4208230932136496371176257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2805487288090997580784171 4208230932136496371176257)
                  ·
                    refine ⟨3156173199102372278382193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4208230932136496371176257 3156173199102372278382193)
                    ·
                      refine ⟨2367129899326779208786645, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3156173199102372278382193 2367129899326779208786645)
                      ·
                        rfl

theorem cell23_4609969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 2, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 2, 1, 4, 1, 2, 2].length) (baseStart_4609969 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4609969 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4609969 prefixEnd_4609969 := by exact prefixLift 4609969
  have htrace : WordTrace (prefixWord ++ tailWord_4609969) baseStart_4609969 baseEnd_4609969 := by
    simpa [prefixWord, tailWord_4609969, baseEnd_4609969] using wordTrace_append hprefix tailTrace_4609969
  have hstable : (prefixWord ++ tailWord_4609969).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4609969).length < 2 ^ (prefixWord ++ tailWord_4609969).sum := by decide
  have hdescent : baseEnd_4609969 < baseStart_4609969 := by decide
  rcases family_descends (prefixWord ++ tailWord_4609969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4609991 : List Nat := [1, 1, 4, 1, 1, 2, 1, 1, 4, 3, 4]
def baseStart_4609991 : Nat := 118140960795 + 4609991 * 2 ^ 59
def prefixEnd_4609991 : Nat := 4983230072969 + 3 ^ 40 * 4609991 * 2
def baseEnd_4609991 : Nat := 2367141195901178122711543

theorem tailTrace_4609991 : CollatzResearch.WordTrace tailWord_4609991 prefixEnd_4609991 2367141195901178122711543 := by
  unfold tailWord_4609991
  simp only [CollatzResearch.WordTrace]
  refine ⟨168140185041797405625861827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112093456694531603750574551 168140185041797405625861827)
  ·
    refine ⟨252210277562696108438792741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 168140185041797405625861827 252210277562696108438792741)
    ·
      refine ⟨47289427043005520332273639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 252210277562696108438792741 47289427043005520332273639)
      ·
        refine ⟨70934140564508280498410459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47289427043005520332273639 70934140564508280498410459)
        ·
          refine ⟨106401210846762420747615689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 70934140564508280498410459 106401210846762420747615689)
          ·
            refine ⟨79800908135071815560711767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 106401210846762420747615689 79800908135071815560711767)
            ·
              refine ⟨119701362202607723341067651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 79800908135071815560711767 119701362202607723341067651)
              ·
                refine ⟨179552043303911585011601477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 119701362202607723341067651 179552043303911585011601477)
                ·
                  refine ⟨33666008119483422189675277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 179552043303911585011601477 33666008119483422189675277)
                  ·
                    refine ⟨12624753044806283321128229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 33666008119483422189675277 12624753044806283321128229)
                    ·
                      refine ⟨2367141195901178122711543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12624753044806283321128229 2367141195901178122711543)
                      ·
                        rfl

theorem cell23_4609991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 1, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 1, 1, 4, 3, 4].length) (baseStart_4609991 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4609991 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4609991 prefixEnd_4609991 := by exact prefixLift 4609991
  have htrace : WordTrace (prefixWord ++ tailWord_4609991) baseStart_4609991 baseEnd_4609991 := by
    simpa [prefixWord, tailWord_4609991, baseEnd_4609991] using wordTrace_append hprefix tailTrace_4609991
  have hstable : (prefixWord ++ tailWord_4609991).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4609991).length < 2 ^ (prefixWord ++ tailWord_4609991).sum := by decide
  have hdescent : baseEnd_4609991 < baseStart_4609991 := by decide
  rcases family_descends (prefixWord ++ tailWord_4609991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4609995 : List Nat := [1, 1, 1, 1, 3, 4, 2, 4, 1, 3, 2]
def baseStart_4609995 : Nat := 118140960795 + 4609995 * 2 ^ 59
def prefixEnd_4609995 : Nat := 4983230072969 + 3 ^ 40 * 4609995 * 2
def baseEnd_4609995 : Nat := 2367143249823796107061525

theorem tailTrace_4609995 : CollatzResearch.WordTrace tailWord_4609995 prefixEnd_4609995 2367143249823796107061525 := by
  unfold tailWord_4609995
  simp only [CollatzResearch.WordTrace]
  refine ⟨168140330933782914309007439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112093553955855276206004959 168140330933782914309007439)
  ·
    refine ⟨252210496400674371463511159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 168140330933782914309007439 252210496400674371463511159)
    ·
      refine ⟨378315744601011557195266739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 252210496400674371463511159 378315744601011557195266739)
      ·
        refine ⟨567473616901517335792900109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 378315744601011557195266739 567473616901517335792900109)
        ·
          refine ⟨212802606338069000922337541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 567473616901517335792900109 212802606338069000922337541)
          ·
            refine ⟨39900488688387937672938289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 212802606338069000922337541 39900488688387937672938289)
            ·
              refine ⟨29925366516290953254703717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 39900488688387937672938289 29925366516290953254703717)
              ·
                refine ⟨5611006221804553735256947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 29925366516290953254703717 5611006221804553735256947)
                ·
                  refine ⟨8416509332706830602885421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5611006221804553735256947 8416509332706830602885421)
                  ·
                    refine ⟨3156190999765061476082033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8416509332706830602885421 3156190999765061476082033)
                    ·
                      refine ⟨2367143249823796107061525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3156190999765061476082033 2367143249823796107061525)
                      ·
                        rfl

theorem cell23_4609995_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 2, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 2, 4, 1, 3, 2].length) (baseStart_4609995 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4609995 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4609995 prefixEnd_4609995 := by exact prefixLift 4609995
  have htrace : WordTrace (prefixWord ++ tailWord_4609995) baseStart_4609995 baseEnd_4609995 := by
    simpa [prefixWord, tailWord_4609995, baseEnd_4609995] using wordTrace_append hprefix tailTrace_4609995
  have hstable : (prefixWord ++ tailWord_4609995).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4609995).length < 2 ^ (prefixWord ++ tailWord_4609995).sum := by decide
  have hdescent : baseEnd_4609995 < baseStart_4609995 := by decide
  rcases family_descends (prefixWord ++ tailWord_4609995) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4610006 : List Nat := [5, 2, 1, 1, 3, 2, 2, 1, 1, 2, 3]
def baseStart_4610006 : Nat := 118140960795 + 4610006 * 2 ^ 59
def prefixEnd_4610006 : Nat := 4983230072969 + 3 ^ 40 * 4610006 * 2
def baseEnd_4610006 : Nat := 2367148898110995564023975

theorem tailTrace_4610006 : CollatzResearch.WordTrace tailWord_4610006 prefixEnd_4610006 2367148898110995564023975 := by
  unfold tailWord_4610006
  simp only [CollatzResearch.WordTrace]
  refine ⟨10508795758546441449228617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 112093821424495375458438581 10508795758546441449228617)
  ·
    refine ⟨7881596818909831086921463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10508795758546441449228617 7881596818909831086921463)
    ·
      refine ⟨11822395228364746630382195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7881596818909831086921463 11822395228364746630382195)
      ·
        refine ⟨17733592842547119945573293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11822395228364746630382195 17733592842547119945573293)
        ·
          refine ⟨6650097315955169979589985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17733592842547119945573293 6650097315955169979589985)
          ·
            refine ⟨4987572986966377484692489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6650097315955169979589985 4987572986966377484692489)
            ·
              refine ⟨3740679740224783113519367, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4987572986966377484692489 3740679740224783113519367)
              ·
                refine ⟨5611019610337174670279051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3740679740224783113519367 5611019610337174670279051)
                ·
                  refine ⟨8416529415505762005418577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5611019610337174670279051 8416529415505762005418577)
                  ·
                    refine ⟨6312397061629321504063933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8416529415505762005418577 6312397061629321504063933)
                    ·
                      refine ⟨2367148898110995564023975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6312397061629321504063933 2367148898110995564023975)
                      ·
                        rfl

theorem cell23_4610006_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 3, 2, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 3, 2, 2, 1, 1, 2, 3].length) (baseStart_4610006 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4610006 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4610006 prefixEnd_4610006 := by exact prefixLift 4610006
  have htrace : WordTrace (prefixWord ++ tailWord_4610006) baseStart_4610006 baseEnd_4610006 := by
    simpa [prefixWord, tailWord_4610006, baseEnd_4610006] using wordTrace_append hprefix tailTrace_4610006
  have hstable : (prefixWord ++ tailWord_4610006).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4610006).length < 2 ^ (prefixWord ++ tailWord_4610006).sum := by decide
  have hdescent : baseEnd_4610006 < baseStart_4610006 := by decide
  rcases family_descends (prefixWord ++ tailWord_4610006) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4610054 : List Nat := [6, 2, 1, 2, 2, 1, 1, 3, 1, 2, 2]
def baseStart_4610054 : Nat := 118140960795 + 4610054 * 2 ^ 59
def prefixEnd_4610054 : Nat := 4983230072969 + 3 ^ 40 * 4610054 * 2
def baseEnd_4610054 : Nat := 2367173545182411376223755

theorem tailTrace_4610054 : CollatzResearch.WordTrace tailWord_4610054 prefixEnd_4610054 2367173545182411376223755 := by
  unfold tailWord_4610054
  simp only [CollatzResearch.WordTrace]
  refine ⟨5254452588767786480793913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 112094988560379444923603477 5254452588767786480793913)
  ·
    refine ⟨3940839441575839860595435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5254452588767786480793913 3940839441575839860595435)
    ·
      refine ⟨5911259162363759790893153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3940839441575839860595435 5911259162363759790893153)
      ·
        refine ⟨4433444371772819843169865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5911259162363759790893153 4433444371772819843169865)
        ·
          refine ⟨3325083278829614882377399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4433444371772819843169865 3325083278829614882377399)
          ·
            refine ⟨4987624918244422323566099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3325083278829614882377399 4987624918244422323566099)
            ·
              refine ⟨7481437377366633485349149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4987624918244422323566099 7481437377366633485349149)
              ·
                refine ⟨2805539016512487557005931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7481437377366633485349149 2805539016512487557005931)
                ·
                  refine ⟨4208308524768731335508897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2805539016512487557005931 4208308524768731335508897)
                  ·
                    refine ⟨3156231393576548501631673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4208308524768731335508897 3156231393576548501631673)
                    ·
                      refine ⟨2367173545182411376223755, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3156231393576548501631673 2367173545182411376223755)
                      ·
                        rfl

theorem cell23_4610054_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 2, 1, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 2, 1, 1, 3, 1, 2, 2].length) (baseStart_4610054 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4610054 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4610054 prefixEnd_4610054 := by exact prefixLift 4610054
  have htrace : WordTrace (prefixWord ++ tailWord_4610054) baseStart_4610054 baseEnd_4610054 := by
    simpa [prefixWord, tailWord_4610054, baseEnd_4610054] using wordTrace_append hprefix tailTrace_4610054
  have hstable : (prefixWord ++ tailWord_4610054).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4610054).length < 2 ^ (prefixWord ++ tailWord_4610054).sum := by decide
  have hdescent : baseEnd_4610054 < baseStart_4610054 := by decide
  rcases family_descends (prefixWord ++ tailWord_4610054) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4610082 : List Nat := [3, 3, 1, 1, 1, 2, 5, 2, 5]
def baseStart_4610082 : Nat := 118140960795 + 4610082 * 2 ^ 59
def prefixEnd_4610082 : Nat := 4983230072969 + 3 ^ 40 * 4610082 * 2
def baseEnd_4610082 : Nat := 263020880293415251852625

theorem tailTrace_4610082 : CollatzResearch.WordTrace tailWord_4610082 prefixEnd_4610082 263020880293415251852625 := by
  unfold tailWord_4610082
  simp only [CollatzResearch.WordTrace]
  refine ⟨42035876021116932041856125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 112095669389645152111616333 42035876021116932041856125)
  ·
    refine ⟨15763453507918849515696047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 42035876021116932041856125 15763453507918849515696047)
    ·
      refine ⟨23645180261878274273544071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15763453507918849515696047 23645180261878274273544071)
      ·
        refine ⟨35467770392817411410316107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23645180261878274273544071 35467770392817411410316107)
        ·
          refine ⟨53201655589226117115474161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35467770392817411410316107 53201655589226117115474161)
          ·
            refine ⟨39901241691919587836605621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 53201655589226117115474161 39901241691919587836605621)
            ·
              refine ⟨3740741408617461359681777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 39901241691919587836605621 3740741408617461359681777)
              ·
                refine ⟨2805556056463096019761333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3740741408617461359681777 2805556056463096019761333)
                ·
                  refine ⟨263020880293415251852625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2805556056463096019761333 263020880293415251852625)
                  ·
                    rfl

theorem cell23_4610082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 5, 2, 5].length) (baseStart_4610082 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4610082 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4610082 prefixEnd_4610082 := by exact prefixLift 4610082
  have htrace : WordTrace (prefixWord ++ tailWord_4610082) baseStart_4610082 baseEnd_4610082 := by
    simpa [prefixWord, tailWord_4610082, baseEnd_4610082] using wordTrace_append hprefix tailTrace_4610082
  have hstable : (prefixWord ++ tailWord_4610082).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4610082).length < 2 ^ (prefixWord ++ tailWord_4610082).sum := by decide
  have hdescent : baseEnd_4610082 < baseStart_4610082 := by decide
  rcases family_descends (prefixWord ++ tailWord_4610082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4610091 : List Nat := [1, 1, 1, 1, 2, 1, 4, 2, 2, 8]
def baseStart_4610091 : Nat := 118140960795 + 4610091 * 2 ^ 59
def prefixEnd_4610091 : Nat := 4983230072969 + 3 ^ 40 * 4610091 * 2
def baseEnd_4610091 : Nat := 789064181322209243820361

theorem tailTrace_4610091 : CollatzResearch.WordTrace tailWord_4610091 prefixEnd_4610091 789064181322209243820361 := by
  unfold tailWord_4610091
  simp only [CollatzResearch.WordTrace]
  refine ⟨168143832341435122704502127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112095888227623415136334751 168143832341435122704502127)
  ·
    refine ⟨252215748512152684056753191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 168143832341435122704502127 252215748512152684056753191)
    ·
      refine ⟨378323622768229026085129787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 252215748512152684056753191 378323622768229026085129787)
      ·
        refine ⟨567485434152343539127694681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 378323622768229026085129787 567485434152343539127694681)
        ·
          refine ⟨425614075614257654345771011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 567485434152343539127694681 425614075614257654345771011)
          ·
            refine ⟨638421113421386481518656517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 425614075614257654345771011 638421113421386481518656517)
            ·
              refine ⟨119703958766509965284748097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 638421113421386481518656517 119703958766509965284748097)
              ·
                refine ⟨89777969074882473963561073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 119703958766509965284748097 89777969074882473963561073)
                ·
                  refine ⟨67333476806161855472670805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 89777969074882473963561073 67333476806161855472670805)
                  ·
                    refine ⟨789064181322209243820361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 67333476806161855472670805 789064181322209243820361)
                    ·
                      rfl

theorem cell23_4610091_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 4, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 4, 2, 2, 8].length) (baseStart_4610091 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4610091 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4610091 prefixEnd_4610091 := by exact prefixLift 4610091
  have htrace : WordTrace (prefixWord ++ tailWord_4610091) baseStart_4610091 baseEnd_4610091 := by
    simpa [prefixWord, tailWord_4610091, baseEnd_4610091] using wordTrace_append hprefix tailTrace_4610091
  have hstable : (prefixWord ++ tailWord_4610091).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4610091).length < 2 ^ (prefixWord ++ tailWord_4610091).sum := by decide
  have hdescent : baseEnd_4610091 < baseStart_4610091 := by decide
  rcases family_descends (prefixWord ++ tailWord_4610091) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4610135 : List Nat := [1, 1, 3, 2, 2, 1, 4, 2, 2, 2, 3]
def baseStart_4610135 : Nat := 118140960795 + 4610135 * 2 ^ 59
def prefixEnd_4610135 : Nat := 4983230072969 + 3 ^ 40 * 4610135 * 2
def baseEnd_4610135 : Nat := 2367215137115425559310881

theorem tailTrace_4610135 : CollatzResearch.WordTrace tailWord_4610135 prefixEnd_4610135 2367215137115425559310881 := by
  unfold tailWord_4610135
  simp only [CollatzResearch.WordTrace]
  refine ⟨168145437153275718219103859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112096958102183812146069239 168145437153275718219103859)
  ·
    refine ⟨252218155729913577328655789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 168145437153275718219103859 252218155729913577328655789)
    ·
      refine ⟨94581808398717591498245921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 252218155729913577328655789 94581808398717591498245921)
      ·
        refine ⟨70936356299038193623684441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 94581808398717591498245921 70936356299038193623684441)
        ·
          refine ⟨53202267224278645217763331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 70936356299038193623684441 53202267224278645217763331)
          ·
            refine ⟨79803400836417967826644997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53202267224278645217763331 79803400836417967826644997)
            ·
              refine ⟨14963137656828368967495937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 79803400836417967826644997 14963137656828368967495937)
              ·
                refine ⟨11222353242621276725621953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14963137656828368967495937 11222353242621276725621953)
                ·
                  refine ⟨8416764931965957544216465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11222353242621276725621953 8416764931965957544216465)
                  ·
                    refine ⟨6312573698974468158162349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8416764931965957544216465 6312573698974468158162349)
                    ·
                      refine ⟨2367215137115425559310881, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6312573698974468158162349 2367215137115425559310881)
                      ·
                        rfl

theorem cell23_4610135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 4, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 4, 2, 2, 2, 3].length) (baseStart_4610135 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4610135 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4610135 prefixEnd_4610135 := by exact prefixLift 4610135
  have htrace : WordTrace (prefixWord ++ tailWord_4610135) baseStart_4610135 baseEnd_4610135 := by
    simpa [prefixWord, tailWord_4610135, baseEnd_4610135] using wordTrace_append hprefix tailTrace_4610135
  have hstable : (prefixWord ++ tailWord_4610135).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4610135).length < 2 ^ (prefixWord ++ tailWord_4610135).sum := by decide
  have hdescent : baseEnd_4610135 < baseStart_4610135 := by decide
  rcases family_descends (prefixWord ++ tailWord_4610135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4610185 : List Nat := [1, 2, 1, 1, 4, 2, 3, 3, 1, 5]
def baseStart_4610185 : Nat := 118140960795 + 4610185 * 2 ^ 59
def prefixEnd_4610185 : Nat := 4983230072969 + 3 ^ 40 * 4610185 * 2
def baseEnd_4610185 : Nat := 789080270382716787895217

theorem tailTrace_4610185 : CollatzResearch.WordTrace tailWord_4610185 prefixEnd_4610185 789080270382716787895217 := by
  unfold tailWord_4610185
  simp only [CollatzResearch.WordTrace]
  refine ⟨168147260803094576758424009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112098173868729717838949339 168147260803094576758424009)
  ·
    refine ⟨126110445602320932568818007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 168147260803094576758424009 126110445602320932568818007)
    ·
      refine ⟨189165668403481398853227011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 126110445602320932568818007 189165668403481398853227011)
      ·
        refine ⟨283748502605222098279840517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 189165668403481398853227011 283748502605222098279840517)
        ·
          refine ⟨53202844238479143427470097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 283748502605222098279840517 53202844238479143427470097)
          ·
            refine ⟨39902133178859357570602573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 53202844238479143427470097 39902133178859357570602573)
            ·
              refine ⟨14963299942072259088975965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 39902133178859357570602573 14963299942072259088975965)
              ·
                refine ⟨5611237478277097158365987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14963299942072259088975965 5611237478277097158365987)
                ·
                  refine ⟨8416856217415645737548981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5611237478277097158365987 8416856217415645737548981)
                  ·
                    refine ⟨789080270382716787895217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8416856217415645737548981 789080270382716787895217)
                    ·
                      rfl

theorem cell23_4610185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 3, 3, 1, 5].length) (baseStart_4610185 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4610185 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4610185 prefixEnd_4610185 := by exact prefixLift 4610185
  have htrace : WordTrace (prefixWord ++ tailWord_4610185) baseStart_4610185 baseEnd_4610185 := by
    simpa [prefixWord, tailWord_4610185, baseEnd_4610185] using wordTrace_append hprefix tailTrace_4610185
  have hstable : (prefixWord ++ tailWord_4610185).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4610185).length < 2 ^ (prefixWord ++ tailWord_4610185).sum := by decide
  have hdescent : baseEnd_4610185 < baseStart_4610185 := by decide
  rcases family_descends (prefixWord ++ tailWord_4610185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4610199 : List Nat := [1, 1, 3, 3, 4, 1, 2, 1, 3, 1, 3]
def baseStart_4610199 : Nat := 118140960795 + 4610199 * 2 ^ 59
def prefixEnd_4610199 : Nat := 4983230072969 + 3 ^ 40 * 4610199 * 2
def baseEnd_4610199 : Nat := 2367247999877313308910587

theorem tailTrace_4610199 : CollatzResearch.WordTrace tailWord_4610199 prefixEnd_4610199 2367247999877313308910587 := by
  unfold tailWord_4610199
  simp only [CollatzResearch.WordTrace]
  refine ⟨168147771425043857149433651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112098514283362571432955767 168147771425043857149433651)
  ·
    refine ⟨252221657137565785724150477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 168147771425043857149433651 252221657137565785724150477)
    ·
      refine ⟨94583121426587169646556429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 252221657137565785724150477 94583121426587169646556429)
      ·
        refine ⟨35468670534970188617458661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 94583121426587169646556429 35468670534970188617458661)
        ·
          refine ⟨6650375725306910365773499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 35468670534970188617458661 6650375725306910365773499)
          ·
            refine ⟨9975563587960365548660249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6650375725306910365773499 9975563587960365548660249)
            ·
              refine ⟨7481672690970274161495187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9975563587960365548660249 7481672690970274161495187)
              ·
                refine ⟨11222509036455411242242781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7481672690970274161495187 11222509036455411242242781)
                ·
                  refine ⟨4208440888670779215841043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11222509036455411242242781 4208440888670779215841043)
                  ·
                    refine ⟨6312661333006168823761565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4208440888670779215841043 6312661333006168823761565)
                    ·
                      refine ⟨2367247999877313308910587, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6312661333006168823761565 2367247999877313308910587)
                      ·
                        rfl

theorem cell23_4610199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 4, 1, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 4, 1, 2, 1, 3, 1, 3].length) (baseStart_4610199 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4610199 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4610199 prefixEnd_4610199 := by exact prefixLift 4610199
  have htrace : WordTrace (prefixWord ++ tailWord_4610199) baseStart_4610199 baseEnd_4610199 := by
    simpa [prefixWord, tailWord_4610199, baseEnd_4610199] using wordTrace_append hprefix tailTrace_4610199
  have hstable : (prefixWord ++ tailWord_4610199).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4610199).length < 2 ^ (prefixWord ++ tailWord_4610199).sum := by decide
  have hdescent : baseEnd_4610199 < baseStart_4610199 := by decide
  rcases family_descends (prefixWord ++ tailWord_4610199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4610262 : List Nat := [5, 2, 1, 2, 1, 1, 1, 10]
def baseStart_4610262 : Nat := 118140960795 + 4610262 * 2 ^ 59
def prefixEnd_4610262 : Nat := 4983230072969 + 3 ^ 40 * 4610262 * 2
def baseEnd_4610262 : Nat := 87677049968835057867511

theorem tailTrace_4610262 : CollatzResearch.WordTrace tailWord_4610262 prefixEnd_4610262 87677049968835057867511 := by
  unfold tailWord_4610262
  simp only [CollatzResearch.WordTrace]
  refine ⟨10509379326488476181811065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 112100046149210412605984693 10509379326488476181811065)
  ·
    refine ⟨7882034494866357136358299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10509379326488476181811065 7882034494866357136358299)
    ·
      refine ⟨11823051742299535704537449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7882034494866357136358299 11823051742299535704537449)
      ·
        refine ⟨8867288806724651778403087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11823051742299535704537449 8867288806724651778403087)
        ·
          refine ⟨13300933210086977667604631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8867288806724651778403087 13300933210086977667604631)
          ·
            refine ⟨19951399815130466501406947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13300933210086977667604631 19951399815130466501406947)
            ·
              refine ⟨29927099722695699752110421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19951399815130466501406947 29927099722695699752110421)
              ·
                refine ⟨87677049968835057867511, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 29927099722695699752110421 87677049968835057867511)
                ·
                  rfl

theorem cell23_4610262_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 1, 10].length) (baseStart_4610262 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4610262 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4610262 prefixEnd_4610262 := by exact prefixLift 4610262
  have htrace : WordTrace (prefixWord ++ tailWord_4610262) baseStart_4610262 baseEnd_4610262 := by
    simpa [prefixWord, tailWord_4610262, baseEnd_4610262] using wordTrace_append hprefix tailTrace_4610262
  have hstable : (prefixWord ++ tailWord_4610262).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4610262).length < 2 ^ (prefixWord ++ tailWord_4610262).sum := by decide
  have hdescent : baseEnd_4610262 < baseStart_4610262 := by decide
  rcases family_descends (prefixWord ++ tailWord_4610262) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4610305 : List Nat := [1, 2, 4, 1, 1, 2, 2, 2, 2, 6]
def baseStart_4610305 : Nat := 118140960795 + 4610305 * 2 ^ 59
def prefixEnd_4610305 : Nat := 4983230072969 + 3 ^ 40 * 4610305 * 2
def baseEnd_4610305 : Nat := 789100809608896631395033

theorem tailTrace_4610305 : CollatzResearch.WordTrace tailWord_4610305 prefixEnd_4610305 789100809608896631395033 := by
  unfold tailWord_4610305
  simp only [CollatzResearch.WordTrace]
  refine ⟨168151637562659837252792369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112101091708439891501861579 168151637562659837252792369)
  ·
    refine ⟨126113728171994877939594277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 168151637562659837252792369 126113728171994877939594277)
    ·
      refine ⟨23646324032249039613673927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 126113728171994877939594277 23646324032249039613673927)
      ·
        refine ⟨35469486048373559420510891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23646324032249039613673927 35469486048373559420510891)
        ·
          refine ⟨53204229072560339130766337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35469486048373559420510891 53204229072560339130766337)
          ·
            refine ⟨39903171804420254348074753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 53204229072560339130766337 39903171804420254348074753)
            ·
              refine ⟨29927378853315190761056065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 39903171804420254348074753 29927378853315190761056065)
              ·
                refine ⟨22445534139986393070792049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29927378853315190761056065 22445534139986393070792049)
                ·
                  refine ⟨16834150604989794803094037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22445534139986393070792049 16834150604989794803094037)
                  ·
                    refine ⟨789100809608896631395033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16834150604989794803094037 789100809608896631395033)
                    ·
                      rfl

theorem cell23_4610305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 2, 2, 2, 6].length) (baseStart_4610305 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4610305 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4610305 prefixEnd_4610305 := by exact prefixLift 4610305
  have htrace : WordTrace (prefixWord ++ tailWord_4610305) baseStart_4610305 baseEnd_4610305 := by
    simpa [prefixWord, tailWord_4610305, baseEnd_4610305] using wordTrace_append hprefix tailTrace_4610305
  have hstable : (prefixWord ++ tailWord_4610305).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4610305).length < 2 ^ (prefixWord ++ tailWord_4610305).sum := by decide
  have hdescent : baseEnd_4610305 < baseStart_4610305 := by decide
  rcases family_descends (prefixWord ++ tailWord_4610305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4610306 : List Nat := [3, 4, 1, 1, 2, 1, 1, 4, 2, 1, 3]
def baseStart_4610306 : Nat := 118140960795 + 4610306 * 2 ^ 59
def prefixEnd_4610306 : Nat := 4983230072969 + 3 ^ 40 * 4610306 * 2
def baseEnd_4610306 : Nat := 2367302942307344390272595

theorem tailTrace_4610306 : CollatzResearch.WordTrace tailWord_4610306 prefixEnd_4610306 2367302942307344390272595 := by
  unfold tailWord_4610306
  simp only [CollatzResearch.WordTrace]
  refine ⟨42037918508914053605894693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 112101116023770809615719181 42037918508914053605894693)
  ·
    refine ⟨7882109720421385051105255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 42037918508914053605894693 7882109720421385051105255)
    ·
      refine ⟨11823164580632077576657883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7882109720421385051105255 11823164580632077576657883)
      ·
        refine ⟨17734746870948116364986825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11823164580632077576657883 17734746870948116364986825)
        ·
          refine ⟨13301060153211087273740119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17734746870948116364986825 13301060153211087273740119)
          ·
            refine ⟨19951590229816630910610179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13301060153211087273740119 19951590229816630910610179)
            ·
              refine ⟨29927385344724946365915269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19951590229816630910610179 29927385344724946365915269)
              ·
                refine ⟨5611384752135927443609113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 29927385344724946365915269 5611384752135927443609113)
                ·
                  refine ⟨4208538564101945582706835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5611384752135927443609113 4208538564101945582706835)
                  ·
                    refine ⟨6312807846152918374060253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4208538564101945582706835 6312807846152918374060253)
                    ·
                      refine ⟨2367302942307344390272595, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6312807846152918374060253 2367302942307344390272595)
                      ·
                        rfl

theorem cell23_4610306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 1, 4, 2, 1, 3].length) (baseStart_4610306 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4610306 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4610306 prefixEnd_4610306 := by exact prefixLift 4610306
  have htrace : WordTrace (prefixWord ++ tailWord_4610306) baseStart_4610306 baseEnd_4610306 := by
    simpa [prefixWord, tailWord_4610306, baseEnd_4610306] using wordTrace_append hprefix tailTrace_4610306
  have hstable : (prefixWord ++ tailWord_4610306).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4610306).length < 2 ^ (prefixWord ++ tailWord_4610306).sum := by decide
  have hdescent : baseEnd_4610306 < baseStart_4610306 := by decide
  rcases family_descends (prefixWord ++ tailWord_4610306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4610315 : List Nat := [1, 1, 1, 1, 5, 2, 1, 1, 1, 6, 3]
def baseStart_4610315 : Nat := 118140960795 + 4610315 * 2 ^ 59
def prefixEnd_4610315 : Nat := 4983230072969 + 3 ^ 40 * 4610315 * 2
def baseEnd_4610315 : Nat := 2367307563633234855060053

theorem tailTrace_4610315 : CollatzResearch.WordTrace tailWord_4610315 prefixEnd_4610315 2367307563633234855060053 := by
  unfold tailWord_4610315
  simp only [CollatzResearch.WordTrace]
  refine ⟨168152002292623608960656399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112101334861749072640437599 168152002292623608960656399)
  ·
    refine ⟨252228003438935413440984599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 168152002292623608960656399 252228003438935413440984599)
    ·
      refine ⟨378342005158403120161476899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 252228003438935413440984599 378342005158403120161476899)
      ·
        refine ⟨567513007737604680242215349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 378342005158403120161476899 567513007737604680242215349)
        ·
          refine ⟨53204344475400438772707689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 567513007737604680242215349 53204344475400438772707689)
          ·
            refine ⟨39903258356550329079530767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 53204344475400438772707689 39903258356550329079530767)
            ·
              refine ⟨59854887534825493619296151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39903258356550329079530767 59854887534825493619296151)
              ·
                refine ⟨89782331302238240428944227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 59854887534825493619296151 89782331302238240428944227)
                ·
                  refine ⟨134673496953357360643416341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 89782331302238240428944227 134673496953357360643416341)
                  ·
                    refine ⟨6312820169688626280160141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 134673496953357360643416341 6312820169688626280160141)
                    ·
                      refine ⟨2367307563633234855060053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6312820169688626280160141 2367307563633234855060053)
                      ·
                        rfl

theorem cell23_4610315_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 1, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 1, 1, 1, 6, 3].length) (baseStart_4610315 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4610315 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4610315 prefixEnd_4610315 := by exact prefixLift 4610315
  have htrace : WordTrace (prefixWord ++ tailWord_4610315) baseStart_4610315 baseEnd_4610315 := by
    simpa [prefixWord, tailWord_4610315, baseEnd_4610315] using wordTrace_append hprefix tailTrace_4610315
  have hstable : (prefixWord ++ tailWord_4610315).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4610315).length < 2 ^ (prefixWord ++ tailWord_4610315).sum := by decide
  have hdescent : baseEnd_4610315 < baseStart_4610315 := by decide
  rcases family_descends (prefixWord ++ tailWord_4610315) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4610325 : List Nat := [1, 3, 2, 1, 2, 1, 3, 1, 1, 4, 4]
def baseStart_4610325 : Nat := 118140960795 + 4610325 * 2 ^ 59
def prefixEnd_4610325 : Nat := 4983230072969 + 3 ^ 40 * 4610325 * 2
def baseEnd_4610325 : Nat := 2367312698439779815935007

theorem tailTrace_4610325 : CollatzResearch.WordTrace tailWord_4610325 prefixEnd_4610325 2367312698439779815935007 := by
  unfold tailWord_4610325
  simp only [CollatzResearch.WordTrace]
  refine ⟨168152367022587380668520429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112101578015058253779013619 168152367022587380668520429)
  ·
    refine ⟨63057137633470267750695161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 168152367022587380668520429 63057137633470267750695161)
    ·
      refine ⟨47292853225102700813021371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 63057137633470267750695161 47292853225102700813021371)
      ·
        refine ⟨70939279837654051219532057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47292853225102700813021371 70939279837654051219532057)
        ·
          refine ⟨53204459878240538414649043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 70939279837654051219532057 53204459878240538414649043)
          ·
            refine ⟨79806689817360807621973565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53204459878240538414649043 79806689817360807621973565)
            ·
              refine ⟨29927508681510302858240087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 79806689817360807621973565 29927508681510302858240087)
              ·
                refine ⟨44891263022265454287360131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29927508681510302858240087 44891263022265454287360131)
                ·
                  refine ⟨67336894533398181431040197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 44891263022265454287360131 67336894533398181431040197)
                  ·
                    refine ⟨12625667725012159018320037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 67336894533398181431040197 12625667725012159018320037)
                    ·
                      refine ⟨2367312698439779815935007, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12625667725012159018320037 2367312698439779815935007)
                      ·
                        rfl

theorem cell23_4610325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 3, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 3, 1, 1, 4, 4].length) (baseStart_4610325 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4610325 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4610325 prefixEnd_4610325 := by exact prefixLift 4610325
  have htrace : WordTrace (prefixWord ++ tailWord_4610325) baseStart_4610325 baseEnd_4610325 := by
    simpa [prefixWord, tailWord_4610325, baseEnd_4610325] using wordTrace_append hprefix tailTrace_4610325
  have hstable : (prefixWord ++ tailWord_4610325).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4610325).length < 2 ^ (prefixWord ++ tailWord_4610325).sum := by decide
  have hdescent : baseEnd_4610325 < baseStart_4610325 := by decide
  rcases family_descends (prefixWord ++ tailWord_4610325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4610335 : List Nat := [1, 1, 2, 4, 3, 1, 1, 1, 9]
def baseStart_4610335 : Nat := 118140960795 + 4610335 * 2 ^ 59
def prefixEnd_4610335 : Nat := 4983230072969 + 3 ^ 40 * 4610335 * 2
def baseEnd_4610335 : Nat := 263035314805147197423329

theorem tailTrace_4610335 : CollatzResearch.WordTrace tailWord_4610335 prefixEnd_4610335 263035314805147197423329 := by
  unfold tailWord_4610335
  simp only [CollatzResearch.WordTrace]
  refine ⟨168152731752551152376384459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112101821168367434917589639 168152731752551152376384459)
  ·
    refine ⟨252229097628826728564576689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 168152731752551152376384459 252229097628826728564576689)
    ·
      refine ⟨189171823221620046423432517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 252229097628826728564576689 189171823221620046423432517)
      ·
        refine ⟨35469716854053758704393597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 189171823221620046423432517 35469716854053758704393597)
        ·
          refine ⟨13301143820270159514147599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 35469716854053758704393597 13301143820270159514147599)
          ·
            refine ⟨19951715730405239271221399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13301143820270159514147599 19951715730405239271221399)
            ·
              refine ⟨29927573595607858906832099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19951715730405239271221399 29927573595607858906832099)
              ·
                refine ⟨44891360393411788360248149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29927573595607858906832099 44891360393411788360248149)
                ·
                  refine ⟨263035314805147197423329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 44891360393411788360248149 263035314805147197423329)
                  ·
                    rfl

theorem cell23_4610335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 1, 1, 9].length) (baseStart_4610335 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4610335 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4610335 prefixEnd_4610335 := by exact prefixLift 4610335
  have htrace : WordTrace (prefixWord ++ tailWord_4610335) baseStart_4610335 baseEnd_4610335 := by
    simpa [prefixWord, tailWord_4610335, baseEnd_4610335] using wordTrace_append hprefix tailTrace_4610335
  have hstable : (prefixWord ++ tailWord_4610335).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4610335).length < 2 ^ (prefixWord ++ tailWord_4610335).sum := by decide
  have hdescent : baseEnd_4610335 < baseStart_4610335 := by decide
  rcases family_descends (prefixWord ++ tailWord_4610335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4610362 : List Nat := [3, 1, 1, 1, 4, 2, 1, 2, 2, 3, 3]
def baseStart_4610362 : Nat := 118140960795 + 4610362 * 2 ^ 59
def prefixEnd_4610362 : Nat := 4983230072969 + 3 ^ 40 * 4610362 * 2
def baseEnd_4610362 : Nat := 2367331697223996171172337

theorem tailTrace_4610362 : CollatzResearch.WordTrace tailWord_4610362 prefixEnd_4610362 2367331697223996171172337 := by
  unfold tailWord_4610362
  simp only [CollatzResearch.WordTrace]
  refine ⟨42038429130863333996904335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 112102477682302223991744893 42038429130863333996904335)
  ·
    refine ⟨63057643696295000995356503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42038429130863333996904335 63057643696295000995356503)
    ·
      refine ⟨94586465544442501493034755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63057643696295000995356503 94586465544442501493034755)
      ·
        refine ⟨141879698316663752239552133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 94586465544442501493034755 141879698316663752239552133)
        ·
          refine ⟨26602443434374453544916025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 141879698316663752239552133 26602443434374453544916025)
          ·
            refine ⟨19951832575780840158687019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26602443434374453544916025 19951832575780840158687019)
            ·
              refine ⟨29927748863671260238030529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19951832575780840158687019 29927748863671260238030529)
              ·
                refine ⟨22445811647753445178522897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29927748863671260238030529 22445811647753445178522897)
                ·
                  refine ⟨16834358735815083883892173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22445811647753445178522897 16834358735815083883892173)
                  ·
                    refine ⟨6312884525930656456459565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16834358735815083883892173 6312884525930656456459565)
                    ·
                      refine ⟨2367331697223996171172337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6312884525930656456459565 2367331697223996171172337)
                      ·
                        rfl

theorem cell23_4610362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 1, 2, 2, 3, 3].length) (baseStart_4610362 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4610362 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4610362 prefixEnd_4610362 := by exact prefixLift 4610362
  have htrace : WordTrace (prefixWord ++ tailWord_4610362) baseStart_4610362 baseEnd_4610362 := by
    simpa [prefixWord, tailWord_4610362, baseEnd_4610362] using wordTrace_append hprefix tailTrace_4610362
  have hstable : (prefixWord ++ tailWord_4610362).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4610362).length < 2 ^ (prefixWord ++ tailWord_4610362).sum := by decide
  have hdescent : baseEnd_4610362 < baseStart_4610362 := by decide
  rcases family_descends (prefixWord ++ tailWord_4610362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4610369 : List Nat := [1, 2, 5, 2, 2, 1, 2, 1, 7]
def baseStart_4610369 : Nat := 118140960795 + 4610369 * 2 ^ 59
def prefixEnd_4610369 : Nat := 4983230072969 + 3 ^ 40 * 4610369 * 2
def baseEnd_4610369 : Nat := 263037254620953071531645

theorem tailTrace_4610369 : CollatzResearch.WordTrace tailWord_4610369 prefixEnd_4610369 263037254620953071531645 := by
  unfold tailWord_4610369
  simp only [CollatzResearch.WordTrace]
  refine ⟨168153971834427976183122161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112102647889618650788748107 168153971834427976183122161)
  ·
    refine ⟨126115478875820982137341621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 168153971834427976183122161 126115478875820982137341621)
    ·
      refine ⟨11823326144608217075375777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 126115478875820982137341621 11823326144608217075375777)
      ·
        refine ⟨8867494608456162806531833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11823326144608217075375777 8867494608456162806531833)
        ·
          refine ⟨6650620956342122104898875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8867494608456162806531833 6650620956342122104898875)
          ·
            refine ⟨9975931434513183157348313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6650620956342122104898875 9975931434513183157348313)
            ·
              refine ⟨7481948575884887368011235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9975931434513183157348313 7481948575884887368011235)
              ·
                refine ⟨11222922863827331052016853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7481948575884887368011235 11222922863827331052016853)
                ·
                  refine ⟨263037254620953071531645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11222922863827331052016853 263037254620953071531645)
                  ·
                    rfl

theorem cell23_4610369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 2, 1, 2, 1, 7].length) (baseStart_4610369 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4610369 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4610369 prefixEnd_4610369 := by exact prefixLift 4610369
  have htrace : WordTrace (prefixWord ++ tailWord_4610369) baseStart_4610369 baseEnd_4610369 := by
    simpa [prefixWord, tailWord_4610369, baseEnd_4610369] using wordTrace_append hprefix tailTrace_4610369
  have hstable : (prefixWord ++ tailWord_4610369).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4610369).length < 2 ^ (prefixWord ++ tailWord_4610369).sum := by decide
  have hdescent : baseEnd_4610369 < baseStart_4610369 := by decide
  rcases family_descends (prefixWord ++ tailWord_4610369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4610375 : List Nat := [1, 1, 4, 1, 2, 2, 2, 1, 1, 1, 7]
def baseStart_4610375 : Nat := 118140960795 + 4610375 * 2 ^ 59
def prefixEnd_4610375 : Nat := 4983230072969 + 3 ^ 40 * 4610375 * 2
def baseEnd_4610375 : Nat := 2367338372472504620309777

theorem tailTrace_4610375 : CollatzResearch.WordTrace tailWord_4610375 prefixEnd_4610375 2367338372472504620309777 := by
  unfold tailWord_4610375
  simp only [CollatzResearch.WordTrace]
  refine ⟨168154190672406239207840579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112102793781604159471893719 168154190672406239207840579)
  ·
    refine ⟨252231286008609358811760869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 168154190672406239207840579 252231286008609358811760869)
    ·
      refine ⟨47293366126614254777205163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 252231286008609358811760869 47293366126614254777205163)
      ·
        refine ⟨70940049189921382165807745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47293366126614254777205163 70940049189921382165807745)
        ·
          refine ⟨53205036892441036624355809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 70940049189921382165807745 53205036892441036624355809)
          ·
            refine ⟨39903777669330777468266857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 53205036892441036624355809 39903777669330777468266857)
            ·
              refine ⟨29927833251998083101200143, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 39903777669330777468266857 29927833251998083101200143)
              ·
                refine ⟨44891749877997124651800215, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29927833251998083101200143 44891749877997124651800215)
                ·
                  refine ⟨67337624816995686977700323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 44891749877997124651800215 67337624816995686977700323)
                  ·
                    refine ⟨101006437225493530466550485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 67337624816995686977700323 101006437225493530466550485)
                    ·
                      refine ⟨2367338372472504620309777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 101006437225493530466550485 2367338372472504620309777)
                      ·
                        rfl

theorem cell23_4610375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 2, 1, 1, 1, 7].length) (baseStart_4610375 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4610375 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4610375 prefixEnd_4610375 := by exact prefixLift 4610375
  have htrace : WordTrace (prefixWord ++ tailWord_4610375) baseStart_4610375 baseEnd_4610375 := by
    simpa [prefixWord, tailWord_4610375, baseEnd_4610375] using wordTrace_append hprefix tailTrace_4610375
  have hstable : (prefixWord ++ tailWord_4610375).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4610375).length < 2 ^ (prefixWord ++ tailWord_4610375).sum := by decide
  have hdescent : baseEnd_4610375 < baseStart_4610375 := by decide
  rcases family_descends (prefixWord ++ tailWord_4610375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4610415 : List Nat := [1, 1, 2, 1, 3, 1, 2, 3, 2, 1, 6]
def baseStart_4610415 : Nat := 118140960795 + 4610415 * 2 ^ 59
def prefixEnd_4610415 : Nat := 4983230072969 + 3 ^ 40 * 4610415 * 2
def baseEnd_4610415 : Nat := 2367358911698684463809593

theorem tailTrace_4610415 : CollatzResearch.WordTrace tailWord_4610415 prefixEnd_4610415 2367358911698684463809593 := by
  unfold tailWord_4610415
  simp only [CollatzResearch.WordTrace]
  refine ⟨168155649592261326039296699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112103766394840884026197799 168155649592261326039296699)
  ·
    refine ⟨252233474388391989058945049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 168155649592261326039296699 252233474388391989058945049)
    ·
      refine ⟨189175105791293991794208787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 252233474388391989058945049 189175105791293991794208787)
      ·
        refine ⟨283762658686940987691313181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 189175105791293991794208787 283762658686940987691313181)
        ·
          refine ⟨106410997007602870384242443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 283762658686940987691313181 106410997007602870384242443)
          ·
            refine ⟨159616495511404305576363665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 106410997007602870384242443 159616495511404305576363665)
            ·
              refine ⟨119712371633553229182272749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 159616495511404305576363665 119712371633553229182272749)
              ·
                refine ⟨44892139362582460943352281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 119712371633553229182272749 44892139362582460943352281)
                ·
                  refine ⟨33669104521936845707514211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 44892139362582460943352281 33669104521936845707514211)
                  ·
                    refine ⟨50503656782905268561271317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 33669104521936845707514211 50503656782905268561271317)
                    ·
                      refine ⟨2367358911698684463809593, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 50503656782905268561271317 2367358911698684463809593)
                      ·
                        rfl

theorem cell23_4610415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 2, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 2, 3, 2, 1, 6].length) (baseStart_4610415 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4610415 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4610415 prefixEnd_4610415 := by exact prefixLift 4610415
  have htrace : WordTrace (prefixWord ++ tailWord_4610415) baseStart_4610415 baseEnd_4610415 := by
    simpa [prefixWord, tailWord_4610415, baseEnd_4610415] using wordTrace_append hprefix tailTrace_4610415
  have hstable : (prefixWord ++ tailWord_4610415).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4610415).length < 2 ^ (prefixWord ++ tailWord_4610415).sum := by decide
  have hdescent : baseEnd_4610415 < baseStart_4610415 := by decide
  rcases family_descends (prefixWord ++ tailWord_4610415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4610429 : List Nat := [1, 4, 1, 1, 2, 3, 3, 1, 3, 4]
def baseStart_4610429 : Nat := 118140960795 + 4610429 * 2 ^ 59
def prefixEnd_4610429 : Nat := 4983230072969 + 3 ^ 40 * 4610429 * 2
def baseEnd_4610429 : Nat := 789122033475949136344843

theorem tailTrace_4610429 : CollatzResearch.WordTrace tailWord_4610429 prefixEnd_4610429 789122033475949136344843 := by
  unfold tailWord_4610429
  simp only [CollatzResearch.WordTrace]
  refine ⟨168156160214210606430306341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112104106809473737620204227 168156160214210606430306341)
  ·
    refine ⟨31529280040164488705682439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 168156160214210606430306341 31529280040164488705682439)
    ·
      refine ⟨47293920060246733058523659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31529280040164488705682439 47293920060246733058523659)
      ·
        refine ⟨70940880090370099587785489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47293920060246733058523659 70940880090370099587785489)
        ·
          refine ⟨53205660067777574690839117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 70940880090370099587785489 53205660067777574690839117)
          ·
            refine ⟨19952122525416590509064669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 53205660067777574690839117 19952122525416590509064669)
            ·
              refine ⟨7482045947031221440899251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19952122525416590509064669 7482045947031221440899251)
              ·
                refine ⟨11223068920546832161348877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7482045947031221440899251 11223068920546832161348877)
                ·
                  refine ⟨4208650845205062060505829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11223068920546832161348877 4208650845205062060505829)
                  ·
                    refine ⟨789122033475949136344843, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4208650845205062060505829 789122033475949136344843)
                    ·
                      rfl

theorem cell23_4610429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 3, 1, 3, 4].length) (baseStart_4610429 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4610429 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4610429 prefixEnd_4610429 := by exact prefixLift 4610429
  have htrace : WordTrace (prefixWord ++ tailWord_4610429) baseStart_4610429 baseEnd_4610429 := by
    simpa [prefixWord, tailWord_4610429, baseEnd_4610429] using wordTrace_append hprefix tailTrace_4610429
  have hstable : (prefixWord ++ tailWord_4610429).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4610429).length < 2 ^ (prefixWord ++ tailWord_4610429).sum := by decide
  have hdescent : baseEnd_4610429 < baseStart_4610429 := by decide
  rcases family_descends (prefixWord ++ tailWord_4610429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4610456 : List Nat := [2, 1, 2, 5, 1, 2, 2, 1, 2, 2, 3]
def baseStart_4610456 : Nat := 118140960795 + 4610456 * 2 ^ 59
def prefixEnd_4610456 : Nat := 4983230072969 + 3 ^ 40 * 4610456 * 2
def baseEnd_4610456 : Nat := 2367379964405518803396905

theorem tailTrace_4610456 : CollatzResearch.WordTrace tailWord_4610456 prefixEnd_4610456 2367379964405518803396905 := by
  unfold tailWord_4610456
  simp only [CollatzResearch.WordTrace]
  refine ⟨84078572492556395020769611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 112104763323408526694359481 84078572492556395020769611)
  ·
    refine ⟨126117858738834592531154417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84078572492556395020769611 126117858738834592531154417)
    ·
      refine ⟨94588394054125944398365813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 126117858738834592531154417 94588394054125944398365813)
      ·
        refine ⟨8867661942574307287346795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 94588394054125944398365813 8867661942574307287346795)
        ·
          refine ⟨13301492913861460931020193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8867661942574307287346795 13301492913861460931020193)
          ·
            refine ⟨9976119685396095698265145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13301492913861460931020193 9976119685396095698265145)
            ·
              refine ⟨7482089764047071773698859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9976119685396095698265145 7482089764047071773698859)
              ·
                refine ⟨11223134646070607660548289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7482089764047071773698859 11223134646070607660548289)
                ·
                  refine ⟨8417350984552955745411217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11223134646070607660548289 8417350984552955745411217)
                  ·
                    refine ⟨6313013238414716809058413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8417350984552955745411217 6313013238414716809058413)
                    ·
                      refine ⟨2367379964405518803396905, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6313013238414716809058413 2367379964405518803396905)
                      ·
                        rfl

theorem cell23_4610456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 2, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 2, 2, 1, 2, 2, 3].length) (baseStart_4610456 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4610456 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4610456 prefixEnd_4610456 := by exact prefixLift 4610456
  have htrace : WordTrace (prefixWord ++ tailWord_4610456) baseStart_4610456 baseEnd_4610456 := by
    simpa [prefixWord, tailWord_4610456, baseEnd_4610456] using wordTrace_append hprefix tailTrace_4610456
  have hstable : (prefixWord ++ tailWord_4610456).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4610456).length < 2 ^ (prefixWord ++ tailWord_4610456).sum := by decide
  have hdescent : baseEnd_4610456 < baseStart_4610456 := by decide
  rcases family_descends (prefixWord ++ tailWord_4610456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4610536 : List Nat := [2, 1, 4, 1, 1, 3, 3, 2, 2, 4]
def baseStart_4610536 : Nat := 118140960795 + 4610536 * 2 ^ 59
def prefixEnd_4610536 : Nat := 4983230072969 + 3 ^ 40 * 4610536 * 2
def baseEnd_4610536 : Nat := 789140347619292830132179

theorem tailTrace_4610536 : CollatzResearch.WordTrace tailWord_4610536 prefixEnd_4610536 789140347619292830132179 := by
  unfold tailWord_4610536
  simp only [CollatzResearch.WordTrace]
  refine ⟨84080031412411481852225731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 112106708549881975802967641 84080031412411481852225731)
  ·
    refine ⟨126120047118617222778338597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84080031412411481852225731 126120047118617222778338597)
    ·
      refine ⟨23647508834740729270938487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 126120047118617222778338597 23647508834740729270938487)
      ·
        refine ⟨35471263252111093906407731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23647508834740729270938487 35471263252111093906407731)
        ·
          refine ⟨53206894878166640859611597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35471263252111093906407731 53206894878166640859611597)
          ·
            refine ⟨19952585579312490322354349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 53206894878166640859611597 19952585579312490322354349)
            ·
              refine ⟨7482219592242183870882881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19952585579312490322354349 7482219592242183870882881)
              ·
                refine ⟨5611664694181637903162161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7482219592242183870882881 5611664694181637903162161)
                ·
                  refine ⟨4208748520636228427371621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5611664694181637903162161 4208748520636228427371621)
                  ·
                    refine ⟨789140347619292830132179, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4208748520636228427371621 789140347619292830132179)
                    ·
                      rfl

theorem cell23_4610536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 3, 2, 2, 4].length) (baseStart_4610536 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4610536 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4610536 prefixEnd_4610536 := by exact prefixLift 4610536
  have htrace : WordTrace (prefixWord ++ tailWord_4610536) baseStart_4610536 baseEnd_4610536 := by
    simpa [prefixWord, tailWord_4610536, baseEnd_4610536] using wordTrace_append hprefix tailTrace_4610536
  have hstable : (prefixWord ++ tailWord_4610536).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4610536).length < 2 ^ (prefixWord ++ tailWord_4610536).sum := by decide
  have hdescent : baseEnd_4610536 < baseStart_4610536 := by decide
  rcases family_descends (prefixWord ++ tailWord_4610536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4610546 : List Nat := [3, 2, 1, 4, 2, 1, 1, 2, 1, 1, 5]
def baseStart_4610546 : Nat := 118140960795 + 4610546 * 2 ^ 59
def prefixEnd_4610546 : Nat := 4983230072969 + 3 ^ 40 * 4610546 * 2
def baseEnd_4610546 : Nat := 2367426177664423451271491

theorem tailTrace_4610546 : CollatzResearch.WordTrace tailWord_4610546 prefixEnd_4610546 2367426177664423451271491 := by
  unfold tailWord_4610546
  simp only [CollatzResearch.WordTrace]
  refine ⟨42040106888696683853078873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 112106951703191156941543661 42040106888696683853078873)
  ·
    refine ⟨31530080166522512889809155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42040106888696683853078873 31530080166522512889809155)
    ·
      refine ⟨47295120249783769334713733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31530080166522512889809155 47295120249783769334713733)
      ·
        refine ⟨8867835046834456750258825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 47295120249783769334713733 8867835046834456750258825)
        ·
          refine ⟨6650876285125842562694119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8867835046834456750258825 6650876285125842562694119)
          ·
            refine ⟨9976314427688763844041179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6650876285125842562694119 9976314427688763844041179)
            ·
              refine ⟨14964471641533145766061769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9976314427688763844041179 14964471641533145766061769)
              ·
                refine ⟨11223353731149859324546327, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14964471641533145766061769 11223353731149859324546327)
                ·
                  refine ⟨16835030596724788986819491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11223353731149859324546327 16835030596724788986819491)
                  ·
                    refine ⟨25252545895087183480229237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16835030596724788986819491 25252545895087183480229237)
                    ·
                      refine ⟨2367426177664423451271491, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25252545895087183480229237 2367426177664423451271491)
                      ·
                        rfl

theorem cell23_4610546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 2, 1, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 2, 1, 1, 2, 1, 1, 5].length) (baseStart_4610546 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4610546 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4610546 prefixEnd_4610546 := by exact prefixLift 4610546
  have htrace : WordTrace (prefixWord ++ tailWord_4610546) baseStart_4610546 baseEnd_4610546 := by
    simpa [prefixWord, tailWord_4610546, baseEnd_4610546] using wordTrace_append hprefix tailTrace_4610546
  have hstable : (prefixWord ++ tailWord_4610546).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4610546).length < 2 ^ (prefixWord ++ tailWord_4610546).sum := by decide
  have hdescent : baseEnd_4610546 < baseStart_4610546 := by decide
  rcases family_descends (prefixWord ++ tailWord_4610546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4610616 : List Nat := [2, 1, 2, 1, 4, 1, 2, 3, 1, 4, 2]
def baseStart_4610616 : Nat := 118140960795 + 4610616 * 2 ^ 59
def prefixEnd_4610616 : Nat := 4983230072969 + 3 ^ 40 * 4610616 * 2
def baseEnd_4610616 : Nat := 2367462121310238177396169

theorem tailTrace_4610616 : CollatzResearch.WordTrace tailWord_4610616 prefixEnd_4610616 2367462121310238177396169 := by
  unfold tailWord_4610616
  simp only [CollatzResearch.WordTrace]
  refine ⟨84081490332266568683681851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 112108653776355424911575801 84081490332266568683681851)
  ·
    refine ⟨126122235498399853025522777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84081490332266568683681851 126122235498399853025522777)
    ·
      refine ⟨94591676623799889769142083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 126122235498399853025522777 94591676623799889769142083)
      ·
        refine ⟨141887514935699834653713125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 94591676623799889769142083 141887514935699834653713125)
        ·
          refine ⟨26603909050443718997571211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 141887514935699834653713125 26603909050443718997571211)
          ·
            refine ⟨39905863575665578496356817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26603909050443718997571211 39905863575665578496356817)
            ·
              refine ⟨29929397681749183872267613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 39905863575665578496356817 29929397681749183872267613)
              ·
                refine ⟨11223524130655943952100355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 29929397681749183872267613 11223524130655943952100355)
                ·
                  refine ⟨16835286195983915928150533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11223524130655943952100355 16835286195983915928150533)
                  ·
                    refine ⟨3156616161746984236528225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16835286195983915928150533 3156616161746984236528225)
                    ·
                      refine ⟨2367462121310238177396169, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3156616161746984236528225 2367462121310238177396169)
                      ·
                        rfl

theorem cell23_4610616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 2, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 2, 3, 1, 4, 2].length) (baseStart_4610616 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4610616 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4610616 prefixEnd_4610616 := by exact prefixLift 4610616
  have htrace : WordTrace (prefixWord ++ tailWord_4610616) baseStart_4610616 baseEnd_4610616 := by
    simpa [prefixWord, tailWord_4610616, baseEnd_4610616] using wordTrace_append hprefix tailTrace_4610616
  have hstable : (prefixWord ++ tailWord_4610616).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4610616).length < 2 ^ (prefixWord ++ tailWord_4610616).sum := by decide
  have hdescent : baseEnd_4610616 < baseStart_4610616 := by decide
  rcases family_descends (prefixWord ++ tailWord_4610616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4610620 : List Nat := [2, 2, 2, 2, 3, 3, 1, 2, 1, 3, 2]
def baseStart_4610620 : Nat := 118140960795 + 4610620 * 2 ^ 59
def prefixEnd_4610620 : Nat := 4983230072969 + 3 ^ 40 * 4610620 * 2
def baseEnd_4610620 : Nat := 2367464175232856161746151

theorem tailTrace_4610620 : CollatzResearch.WordTrace tailWord_4610620 prefixEnd_4610620 2367464175232856161746151 := by
  unfold tailWord_4610620
  simp only [CollatzResearch.WordTrace]
  refine ⟨84081563278259323025254657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 112108751037679097367006209 84081563278259323025254657)
  ·
    refine ⟨63061172458694492268940993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 84081563278259323025254657 63061172458694492268940993)
    ·
      refine ⟨47295879344020869201705745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 63061172458694492268940993 47295879344020869201705745)
      ·
        refine ⟨35471909508015651901279309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47295879344020869201705745 35471909508015651901279309)
        ·
          refine ⟨13301966065505869462979741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 35471909508015651901279309 13301966065505869462979741)
          ·
            refine ⟨4988237274564701048617403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13301966065505869462979741 4988237274564701048617403)
            ·
              refine ⟨7482355911847051572926105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4988237274564701048617403 7482355911847051572926105)
              ·
                refine ⟨5611766933885288679694579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7482355911847051572926105 5611766933885288679694579)
                ·
                  refine ⟨8417650400827933019541869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5611766933885288679694579 8417650400827933019541869)
                  ·
                    refine ⟨3156618900310474882328201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8417650400827933019541869 3156618900310474882328201)
                    ·
                      refine ⟨2367464175232856161746151, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3156618900310474882328201 2367464175232856161746151)
                      ·
                        rfl

theorem cell23_4610620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 3, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 3, 1, 2, 1, 3, 2].length) (baseStart_4610620 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4610620 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4610620 prefixEnd_4610620 := by exact prefixLift 4610620
  have htrace : WordTrace (prefixWord ++ tailWord_4610620) baseStart_4610620 baseEnd_4610620 := by
    simpa [prefixWord, tailWord_4610620, baseEnd_4610620] using wordTrace_append hprefix tailTrace_4610620
  have hstable : (prefixWord ++ tailWord_4610620).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4610620).length < 2 ^ (prefixWord ++ tailWord_4610620).sum := by decide
  have hdescent : baseEnd_4610620 < baseStart_4610620 := by decide
  rcases family_descends (prefixWord ++ tailWord_4610620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4610637 : List Nat := [1, 6, 1, 1, 2, 2, 3, 1, 1, 3, 2]
def baseStart_4610637 : Nat := 118140960795 + 4610637 * 2 ^ 59
def prefixEnd_4610637 : Nat := 4983230072969 + 3 ^ 40 * 4610637 * 2
def baseEnd_4610637 : Nat := 2367472904403982595233573

theorem tailTrace_4610637 : CollatzResearch.WordTrace tailWord_4610637 prefixEnd_4610637 2367472904403982595233573 := by
  unfold tailWord_4610637
  simp only [CollatzResearch.WordTrace]
  refine ⟨168163746597457057953878165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112109164398304705302585443 168163746597457057953878165)
  ·
    refine ⟨7882675621755799591588039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 168163746597457057953878165 7882675621755799591588039)
    ·
      refine ⟨11824013432633699387382059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7882675621755799591588039 11824013432633699387382059)
      ·
        refine ⟨17736020148950549081073089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11824013432633699387382059 17736020148950549081073089)
        ·
          refine ⟨13302015111712911810804817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17736020148950549081073089 13302015111712911810804817)
          ·
            refine ⟨9976511333784683858103613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13302015111712911810804817 9976511333784683858103613)
            ·
              refine ⟨3741191750169256446788855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9976511333784683858103613 3741191750169256446788855)
              ·
                refine ⟨5611787625253884670183283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3741191750169256446788855 5611787625253884670183283)
                ·
                  refine ⟨8417681437880827005274925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5611787625253884670183283 8417681437880827005274925)
                  ·
                    refine ⟨3156630539205310126978097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8417681437880827005274925 3156630539205310126978097)
                    ·
                      refine ⟨2367472904403982595233573, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3156630539205310126978097 2367472904403982595233573)
                      ·
                        rfl

theorem cell23_4610637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 2, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 2, 3, 1, 1, 3, 2].length) (baseStart_4610637 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4610637 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4610637 prefixEnd_4610637 := by exact prefixLift 4610637
  have htrace : WordTrace (prefixWord ++ tailWord_4610637) baseStart_4610637 baseEnd_4610637 := by
    simpa [prefixWord, tailWord_4610637, baseEnd_4610637] using wordTrace_append hprefix tailTrace_4610637
  have hstable : (prefixWord ++ tailWord_4610637).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4610637).length < 2 ^ (prefixWord ++ tailWord_4610637).sum := by decide
  have hdescent : baseEnd_4610637 < baseStart_4610637 := by decide
  rcases family_descends (prefixWord ++ tailWord_4610637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4610666 : List Nat := [3, 1, 3, 2, 1, 1, 3, 1, 2, 3, 3]
def baseStart_4610666 : Nat := 118140960795 + 4610666 * 2 ^ 59
def prefixEnd_4610666 : Nat := 4983230072969 + 3 ^ 40 * 4610666 * 2
def baseEnd_4610666 : Nat := 2367487795342962981770939

theorem tailTrace_4610666 : CollatzResearch.WordTrace tailWord_4610666 prefixEnd_4610666 2367487795342962981770939 := by
  unfold tailWord_4610666
  simp only [CollatzResearch.WordTrace]
  refine ⟨42041201078587998976670963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 112109869542901330604455901 42041201078587998976670963)
  ·
    refine ⟨63061801617881998465006445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42041201078587998976670963 63061801617881998465006445)
    ·
      refine ⟨23648175606705749424377417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 63061801617881998465006445 23648175606705749424377417)
      ·
        refine ⟨17736131705029312068283063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23648175606705749424377417 17736131705029312068283063)
        ·
          refine ⟨26604197557543968102424595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17736131705029312068283063 26604197557543968102424595)
          ·
            refine ⟨39906296336315952153636893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26604197557543968102424595 39906296336315952153636893)
            ·
              refine ⟨14964861126118482057613835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 39906296336315952153636893 14964861126118482057613835)
              ·
                refine ⟨22447291689177723086420753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14964861126118482057613835 22447291689177723086420753)
                ·
                  refine ⟨16835468766883292314815565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22447291689177723086420753 16835468766883292314815565)
                  ·
                    refine ⟨6313300787581234618055837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16835468766883292314815565 6313300787581234618055837)
                    ·
                      refine ⟨2367487795342962981770939, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6313300787581234618055837 2367487795342962981770939)
                      ·
                        rfl

theorem cell23_4610666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 3, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 3, 1, 2, 3, 3].length) (baseStart_4610666 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4610666 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4610666 prefixEnd_4610666 := by exact prefixLift 4610666
  have htrace : WordTrace (prefixWord ++ tailWord_4610666) baseStart_4610666 baseEnd_4610666 := by
    simpa [prefixWord, tailWord_4610666, baseEnd_4610666] using wordTrace_append hprefix tailTrace_4610666
  have hstable : (prefixWord ++ tailWord_4610666).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4610666).length < 2 ^ (prefixWord ++ tailWord_4610666).sum := by decide
  have hdescent : baseEnd_4610666 < baseStart_4610666 := by decide
  rcases family_descends (prefixWord ++ tailWord_4610666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4610733 : List Nat := [1, 5, 2, 1, 1, 2, 2, 2, 3, 4]
def baseStart_4610733 : Nat := 118140960795 + 4610733 * 2 ^ 59
def prefixEnd_4610733 : Nat := 4983230072969 + 3 ^ 40 * 4610733 * 2
def baseEnd_4610733 : Nat := 789174066182271406544377

theorem tailTrace_4610733 : CollatzResearch.WordTrace tailWord_4610733 prefixEnd_4610733 789174066182271406544377 := by
  unfold tailWord_4610733
  simp only [CollatzResearch.WordTrace]
  refine ⟨168167248005109266349372853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112111498670072844232915235 168167248005109266349372853)
  ·
    refine ⟨15765679500478993720253705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 168167248005109266349372853 15765679500478993720253705)
    ·
      refine ⟨11824259625359245290190279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15765679500478993720253705 11824259625359245290190279)
      ·
        refine ⟨17736389438038867935285419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11824259625359245290190279 17736389438038867935285419)
        ·
          refine ⟨26604584157058301902928129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17736389438038867935285419 26604584157058301902928129)
          ·
            refine ⟨19953438117793726427196097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26604584157058301902928129 19953438117793726427196097)
            ·
              refine ⟨14965078588345294820397073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19953438117793726427196097 14965078588345294820397073)
              ·
                refine ⟨11223808941258971115297805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14965078588345294820397073 11223808941258971115297805)
                ·
                  refine ⟨4208928352972114168236677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11223808941258971115297805 4208928352972114168236677)
                  ·
                    refine ⟨789174066182271406544377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4208928352972114168236677 789174066182271406544377)
                    ·
                      rfl

theorem cell23_4610733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 2, 2, 3, 4].length) (baseStart_4610733 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4610733 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4610733 prefixEnd_4610733 := by exact prefixLift 4610733
  have htrace : WordTrace (prefixWord ++ tailWord_4610733) baseStart_4610733 baseEnd_4610733 := by
    simpa [prefixWord, tailWord_4610733, baseEnd_4610733] using wordTrace_append hprefix tailTrace_4610733
  have hstable : (prefixWord ++ tailWord_4610733).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4610733).length < 2 ^ (prefixWord ++ tailWord_4610733).sum := by decide
  have hdescent : baseEnd_4610733 < baseStart_4610733 := by decide
  rcases family_descends (prefixWord ++ tailWord_4610733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4610780 : List Nat := [2, 2, 5, 1, 1, 1, 4, 1, 6]
def baseStart_4610780 : Nat := 118140960795 + 4610780 * 2 ^ 59
def prefixEnd_4610780 : Nat := 4983230072969 + 3 ^ 40 * 4610780 * 2
def baseEnd_4610780 : Nat := 263060703570841726193935

theorem tailTrace_4610780 : CollatzResearch.WordTrace tailWord_4610780 prefixEnd_4610780 263060703570841726193935 := by
  unfold tailWord_4610780
  simp only [CollatzResearch.WordTrace]
  refine ⟨84084481117969496688166897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 112112641490625995584222529 84084481117969496688166897)
  ·
    refine ⟨63063360838477122516125173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 84084481117969496688166897 63063360838477122516125173)
    ·
      refine ⟨5912190078607230235886735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 63063360838477122516125173 5912190078607230235886735)
      ·
        refine ⟨8868285117910845353830103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5912190078607230235886735 8868285117910845353830103)
        ·
          refine ⟨13302427676866268030745155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8868285117910845353830103 13302427676866268030745155)
          ·
            refine ⟨19953641515299402046117733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13302427676866268030745155 19953641515299402046117733)
            ·
              refine ⟨3741307784118637883647075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 19953641515299402046117733 3741307784118637883647075)
              ·
                refine ⟨5611961676177956825470613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3741307784118637883647075 5611961676177956825470613)
                ·
                  refine ⟨263060703570841726193935, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5611961676177956825470613 263060703570841726193935)
                  ·
                    rfl

theorem cell23_4610780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 4, 1, 6].length) (baseStart_4610780 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4610780 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4610780 prefixEnd_4610780 := by exact prefixLift 4610780
  have htrace : WordTrace (prefixWord ++ tailWord_4610780) baseStart_4610780 baseEnd_4610780 := by
    simpa [prefixWord, tailWord_4610780, baseEnd_4610780] using wordTrace_append hprefix tailTrace_4610780
  have hstable : (prefixWord ++ tailWord_4610780).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4610780).length < 2 ^ (prefixWord ++ tailWord_4610780).sum := by decide
  have hdescent : baseEnd_4610780 < baseStart_4610780 := by decide
  rcases family_descends (prefixWord ++ tailWord_4610780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4610816 : List Nat := [2, 1, 1, 2, 1, 1, 2, 1, 7, 2, 3]
def baseStart_4610816 : Nat := 118140960795 + 4610816 * 2 ^ 59
def prefixEnd_4610816 : Nat := 4983230072969 + 3 ^ 40 * 4610816 * 2
def baseEnd_4610816 : Nat := 2367564817441137394895249

theorem tailTrace_4610816 : CollatzResearch.WordTrace tailWord_4610816 prefixEnd_4610816 2367564817441137394895249 := by
  unfold tailWord_4610816
  simp only [CollatzResearch.WordTrace]
  refine ⟨84085137631904285762322151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 112113516842539047683096201 84085137631904285762322151)
  ·
    refine ⟨126127706447856428643483227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84085137631904285762322151 126127706447856428643483227)
    ·
      refine ⟨189191559671784642965224841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 126127706447856428643483227 189191559671784642965224841)
      ·
        refine ⟨141893669753838482223918631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 189191559671784642965224841 141893669753838482223918631)
        ·
          refine ⟨212840504630757723335877947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 141893669753838482223918631 212840504630757723335877947)
          ·
            refine ⟨319260756946136585003816921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 212840504630757723335877947 319260756946136585003816921)
            ·
              refine ⟨239445567709602438752862691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 319260756946136585003816921 239445567709602438752862691)
              ·
                refine ⟨359168351564403658129294037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 239445567709602438752862691 359168351564403658129294037)
                ·
                  refine ⟨8418008239790710737405329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 359168351564403658129294037 8418008239790710737405329)
                  ·
                    refine ⟨6313506179843033053053997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8418008239790710737405329 6313506179843033053053997)
                    ·
                      refine ⟨2367564817441137394895249, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6313506179843033053053997 2367564817441137394895249)
                      ·
                        rfl

theorem cell23_4610816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 1, 7, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 1, 7, 2, 3].length) (baseStart_4610816 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4610816 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4610816 prefixEnd_4610816 := by exact prefixLift 4610816
  have htrace : WordTrace (prefixWord ++ tailWord_4610816) baseStart_4610816 baseEnd_4610816 := by
    simpa [prefixWord, tailWord_4610816, baseEnd_4610816] using wordTrace_append hprefix tailTrace_4610816
  have hstable : (prefixWord ++ tailWord_4610816).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4610816).length < 2 ^ (prefixWord ++ tailWord_4610816).sum := by decide
  have hdescent : baseEnd_4610816 < baseStart_4610816 := by decide
  rcases family_descends (prefixWord ++ tailWord_4610816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4610824 : List Nat := [2, 1, 3, 2, 2, 4, 2, 2, 1, 1, 3]
def baseStart_4610824 : Nat := 118140960795 + 4610824 * 2 ^ 59
def prefixEnd_4610824 : Nat := 4983230072969 + 3 ^ 40 * 4610824 * 2
def baseEnd_4610824 : Nat := 2367568925286373363595213

theorem tailTrace_4610824 : CollatzResearch.WordTrace tailWord_4610824 prefixEnd_4610824 2367568925286373363595213 := by
  unfold tailWord_4610824
  simp only [CollatzResearch.WordTrace]
  refine ⟨84085283523889794445467763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 112113711365186392593957017 84085283523889794445467763)
  ·
    refine ⟨126127925285834691668201645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84085283523889794445467763 126127925285834691668201645)
    ·
      refine ⟨47297971982188009375575617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 126127925285834691668201645 47297971982188009375575617)
      ·
        refine ⟨35473478986641007031681713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47297971982188009375575617 35473478986641007031681713)
        ·
          refine ⟨26605109239980755273761285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35473478986641007031681713 26605109239980755273761285)
          ·
            refine ⟨4988457982496391613830241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 26605109239980755273761285 4988457982496391613830241)
            ·
              refine ⟨3741343486872293710372681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4988457982496391613830241 3741343486872293710372681)
              ·
                refine ⟨2806007615154220282779511, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3741343486872293710372681 2806007615154220282779511)
                ·
                  refine ⟨4209011422731330424169267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2806007615154220282779511 4209011422731330424169267)
                  ·
                    refine ⟨6313517134096995636253901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4209011422731330424169267 6313517134096995636253901)
                    ·
                      refine ⟨2367568925286373363595213, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6313517134096995636253901 2367568925286373363595213)
                      ·
                        rfl

theorem cell23_4610824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 4, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 4, 2, 2, 1, 1, 3].length) (baseStart_4610824 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4610824 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4610824 prefixEnd_4610824 := by exact prefixLift 4610824
  have htrace : WordTrace (prefixWord ++ tailWord_4610824) baseStart_4610824 baseEnd_4610824 := by
    simpa [prefixWord, tailWord_4610824, baseEnd_4610824] using wordTrace_append hprefix tailTrace_4610824
  have hstable : (prefixWord ++ tailWord_4610824).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4610824).length < 2 ^ (prefixWord ++ tailWord_4610824).sum := by decide
  have hdescent : baseEnd_4610824 < baseStart_4610824 := by decide
  rcases family_descends (prefixWord ++ tailWord_4610824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4610826 : List Nat := [3, 1, 2, 2, 1, 2, 1, 2, 3, 2, 4]
def baseStart_4610826 : Nat := 118140960795 + 4610826 * 2 ^ 59
def prefixEnd_4610826 : Nat := 4983230072969 + 3 ^ 40 * 4610826 * 2
def baseEnd_4610826 : Nat := 2367569952247682355770203

theorem tailTrace_4610826 : CollatzResearch.WordTrace tailWord_4610826 prefixEnd_4610826 2367569952247682355770203 := by
  unfold tailWord_4610826
  simp only [CollatzResearch.WordTrace]
  refine ⟨42042659998443085808127083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 112113759995848228821672221 42042659998443085808127083)
  ·
    refine ⟨63063989997664628712190625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42042659998443085808127083 63063989997664628712190625)
    ·
      refine ⟨47297992498248471534142969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 63063989997664628712190625 47297992498248471534142969)
      ·
        refine ⟨35473494373686353650607227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47297992498248471534142969 35473494373686353650607227)
        ·
          refine ⟨53210241560529530475910841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35473494373686353650607227 53210241560529530475910841)
          ·
            refine ⟨39907681170397147856933131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 53210241560529530475910841 39907681170397147856933131)
            ·
              refine ⟨59861521755595721785399697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39907681170397147856933131 59861521755595721785399697)
              ·
                refine ⟨44896141316696791339049773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 59861521755595721785399697 44896141316696791339049773)
                ·
                  refine ⟨16836052993761296752143665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 44896141316696791339049773 16836052993761296752143665)
                  ·
                    refine ⟨12627039745320972564107749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16836052993761296752143665 12627039745320972564107749)
                    ·
                      refine ⟨2367569952247682355770203, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12627039745320972564107749 2367569952247682355770203)
                      ·
                        rfl

theorem cell23_4610826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 1, 2, 3, 2, 4].length) (baseStart_4610826 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4610826 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4610826 prefixEnd_4610826 := by exact prefixLift 4610826
  have htrace : WordTrace (prefixWord ++ tailWord_4610826) baseStart_4610826 baseEnd_4610826 := by
    simpa [prefixWord, tailWord_4610826, baseEnd_4610826] using wordTrace_append hprefix tailTrace_4610826
  have hstable : (prefixWord ++ tailWord_4610826).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4610826).length < 2 ^ (prefixWord ++ tailWord_4610826).sum := by decide
  have hdescent : baseEnd_4610826 < baseStart_4610826 := by decide
  rcases family_descends (prefixWord ++ tailWord_4610826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4610830 : List Nat := [4, 1, 1, 2, 1, 1, 1, 5, 3, 2, 2]
def baseStart_4610830 : Nat := 118140960795 + 4610830 * 2 ^ 59
def prefixEnd_4610830 : Nat := 4983230072969 + 3 ^ 40 * 4610830 * 2
def baseEnd_4610830 : Nat := 2367572006170300340120185

theorem tailTrace_4610830 : CollatzResearch.WordTrace tailWord_4610830 prefixEnd_4610830 2367572006170300340120185 := by
  unfold tailWord_4610830
  simp only [CollatzResearch.WordTrace]
  refine ⟨21021348235719731489456743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 112113857257171901277102629 21021348235719731489456743)
  ·
    refine ⟨31532022353579597234185115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21021348235719731489456743 31532022353579597234185115)
    ·
      refine ⟨47298033530369395851277673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31532022353579597234185115 47298033530369395851277673)
      ·
        refine ⟨35473525147777046888458255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47298033530369395851277673 35473525147777046888458255)
        ·
          refine ⟨53210287721665570332687383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35473525147777046888458255 53210287721665570332687383)
          ·
            refine ⟨79815431582498355499031075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53210287721665570332687383 79815431582498355499031075)
            ·
              refine ⟨119723147373747533248546613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 79815431582498355499031075 119723147373747533248546613)
              ·
                refine ⟨11224045066288831242051245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 119723147373747533248546613 11224045066288831242051245)
                ·
                  refine ⟨4209016899858311715769217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11224045066288831242051245 4209016899858311715769217)
                  ·
                    refine ⟨3156762674893733786826913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4209016899858311715769217 3156762674893733786826913)
                    ·
                      refine ⟨2367572006170300340120185, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3156762674893733786826913 2367572006170300340120185)
                      ·
                        rfl

theorem cell23_4610830_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 1, 5, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 1, 5, 3, 2, 2].length) (baseStart_4610830 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4610830 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4610830 prefixEnd_4610830 := by exact prefixLift 4610830
  have htrace : WordTrace (prefixWord ++ tailWord_4610830) baseStart_4610830 baseEnd_4610830 := by
    simpa [prefixWord, tailWord_4610830, baseEnd_4610830] using wordTrace_append hprefix tailTrace_4610830
  have hstable : (prefixWord ++ tailWord_4610830).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4610830).length < 2 ^ (prefixWord ++ tailWord_4610830).sum := by decide
  have hdescent : baseEnd_4610830 < baseStart_4610830 := by decide
  rcases family_descends (prefixWord ++ tailWord_4610830) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4610861 : List Nat := [1, 5, 3, 2, 2, 1, 2, 1, 1, 5]
def baseStart_4610861 : Nat := 118140960795 + 4610861 * 2 ^ 59
def prefixEnd_4610861 : Nat := 4983230072969 + 3 ^ 40 * 4610861 * 2
def baseEnd_4610861 : Nat := 789195974690196572944181

theorem tailTrace_4610861 : CollatzResearch.WordTrace tailWord_4610861 prefixEnd_4610861 789195974690196572944181 := by
  unfold tailWord_4610861
  simp only [CollatzResearch.WordTrace]
  refine ⟨168171916548645544210032437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112114611032430362806688291 168171916548645544210032437)
  ·
    refine ⟨15766117176435519769690541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 168171916548645544210032437 15766117176435519769690541)
    ·
      refine ⟨5912293941163319913633953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15766117176435519769690541 5912293941163319913633953)
      ·
        refine ⟨4434220455872489935225465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5912293941163319913633953 4434220455872489935225465)
        ·
          refine ⟨3325665341904367451419099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4434220455872489935225465 3325665341904367451419099)
          ·
            refine ⟨4988498012856551177128649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3325665341904367451419099 4988498012856551177128649)
            ·
              refine ⟨3741373509642413382846487, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4988498012856551177128649 3741373509642413382846487)
              ·
                refine ⟨5612060264463620074269731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3741373509642413382846487 5612060264463620074269731)
                ·
                  refine ⟨8418090396695430111404597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5612060264463620074269731 8418090396695430111404597)
                  ·
                    refine ⟨789195974690196572944181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8418090396695430111404597 789195974690196572944181)
                    ·
                      rfl

theorem cell23_4610861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 2, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 2, 1, 2, 1, 1, 5].length) (baseStart_4610861 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4610861 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4610861 prefixEnd_4610861 := by exact prefixLift 4610861
  have htrace : WordTrace (prefixWord ++ tailWord_4610861) baseStart_4610861 baseEnd_4610861 := by
    simpa [prefixWord, tailWord_4610861, baseEnd_4610861] using wordTrace_append hprefix tailTrace_4610861
  have hstable : (prefixWord ++ tailWord_4610861).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4610861).length < 2 ^ (prefixWord ++ tailWord_4610861).sum := by decide
  have hdescent : baseEnd_4610861 < baseStart_4610861 := by decide
  rcases family_descends (prefixWord ++ tailWord_4610861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4610867 : List Nat := [1, 1, 1, 2, 6, 3, 2, 1, 1, 2, 3]
def baseStart_4610867 : Nat := 118140960795 + 4610867 * 2 ^ 59
def prefixEnd_4610867 : Nat := 4983230072969 + 3 ^ 40 * 4610867 * 2
def baseEnd_4610867 : Nat := 2367591004954516695357515

theorem tailTrace_4610867 : CollatzResearch.WordTrace tailWord_4610867 prefixEnd_4610867 2367591004954516695357515 := by
  unfold tailWord_4610867
  simp only [CollatzResearch.WordTrace]
  refine ⟨168172135386623807234750855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112114756924415871489833903 168172135386623807234750855)
  ·
    refine ⟨252258203079935710852126283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 168172135386623807234750855 252258203079935710852126283)
    ·
      refine ⟨378387304619903566278189425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 252258203079935710852126283 378387304619903566278189425)
      ·
        refine ⟨283790478464927674708642069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 378387304619903566278189425 283790478464927674708642069)
        ·
          refine ⟨13302678678043484751967597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 283790478464927674708642069 13302678678043484751967597)
          ·
            refine ⟨4988504504266306781987849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13302678678043484751967597 4988504504266306781987849)
            ·
              refine ⟨3741378378199730086490887, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4988504504266306781987849 3741378378199730086490887)
              ·
                refine ⟨5612067567299595129736331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3741378378199730086490887 5612067567299595129736331)
                ·
                  refine ⟨8418101350949392694604497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5612067567299595129736331 8418101350949392694604497)
                  ·
                    refine ⟨6313576013212044520953373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8418101350949392694604497 6313576013212044520953373)
                    ·
                      refine ⟨2367591004954516695357515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6313576013212044520953373 2367591004954516695357515)
                      ·
                        rfl

theorem cell23_4610867_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 3, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 3, 2, 1, 1, 2, 3].length) (baseStart_4610867 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4610867 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4610867 prefixEnd_4610867 := by exact prefixLift 4610867
  have htrace : WordTrace (prefixWord ++ tailWord_4610867) baseStart_4610867 baseEnd_4610867 := by
    simpa [prefixWord, tailWord_4610867, baseEnd_4610867] using wordTrace_append hprefix tailTrace_4610867
  have hstable : (prefixWord ++ tailWord_4610867).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4610867).length < 2 ^ (prefixWord ++ tailWord_4610867).sum := by decide
  have hdescent : baseEnd_4610867 < baseStart_4610867 := by decide
  rcases family_descends (prefixWord ++ tailWord_4610867) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4610896 : List Nat := [2, 1, 1, 1, 1, 4, 4, 1, 2, 6]
def baseStart_4610896 : Nat := 118140960795 + 4610896 * 2 ^ 59
def prefixEnd_4610896 : Nat := 4983230072969 + 3 ^ 40 * 4610896 * 2
def baseEnd_4610896 : Nat := 789201965297832360631627

theorem tailTrace_4610896 : CollatzResearch.WordTrace tailWord_4610896 prefixEnd_4610896 789201965297832360631627 := by
  unfold tailWord_4610896
  simp only [CollatzResearch.WordTrace]
  refine ⟨84086596551759372593778271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 112115462069012496791704361 84086596551759372593778271)
  ·
    refine ⟨126129894827639058890667407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84086596551759372593778271 126129894827639058890667407)
    ·
      refine ⟨189194842241458588336001111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 126129894827639058890667407 189194842241458588336001111)
      ·
        refine ⟨283792263362187882504001667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 189194842241458588336001111 283792263362187882504001667)
        ·
          refine ⟨425688395043281823756002501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 283792263362187882504001667 425688395043281823756002501)
          ·
            refine ⟨79816574070615341954250469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 425688395043281823756002501 79816574070615341954250469)
            ·
              refine ⟨14965607638240376616421963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 79816574070615341954250469 14965607638240376616421963)
              ·
                refine ⟨22448411457360564924632945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14965607638240376616421963 22448411457360564924632945)
                ·
                  refine ⟨16836308593020423693474709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22448411457360564924632945 16836308593020423693474709)
                  ·
                    refine ⟨789201965297832360631627, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16836308593020423693474709 789201965297832360631627)
                    ·
                      rfl

theorem cell23_4610896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 4, 1, 2, 6].length) (baseStart_4610896 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4610896 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4610896 prefixEnd_4610896 := by exact prefixLift 4610896
  have htrace : WordTrace (prefixWord ++ tailWord_4610896) baseStart_4610896 baseEnd_4610896 := by
    simpa [prefixWord, tailWord_4610896, baseEnd_4610896] using wordTrace_append hprefix tailTrace_4610896
  have hstable : (prefixWord ++ tailWord_4610896).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4610896).length < 2 ^ (prefixWord ++ tailWord_4610896).sum := by decide
  have hdescent : baseEnd_4610896 < baseStart_4610896 := by decide
  rcases family_descends (prefixWord ++ tailWord_4610896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4610897 : List Nat := [1, 2, 2, 1, 7, 1, 1, 1, 1, 3, 3]
def baseStart_4610897 : Nat := 118140960795 + 4610897 * 2 ^ 59
def prefixEnd_4610897 : Nat := 4983230072969 + 3 ^ 40 * 4610897 * 2
def baseEnd_4610897 : Nat := 2367606409374151577982377

theorem tailTrace_4610897 : CollatzResearch.WordTrace tailWord_4610897 prefixEnd_4610897 2367606409374151577982377 := by
  unfold tailWord_4610897
  simp only [CollatzResearch.WordTrace]
  refine ⟨168173229576515122358342945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112115486384343414905561963 168173229576515122358342945)
  ·
    refine ⟨126129922182386341768757209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 168173229576515122358342945 126129922182386341768757209)
    ·
      refine ⟨94597441636789756326567907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 126129922182386341768757209 94597441636789756326567907)
      ·
        refine ⟨141896162455184634489851861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 94597441636789756326567907 141896162455184634489851861)
        ·
          refine ⟨3325691307543389870855903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 141896162455184634489851861 3325691307543389870855903)
          ·
            refine ⟨4988536961315084806283855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3325691307543389870855903 4988536961315084806283855)
            ·
              refine ⟨7482805441972627209425783, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4988536961315084806283855 7482805441972627209425783)
              ·
                refine ⟨11224208162958940814138675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7482805441972627209425783 11224208162958940814138675)
                ·
                  refine ⟨16836312244438411221208013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11224208162958940814138675 16836312244438411221208013)
                  ·
                    refine ⟨6313617091664404207953005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16836312244438411221208013 6313617091664404207953005)
                    ·
                      refine ⟨2367606409374151577982377, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6313617091664404207953005 2367606409374151577982377)
                      ·
                        rfl

theorem cell23_4610897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 7, 1, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 7, 1, 1, 1, 1, 3, 3].length) (baseStart_4610897 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4610897 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4610897 prefixEnd_4610897 := by exact prefixLift 4610897
  have htrace : WordTrace (prefixWord ++ tailWord_4610897) baseStart_4610897 baseEnd_4610897 := by
    simpa [prefixWord, tailWord_4610897, baseEnd_4610897] using wordTrace_append hprefix tailTrace_4610897
  have hstable : (prefixWord ++ tailWord_4610897).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4610897).length < 2 ^ (prefixWord ++ tailWord_4610897).sum := by decide
  have hdescent : baseEnd_4610897 < baseStart_4610897 := by decide
  rcases family_descends (prefixWord ++ tailWord_4610897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4610943 : List Nat := [1, 1, 2, 2, 1, 1, 4, 6, 5]
def baseStart_4610943 : Nat := 118140960795 + 4610943 * 2 ^ 59
def prefixEnd_4610943 : Nat := 4983230072969 + 3 ^ 40 * 4610943 * 2
def baseEnd_4610943 : Nat := 263070003276028710889685

theorem tailTrace_4610943 : CollatzResearch.WordTrace tailWord_4610943 prefixEnd_4610943 263070003276028710889685 := by
  unfold tailWord_4610943
  simp only [CollatzResearch.WordTrace]
  refine ⟨168174907334348472214517483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112116604889565648143011655 168174907334348472214517483)
  ·
    refine ⟨252262361001522708321776225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 168174907334348472214517483 252262361001522708321776225)
    ·
      refine ⟨189196770751142031241332169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 252262361001522708321776225 189196770751142031241332169)
      ·
        refine ⟨141897578063356523430999127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 189196770751142031241332169 141897578063356523430999127)
        ·
          refine ⟨212846367095034785146498691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 141897578063356523430999127 212846367095034785146498691)
          ·
            refine ⟨319269550642552177719748037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 212846367095034785146498691 319269550642552177719748037)
            ·
              refine ⟨59863040745478533322452757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 319269550642552177719748037 59863040745478533322452757)
              ·
                refine ⟨2806080034944306249489973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 59863040745478533322452757 2806080034944306249489973)
                ·
                  refine ⟨263070003276028710889685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2806080034944306249489973 263070003276028710889685)
                  ·
                    rfl

theorem cell23_4610943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 4, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 4, 6, 5].length) (baseStart_4610943 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4610943 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4610943 prefixEnd_4610943 := by exact prefixLift 4610943
  have htrace : WordTrace (prefixWord ++ tailWord_4610943) baseStart_4610943 baseEnd_4610943 := by
    simpa [prefixWord, tailWord_4610943, baseEnd_4610943] using wordTrace_append hprefix tailTrace_4610943
  have hstable : (prefixWord ++ tailWord_4610943).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4610943).length < 2 ^ (prefixWord ++ tailWord_4610943).sum := by decide
  have hdescent : baseEnd_4610943 < baseStart_4610943 := by decide
  rcases family_descends (prefixWord ++ tailWord_4610943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4610954 : List Nat := [3, 1, 2, 4, 1, 2, 1, 3, 2, 2, 2]
def baseStart_4610954 : Nat := 118140960795 + 4610954 * 2 ^ 59
def prefixEnd_4610954 : Nat := 4983230072969 + 3 ^ 40 * 4610954 * 2
def baseEnd_4610954 : Nat := 2367635677771457854969615

theorem tailTrace_4610954 : CollatzResearch.WordTrace tailWord_4610954 prefixEnd_4610954 2367635677771457854969615 := by
  unfold tailWord_4610954
  simp only [CollatzResearch.WordTrace]
  refine ⟨42043827134327155273291979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 112116872358205747395445277 42043827134327155273291979)
  ·
    refine ⟨63065740701490732909937969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42043827134327155273291979 63065740701490732909937969)
    ·
      refine ⟨47299305526118049682453477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 63065740701490732909937969 47299305526118049682453477)
      ·
        refine ⟨8868619786147134315460027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 47299305526118049682453477 8868619786147134315460027)
        ·
          refine ⟨13302929679220701473190041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8868619786147134315460027 13302929679220701473190041)
          ·
            refine ⟨9977197259415526104892531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13302929679220701473190041 9977197259415526104892531)
            ·
              refine ⟨14965795889123289157338797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9977197259415526104892531 14965795889123289157338797)
              ·
                refine ⟨5612173458421233434002049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14965795889123289157338797 5612173458421233434002049)
                ·
                  refine ⟨4209130093815925075501537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5612173458421233434002049 4209130093815925075501537)
                  ·
                    refine ⟨3156847570361943806626153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4209130093815925075501537 3156847570361943806626153)
                    ·
                      refine ⟨2367635677771457854969615, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3156847570361943806626153 2367635677771457854969615)
                      ·
                        rfl

theorem cell23_4610954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 2, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 2, 1, 3, 2, 2, 2].length) (baseStart_4610954 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4610954 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4610954 prefixEnd_4610954 := by exact prefixLift 4610954
  have htrace : WordTrace (prefixWord ++ tailWord_4610954) baseStart_4610954 baseEnd_4610954 := by
    simpa [prefixWord, tailWord_4610954, baseEnd_4610954] using wordTrace_append hprefix tailTrace_4610954
  have hstable : (prefixWord ++ tailWord_4610954).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4610954).length < 2 ^ (prefixWord ++ tailWord_4610954).sum := by decide
  have hdescent : baseEnd_4610954 < baseStart_4610954 := by decide
  rcases family_descends (prefixWord ++ tailWord_4610954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4610956 : List Nat := [2, 2, 1, 2, 1, 2, 2, 1, 3, 7]
def baseStart_4610956 : Nat := 118140960795 + 4610956 * 2 ^ 59
def prefixEnd_4610956 : Nat := 4983230072969 + 3 ^ 40 * 4610956 * 2
def baseEnd_4610956 : Nat := 789212234910922282381535

theorem tailTrace_4610956 : CollatzResearch.WordTrace tailWord_4610956 prefixEnd_4610956 789212234910922282381535 := by
  unfold tailWord_4610956
  simp only [CollatzResearch.WordTrace]
  refine ⟨84087690741650687717370361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 112116920988867583623160481 84087690741650687717370361)
  ·
    refine ⟨63065768056238015788027771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 84087690741650687717370361 63065768056238015788027771)
    ·
      refine ⟨94598652084357023682041657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63065768056238015788027771 94598652084357023682041657)
      ·
        refine ⟨70948989063267767761531243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 94598652084357023682041657 70948989063267767761531243)
        ·
          refine ⟨106423483594901651642296865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 70948989063267767761531243 106423483594901651642296865)
          ·
            refine ⟨79817612696176238731722649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 106423483594901651642296865 79817612696176238731722649)
            ·
              refine ⟨59863209522132179048791987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 79817612696176238731722649 59863209522132179048791987)
              ·
                refine ⟨89794814283198268573187981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 59863209522132179048791987 89794814283198268573187981)
                ·
                  refine ⟨33673055356199350714945493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 89794814283198268573187981 33673055356199350714945493)
                  ·
                    refine ⟨789212234910922282381535, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 33673055356199350714945493 789212234910922282381535)
                    ·
                      rfl

theorem cell23_4610956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 2, 1, 3, 7].length) (baseStart_4610956 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4610956 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4610956 prefixEnd_4610956 := by exact prefixLift 4610956
  have htrace : WordTrace (prefixWord ++ tailWord_4610956) baseStart_4610956 baseEnd_4610956 := by
    simpa [prefixWord, tailWord_4610956, baseEnd_4610956] using wordTrace_append hprefix tailTrace_4610956
  have hstable : (prefixWord ++ tailWord_4610956).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4610956).length < 2 ^ (prefixWord ++ tailWord_4610956).sum := by decide
  have hdescent : baseEnd_4610956 < baseStart_4610956 := by decide
  rcases family_descends (prefixWord ++ tailWord_4610956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4610963 : List Nat := [1, 1, 1, 2, 1, 2, 1, 3, 4, 5, 2]
def baseStart_4610963 : Nat := 118140960795 + 4610963 * 2 ^ 59
def prefixEnd_4610963 : Nat := 4983230072969 + 3 ^ 40 * 4610963 * 2
def baseEnd_4610963 : Nat := 2367640299097348319757073

theorem tailTrace_4610963 : CollatzResearch.WordTrace tailWord_4610963 prefixEnd_4610963 2367640299097348319757073 := by
  unfold tailWord_4610963
  simp only [CollatzResearch.WordTrace]
  refine ⟨168175636794276015630245543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112117091196184010420163695 168175636794276015630245543)
  ·
    refine ⟨252263455191414023445368315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 168175636794276015630245543 252263455191414023445368315)
    ·
      refine ⟨378395182787121035168052473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 252263455191414023445368315 378395182787121035168052473)
      ·
        refine ⟨283796387090340776376039355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 378395182787121035168052473 283796387090340776376039355)
        ·
          refine ⟨425694580635511164564059033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 283796387090340776376039355 425694580635511164564059033)
          ·
            refine ⟨319270935476633373423044275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 425694580635511164564059033 319270935476633373423044275)
            ·
              refine ⟨478906403214950060134566413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 319270935476633373423044275 478906403214950060134566413)
              ·
                refine ⟨179589901205606272550462405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 478906403214950060134566413 179589901205606272550462405)
                ·
                  refine ⟨33673106476051176103211701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 179589901205606272550462405 33673106476051176103211701)
                  ·
                    refine ⟨3156853732129797759676097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 33673106476051176103211701 3156853732129797759676097)
                    ·
                      refine ⟨2367640299097348319757073, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3156853732129797759676097 2367640299097348319757073)
                      ·
                        rfl

theorem cell23_4610963_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 3, 4, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 3, 4, 5, 2].length) (baseStart_4610963 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4610963 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4610963 prefixEnd_4610963 := by exact prefixLift 4610963
  have htrace : WordTrace (prefixWord ++ tailWord_4610963) baseStart_4610963 baseEnd_4610963 := by
    simpa [prefixWord, tailWord_4610963, baseEnd_4610963] using wordTrace_append hprefix tailTrace_4610963
  have hstable : (prefixWord ++ tailWord_4610963).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4610963).length < 2 ^ (prefixWord ++ tailWord_4610963).sum := by decide
  have hdescent : baseEnd_4610963 < baseStart_4610963 := by decide
  rcases family_descends (prefixWord ++ tailWord_4610963) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4611020 : List Nat := [2, 2, 1, 4, 1, 1, 3, 2, 3, 4]
def baseStart_4611020 : Nat := 118140960795 + 4611020 * 2 ^ 59
def prefixEnd_4611020 : Nat := 4983230072969 + 3 ^ 40 * 4611020 * 2
def baseEnd_4611020 : Nat := 789223189164884865581437

theorem tailTrace_4611020 : CollatzResearch.WordTrace tailWord_4611020 prefixEnd_4611020 789223189164884865581437 := by
  unfold tailWord_4611020
  simp only [CollatzResearch.WordTrace]
  refine ⟨84088857877534757182535257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 112118477170046342910047009 84088857877534757182535257)
  ·
    refine ⟨63066643408151067886901443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 84088857877534757182535257 63066643408151067886901443)
    ·
      refine ⟨94599965112226601830352165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63066643408151067886901443 94599965112226601830352165)
      ·
        refine ⟨17737493458542487843191031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 94599965112226601830352165 17737493458542487843191031)
        ·
          refine ⟨26606240187813731764786547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17737493458542487843191031 26606240187813731764786547)
          ·
            refine ⟨39909360281720597647179821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26606240187813731764786547 39909360281720597647179821)
            ·
              refine ⟨14966010105645224117692433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 39909360281720597647179821 14966010105645224117692433)
              ·
                refine ⟨11224507579233918088269325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14966010105645224117692433 11224507579233918088269325)
                ·
                  refine ⟨4209190342212719283100997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11224507579233918088269325 4209190342212719283100997)
                  ·
                    refine ⟨789223189164884865581437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4209190342212719283100997 789223189164884865581437)
                    ·
                      rfl

theorem cell23_4611020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 3, 2, 3, 4].length) (baseStart_4611020 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4611020 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4611020 prefixEnd_4611020 := by exact prefixLift 4611020
  have htrace : WordTrace (prefixWord ++ tailWord_4611020) baseStart_4611020 baseEnd_4611020 := by
    simpa [prefixWord, tailWord_4611020, baseEnd_4611020] using wordTrace_append hprefix tailTrace_4611020
  have hstable : (prefixWord ++ tailWord_4611020).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4611020).length < 2 ^ (prefixWord ++ tailWord_4611020).sum := by decide
  have hdescent : baseEnd_4611020 < baseStart_4611020 := by decide
  rcases family_descends (prefixWord ++ tailWord_4611020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4611050 : List Nat := [3, 1, 3, 1, 2, 2, 3, 2, 6]
def baseStart_4611050 : Nat := 118140960795 + 4611050 * 2 ^ 59
def prefixEnd_4611050 : Nat := 4983230072969 + 3 ^ 40 * 4611050 * 2
def baseEnd_4611050 : Nat := 263076107990476608818797

theorem tailTrace_4611050 : CollatzResearch.WordTrace tailWord_4611050 prefixEnd_4611050 263076107990476608818797 := by
  unfold tailWord_4611050
  simp only [CollatzResearch.WordTrace]
  refine ⟨42044702486240207372165651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 112119206629973886325775069 42044702486240207372165651)
  ·
    refine ⟨63067053729360311058248477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42044702486240207372165651 63067053729360311058248477)
    ·
      refine ⟨23650145148510116646843179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 63067053729360311058248477 23650145148510116646843179)
      ·
        refine ⟨35475217722765174970264769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23650145148510116646843179 35475217722765174970264769)
        ·
          refine ⟨26606413292073881227698577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35475217722765174970264769 26606413292073881227698577)
          ·
            refine ⟨19954809969055410920773933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26606413292073881227698577 19954809969055410920773933)
            ·
              refine ⟨7483053738395779095290225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19954809969055410920773933 7483053738395779095290225)
              ·
                refine ⟨5612290303796834321467669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7483053738395779095290225 5612290303796834321467669)
                ·
                  refine ⟨263076107990476608818797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5612290303796834321467669 263076107990476608818797)
                  ·
                    rfl

theorem cell23_4611050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 3, 2, 6].length) (baseStart_4611050 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4611050 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4611050 prefixEnd_4611050 := by exact prefixLift 4611050
  have htrace : WordTrace (prefixWord ++ tailWord_4611050) baseStart_4611050 baseEnd_4611050 := by
    simpa [prefixWord, tailWord_4611050, baseEnd_4611050] using wordTrace_append hprefix tailTrace_4611050
  have hstable : (prefixWord ++ tailWord_4611050).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4611050).length < 2 ^ (prefixWord ++ tailWord_4611050).sum := by decide
  have hdescent : baseEnd_4611050 < baseStart_4611050 := by decide
  rcases family_descends (prefixWord ++ tailWord_4611050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4611080 : List Nat := [2, 1, 3, 2, 1, 3, 1, 4, 1, 5]
def baseStart_4611080 : Nat := 118140960795 + 4611080 * 2 ^ 59
def prefixEnd_4611080 : Nat := 4983230072969 + 3 ^ 40 * 4611080 * 2
def baseEnd_4611080 : Nat := 789233458777974787331345

theorem tailTrace_4611080 : CollatzResearch.WordTrace tailWord_4611080 prefixEnd_4611080 789233458777974787331345 := by
  unfold tailWord_4611080
  simp only [CollatzResearch.WordTrace]
  refine ⟨84089952067426072306127347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 112119936089901429741503129 84089952067426072306127347)
  ·
    refine ⟨126134928101139108459191021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84089952067426072306127347 126134928101139108459191021)
    ·
      refine ⟨47300598037927165672196633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 126134928101139108459191021 47300598037927165672196633)
      ·
        refine ⟨35475448528445374254147475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47300598037927165672196633 35475448528445374254147475)
        ·
          refine ⟨53213172792668061381221213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35475448528445374254147475 53213172792668061381221213)
          ·
            refine ⟨19954939797250523017957955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 53213172792668061381221213 19954939797250523017957955)
            ·
              refine ⟨29932409695875784526936933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19954939797250523017957955 29932409695875784526936933)
              ·
                refine ⟨5612326817976709598800675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 29932409695875784526936933 5612326817976709598800675)
                ·
                  refine ⟨8418490226965064398201013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5612326817976709598800675 8418490226965064398201013)
                  ·
                    refine ⟨789233458777974787331345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8418490226965064398201013 789233458777974787331345)
                    ·
                      rfl

theorem cell23_4611080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 1, 4, 1, 5].length) (baseStart_4611080 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4611080 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4611080 prefixEnd_4611080 := by exact prefixLift 4611080
  have htrace : WordTrace (prefixWord ++ tailWord_4611080) baseStart_4611080 baseEnd_4611080 := by
    simpa [prefixWord, tailWord_4611080, baseEnd_4611080] using wordTrace_append hprefix tailTrace_4611080
  have hstable : (prefixWord ++ tailWord_4611080).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4611080).length < 2 ^ (prefixWord ++ tailWord_4611080).sum := by decide
  have hdescent : baseEnd_4611080 < baseStart_4611080 := by decide
  rcases family_descends (prefixWord ++ tailWord_4611080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4611111 : List Nat := [1, 1, 7, 1, 1, 3, 1, 1, 3, 1, 3]
def baseStart_4611111 : Nat := 118140960795 + 4611111 * 2 ^ 59
def prefixEnd_4611111 : Nat := 4983230072969 + 3 ^ 40 * 4611111 * 2
def baseEnd_4611111 : Nat := 2367716294234213740706393

theorem tailTrace_4611111 : CollatzResearch.WordTrace tailWord_4611111 prefixEnd_4611111 2367716294234213740706393 := by
  unfold tailWord_4611111
  simp only [CollatzResearch.WordTrace]
  refine ⟨168181034797739836906633187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112120689865159891271088791 168181034797739836906633187)
  ·
    refine ⟨252271552196609755359949781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 168181034797739836906633187 252271552196609755359949781)
    ·
      refine ⟨5912614504608041141248823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 252271552196609755359949781 5912614504608041141248823)
      ·
        refine ⟨8868921756912061711873235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5912614504608041141248823 8868921756912061711873235)
        ·
          refine ⟨13303382635368092567809853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8868921756912061711873235 13303382635368092567809853)
          ·
            refine ⟨4988768488263034712928695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13303382635368092567809853 4988768488263034712928695)
            ·
              refine ⟨7483152732394552069393043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4988768488263034712928695 7483152732394552069393043)
              ·
                refine ⟨11224729098591828104089565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7483152732394552069393043 11224729098591828104089565)
                ·
                  refine ⟨4209273411971935539033587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11224729098591828104089565 4209273411971935539033587)
                  ·
                    refine ⟨6313910117957903308550381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4209273411971935539033587 6313910117957903308550381)
                    ·
                      refine ⟨2367716294234213740706393, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6313910117957903308550381 2367716294234213740706393)
                      ·
                        rfl

theorem cell23_4611111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 3, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 3, 1, 1, 3, 1, 3].length) (baseStart_4611111 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4611111 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4611111 prefixEnd_4611111 := by exact prefixLift 4611111
  have htrace : WordTrace (prefixWord ++ tailWord_4611111) baseStart_4611111 baseEnd_4611111 := by
    simpa [prefixWord, tailWord_4611111, baseEnd_4611111] using wordTrace_append hprefix tailTrace_4611111
  have hstable : (prefixWord ++ tailWord_4611111).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4611111).length < 2 ^ (prefixWord ++ tailWord_4611111).sum := by decide
  have hdescent : baseEnd_4611111 < baseStart_4611111 := by decide
  rcases family_descends (prefixWord ++ tailWord_4611111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4611120 : List Nat := [2, 1, 1, 1, 2, 4, 2, 2, 3, 2, 3]
def baseStart_4611120 : Nat := 118140960795 + 4611120 * 2 ^ 59
def prefixEnd_4611120 : Nat := 4983230072969 + 3 ^ 40 * 4611120 * 2
def baseEnd_4611120 : Nat := 2367720915560104205493851

theorem tailTrace_4611120 : CollatzResearch.WordTrace tailWord_4611120 prefixEnd_4611120 2367720915560104205493851 := by
  unfold tailWord_4611120
  simp only [CollatzResearch.WordTrace]
  refine ⟨84090681527353615721855407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 112120908703138154295807209 84090681527353615721855407)
  ·
    refine ⟨126136022291030423582783111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84090681527353615721855407 126136022291030423582783111)
    ·
      refine ⟨189204033436545635374174667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 126136022291030423582783111 189204033436545635374174667)
      ·
        refine ⟨283806050154818453061262001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 189204033436545635374174667 283806050154818453061262001)
        ·
          refine ⟨212854537616113839795946501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 283806050154818453061262001 212854537616113839795946501)
          ·
            refine ⟨39910225803021344961739969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 212854537616113839795946501 39910225803021344961739969)
            ·
              refine ⟨29932669352266008721304977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 39910225803021344961739969 29932669352266008721304977)
              ·
                refine ⟨22449502014199506540978733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29932669352266008721304977 22449502014199506540978733)
                ·
                  refine ⟨8418563255324814952867025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22449502014199506540978733 8418563255324814952867025)
                  ·
                    refine ⟨6313922441493611214650269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8418563255324814952867025 6313922441493611214650269)
                    ·
                      refine ⟨2367720915560104205493851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6313922441493611214650269 2367720915560104205493851)
                      ·
                        rfl

theorem cell23_4611120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 2, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 2, 2, 3, 2, 3].length) (baseStart_4611120 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4611120 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4611120 prefixEnd_4611120 := by exact prefixLift 4611120
  have htrace : WordTrace (prefixWord ++ tailWord_4611120) baseStart_4611120 baseEnd_4611120 := by
    simpa [prefixWord, tailWord_4611120, baseEnd_4611120] using wordTrace_append hprefix tailTrace_4611120
  have hstable : (prefixWord ++ tailWord_4611120).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4611120).length < 2 ^ (prefixWord ++ tailWord_4611120).sum := by decide
  have hdescent : baseEnd_4611120 < baseStart_4611120 := by decide
  rcases family_descends (prefixWord ++ tailWord_4611120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4611134 : List Nat := [4, 2, 1, 3, 1, 1, 3, 2, 1, 1, 4]
def baseStart_4611134 : Nat := 118140960795 + 4611134 * 2 ^ 59
def prefixEnd_4611134 : Nat := 4983230072969 + 3 ^ 40 * 4611134 * 2
def baseEnd_4611134 : Nat := 2367728104289267150718787

theorem tailTrace_4611134 : CollatzResearch.WordTrace tailWord_4611134 prefixEnd_4611134 2367728104289267150718787 := by
  unfold tailWord_4611134
  simp only [CollatzResearch.WordTrace]
  refine ⟨21022734209582063979340057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 112121249117771007889813637 21022734209582063979340057)
  ·
    refine ⟨15767050657186547984505043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21022734209582063979340057 15767050657186547984505043)
    ·
      refine ⟨23650575985779821976757565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15767050657186547984505043 23650575985779821976757565)
      ·
        refine ⟨8868965994667433241284087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23650575985779821976757565 8868965994667433241284087)
        ·
          refine ⟨13303448992001149861926131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8868965994667433241284087 13303448992001149861926131)
          ·
            refine ⟨19955173488001724792889197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13303448992001149861926131 19955173488001724792889197)
            ·
              refine ⟨7483190058000646797333449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19955173488001724792889197 7483190058000646797333449)
              ·
                refine ⟨5612392543500485098000087, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7483190058000646797333449 5612392543500485098000087)
                ·
                  refine ⟨8418588815250727647000131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5612392543500485098000087 8418588815250727647000131)
                  ·
                    refine ⟨12627883222876091470500197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8418588815250727647000131 12627883222876091470500197)
                    ·
                      refine ⟨2367728104289267150718787, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12627883222876091470500197 2367728104289267150718787)
                      ·
                        rfl

theorem cell23_4611134_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 3, 2, 1, 1, 4].length) (baseStart_4611134 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4611134 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4611134 prefixEnd_4611134 := by exact prefixLift 4611134
  have htrace : WordTrace (prefixWord ++ tailWord_4611134) baseStart_4611134 baseEnd_4611134 := by
    simpa [prefixWord, tailWord_4611134, baseEnd_4611134] using wordTrace_append hprefix tailTrace_4611134
  have hstable : (prefixWord ++ tailWord_4611134).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4611134).length < 2 ^ (prefixWord ++ tailWord_4611134).sum := by decide
  have hdescent : baseEnd_4611134 < baseStart_4611134 := by decide
  rcases family_descends (prefixWord ++ tailWord_4611134) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4611177 : List Nat := [1, 2, 1, 1, 1, 6, 1, 2, 3, 3, 2]
def baseStart_4611177 : Nat := 118140960795 + 4611177 * 2 ^ 59
def prefixEnd_4611177 : Nat := 4983230072969 + 3 ^ 40 * 4611177 * 2
def baseEnd_4611177 : Nat := 2367750183957410482481089

theorem tailTrace_4611177 : CollatzResearch.WordTrace tailWord_4611177 prefixEnd_4611177 2367750183957410482481089 := by
  unfold tailWord_4611177
  simp only [CollatzResearch.WordTrace]
  refine ⟨168183442015500730178535785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112122294677000486785690523 168183442015500730178535785)
  ·
    refine ⟨126137581511625547633901839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 168183442015500730178535785 126137581511625547633901839)
    ·
      refine ⟨189206372267438321450852759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 126137581511625547633901839 189206372267438321450852759)
      ·
        refine ⟨283809558401157482176279139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 189206372267438321450852759 283809558401157482176279139)
        ·
          refine ⟨425714337601736223264418709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 283809558401157482176279139 425714337601736223264418709)
          ·
            refine ⟨19955359575081385465519627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 425714337601736223264418709 19955359575081385465519627)
            ·
              refine ⟨29933039362622078198279441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19955359575081385465519627 29933039362622078198279441)
              ·
                refine ⟨22449779521966558648709581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29933039362622078198279441 22449779521966558648709581)
                ·
                  refine ⟨8418667320737459493266093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22449779521966558648709581 8418667320737459493266093)
                  ·
                    refine ⟨3157000245276547309974785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8418667320737459493266093 3157000245276547309974785)
                    ·
                      refine ⟨2367750183957410482481089, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3157000245276547309974785 2367750183957410482481089)
                      ·
                        rfl

theorem cell23_4611177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 1, 2, 3, 3, 2].length) (baseStart_4611177 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4611177 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4611177 prefixEnd_4611177 := by exact prefixLift 4611177
  have htrace : WordTrace (prefixWord ++ tailWord_4611177) baseStart_4611177 baseEnd_4611177 := by
    simpa [prefixWord, tailWord_4611177, baseEnd_4611177] using wordTrace_append hprefix tailTrace_4611177
  have hstable : (prefixWord ++ tailWord_4611177).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4611177).length < 2 ^ (prefixWord ++ tailWord_4611177).sum := by decide
  have hdescent : baseEnd_4611177 < baseStart_4611177 := by decide
  rcases family_descends (prefixWord ++ tailWord_4611177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4611210 : List Nat := [3, 1, 2, 3, 1, 1, 2, 1, 1, 3, 5]
def baseStart_4611210 : Nat := 118140960795 + 4611210 * 2 ^ 59
def prefixEnd_4611210 : Nat := 4983230072969 + 3 ^ 40 * 4611210 * 2
def baseEnd_4611210 : Nat := 2367767128819008853368437

theorem tailTrace_4611210 : CollatzResearch.WordTrace tailWord_4611210 prefixEnd_4611210 2367767128819008853368437 := by
  unfold tailWord_4611210
  simp only [CollatzResearch.WordTrace]
  refine ⟨42046161406095294203621771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 112123097082920784542991389 42046161406095294203621771)
  ·
    refine ⟨63069242109142941305432657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42046161406095294203621771 63069242109142941305432657)
    ·
      refine ⟨47301931581857205979074493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 63069242109142941305432657 47301931581857205979074493)
      ·
        refine ⟨17738224343196452242152935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 47301931581857205979074493 17738224343196452242152935)
        ·
          refine ⟨26607336514794678363229403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17738224343196452242152935 26607336514794678363229403)
          ·
            refine ⟨39911004772192017544844105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26607336514794678363229403 39911004772192017544844105)
            ·
              refine ⟨29933253579144013158633079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 39911004772192017544844105 29933253579144013158633079)
              ·
                refine ⟨44899880368716019737949619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29933253579144013158633079 44899880368716019737949619)
                ·
                  refine ⟨67349820553074029606924429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 44899880368716019737949619 67349820553074029606924429)
                  ·
                    refine ⟨25256182707402761102596661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 67349820553074029606924429 25256182707402761102596661)
                    ·
                      refine ⟨2367767128819008853368437, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25256182707402761102596661 2367767128819008853368437)
                      ·
                        rfl

theorem cell23_4611210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 2, 1, 1, 3, 5].length) (baseStart_4611210 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4611210 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4611210 prefixEnd_4611210 := by exact prefixLift 4611210
  have htrace : WordTrace (prefixWord ++ tailWord_4611210) baseStart_4611210 baseEnd_4611210 := by
    simpa [prefixWord, tailWord_4611210, baseEnd_4611210] using wordTrace_append hprefix tailTrace_4611210
  have hstable : (prefixWord ++ tailWord_4611210).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4611210).length < 2 ^ (prefixWord ++ tailWord_4611210).sum := by decide
  have hdescent : baseEnd_4611210 < baseStart_4611210 := by decide
  rcases family_descends (prefixWord ++ tailWord_4611210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4611337 : List Nat := [1, 2, 1, 1, 3, 3, 4, 2, 6]
def baseStart_4611337 : Nat := 118140960795 + 4611337 * 2 ^ 59
def prefixEnd_4611337 : Nat := 4983230072969 + 3 ^ 40 * 4611337 * 2
def baseEnd_4611337 : Nat := 263092482318014428497817

theorem tailTrace_4611337 : CollatzResearch.WordTrace tailWord_4611337 prefixEnd_4611337 263092482318014428497817 := by
  unfold tailWord_4611337
  simp only [CollatzResearch.WordTrace]
  refine ⟨168189277694921077504360265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112126185129947385002906843 168189277694921077504360265)
  ·
    refine ⟨126141958271190808128270199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 168189277694921077504360265 126141958271190808128270199)
    ·
      refine ⟨189212937406786212192405299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 126141958271190808128270199 189212937406786212192405299)
      ·
        refine ⟨283819406110179318288607949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 189212937406786212192405299 283819406110179318288607949)
        ·
          refine ⟨106432277291317244358227981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 283819406110179318288607949 106432277291317244358227981)
          ·
            refine ⟨39912103984243966634335493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 106432277291317244358227981 39912103984243966634335493)
            ·
              refine ⟨7483519497045743743937905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 39912103984243966634335493 7483519497045743743937905)
              ·
                refine ⟨5612639622784307807953429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7483519497045743743937905 5612639622784307807953429)
                ·
                  refine ⟨263092482318014428497817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5612639622784307807953429 263092482318014428497817)
                  ·
                    rfl

theorem cell23_4611337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 4, 2, 6].length) (baseStart_4611337 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4611337 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4611337 prefixEnd_4611337 := by exact prefixLift 4611337
  have htrace : WordTrace (prefixWord ++ tailWord_4611337) baseStart_4611337 baseEnd_4611337 := by
    simpa [prefixWord, tailWord_4611337, baseEnd_4611337] using wordTrace_append hprefix tailTrace_4611337
  have hstable : (prefixWord ++ tailWord_4611337).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4611337).length < 2 ^ (prefixWord ++ tailWord_4611337).sum := by decide
  have hdescent : baseEnd_4611337 < baseStart_4611337 := by decide
  rcases family_descends (prefixWord ++ tailWord_4611337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4611358 : List Nat := [4, 3, 2, 1, 2, 1, 1, 2, 3, 4]
def baseStart_4611358 : Nat := 118140960795 + 4611358 * 2 ^ 59
def prefixEnd_4611358 : Nat := 4983230072969 + 3 ^ 40 * 4611358 * 2
def baseEnd_4611358 : Nat := 789281041318624758105919

theorem tailTrace_4611358 : CollatzResearch.WordTrace tailWord_4611358 prefixEnd_4611358 789281041318624758105919 := by
  unfold tailWord_4611358
  simp only [CollatzResearch.WordTrace]
  refine ⟨21023755453480624761359341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 112126695751896665393916485 21023755453480624761359341)
  ·
    refine ⟨7883908295055234285509753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21023755453480624761359341 7883908295055234285509753)
    ·
      refine ⟨5912931221291425714132315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7883908295055234285509753 5912931221291425714132315)
      ·
        refine ⟨8869396831937138571198473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5912931221291425714132315 8869396831937138571198473)
        ·
          refine ⟨6652047623952853928398855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8869396831937138571198473 6652047623952853928398855)
          ·
            refine ⟨9978071435929280892598283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6652047623952853928398855 9978071435929280892598283)
            ·
              refine ⟨14967107153893921338897425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9978071435929280892598283 14967107153893921338897425)
              ·
                refine ⟨11225330365420441004173069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14967107153893921338897425 11225330365420441004173069)
                ·
                  refine ⟨4209498887032665376564901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11225330365420441004173069 4209498887032665376564901)
                  ·
                    refine ⟨789281041318624758105919, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4209498887032665376564901 789281041318624758105919)
                    ·
                      rfl

theorem cell23_4611358_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 2, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 2, 1, 1, 2, 3, 4].length) (baseStart_4611358 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4611358 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4611358 prefixEnd_4611358 := by exact prefixLift 4611358
  have htrace : WordTrace (prefixWord ++ tailWord_4611358) baseStart_4611358 baseEnd_4611358 := by
    simpa [prefixWord, tailWord_4611358, baseEnd_4611358] using wordTrace_append hprefix tailTrace_4611358
  have hstable : (prefixWord ++ tailWord_4611358).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4611358).length < 2 ^ (prefixWord ++ tailWord_4611358).sum := by decide
  have hdescent : baseEnd_4611358 < baseStart_4611358 := by decide
  rcases family_descends (prefixWord ++ tailWord_4611358) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4611427 : List Nat := [1, 1, 1, 5, 2, 3, 1, 9]
def baseStart_4611427 : Nat := 118140960795 + 4611427 * 2 ^ 59
def prefixEnd_4611427 : Nat := 4983230072969 + 3 ^ 40 * 4611427 * 2
def baseEnd_4611427 : Nat := 87699205708186463124257

theorem tailTrace_4611427 : CollatzResearch.WordTrace tailWord_4611427 prefixEnd_4611427 87699205708186463124257 := by
  unfold tailWord_4611427
  simp only [CollatzResearch.WordTrace]
  refine ⟨168192560264595022875136535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112128373509730015250091023 168192560264595022875136535)
  ·
    refine ⟨252288840396892534312704803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 168192560264595022875136535 252288840396892534312704803)
    ·
      refine ⟨378433260595338801469057205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 252288840396892534312704803 378433260595338801469057205)
      ·
        refine ⟨35478118180813012637724113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 378433260595338801469057205 35478118180813012637724113)
        ·
          refine ⟨26608588635609759478293085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35478118180813012637724113 26608588635609759478293085)
          ·
            refine ⟨9978220738353659804359907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26608588635609759478293085 9978220738353659804359907)
            ·
              refine ⟨14967331107530489706539861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9978220738353659804359907 14967331107530489706539861)
              ·
                refine ⟨87699205708186463124257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 14967331107530489706539861 87699205708186463124257)
                ·
                  rfl

theorem cell23_4611427_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 3, 1, 9].length) (baseStart_4611427 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4611427 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4611427 prefixEnd_4611427 := by exact prefixLift 4611427
  have htrace : WordTrace (prefixWord ++ tailWord_4611427) baseStart_4611427 baseEnd_4611427 := by
    simpa [prefixWord, tailWord_4611427, baseEnd_4611427] using wordTrace_append hprefix tailTrace_4611427
  have hstable : (prefixWord ++ tailWord_4611427).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4611427).length < 2 ^ (prefixWord ++ tailWord_4611427).sum := by decide
  have hdescent : baseEnd_4611427 < baseStart_4611427 := by decide
  rcases family_descends (prefixWord ++ tailWord_4611427) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4611432 : List Nat := [2, 1, 4, 2, 4, 1, 1, 3, 1, 1, 3]
def baseStart_4611432 : Nat := 118140960795 + 4611432 * 2 ^ 59
def prefixEnd_4611432 : Nat := 4983230072969 + 3 ^ 40 * 4611432 * 2
def baseEnd_4611432 : Nat := 2367881121524306984792417

theorem tailTrace_4611432 : CollatzResearch.WordTrace tailWord_4611432 prefixEnd_4611432 2367881121524306984792417 := by
  unfold tailWord_4611432
  simp only [CollatzResearch.WordTrace]
  refine ⟨84096371314788454364534275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 112128495086384605819379033 84096371314788454364534275)
  ·
    refine ⟨126144556972182681546801413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84096371314788454364534275 126144556972182681546801413)
    ·
      refine ⟨23652104432284252790025265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 126144556972182681546801413 23652104432284252790025265)
      ·
        refine ⟨17739078324213189592518949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23652104432284252790025265 17739078324213189592518949)
        ·
          refine ⟨3326077185789973048597303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 17739078324213189592518949 3326077185789973048597303)
          ·
            refine ⟨4989115778684959572895955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3326077185789973048597303 4989115778684959572895955)
            ·
              refine ⟨7483673668027439359343933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4989115778684959572895955 7483673668027439359343933)
              ·
                refine ⟨2806377625510289759753975, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7483673668027439359343933 2806377625510289759753975)
                ·
                  refine ⟨4209566438265434639630963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2806377625510289759753975 4209566438265434639630963)
                  ·
                    refine ⟨6314349657398151959446445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4209566438265434639630963 6314349657398151959446445)
                    ·
                      refine ⟨2367881121524306984792417, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6314349657398151959446445 2367881121524306984792417)
                      ·
                        rfl

theorem cell23_4611432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 4, 1, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 4, 1, 1, 3, 1, 1, 3].length) (baseStart_4611432 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4611432 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4611432 prefixEnd_4611432 := by exact prefixLift 4611432
  have htrace : WordTrace (prefixWord ++ tailWord_4611432) baseStart_4611432 baseEnd_4611432 := by
    simpa [prefixWord, tailWord_4611432, baseEnd_4611432] using wordTrace_append hprefix tailTrace_4611432
  have hstable : (prefixWord ++ tailWord_4611432).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4611432).length < 2 ^ (prefixWord ++ tailWord_4611432).sum := by decide
  have hdescent : baseEnd_4611432 < baseStart_4611432 := by decide
  rcases family_descends (prefixWord ++ tailWord_4611432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4611465 : List Nat := [1, 2, 1, 1, 8, 1, 2, 1, 2, 4]
def baseStart_4611465 : Nat := 118140960795 + 4611465 * 2 ^ 59
def prefixEnd_4611465 : Nat := 4983230072969 + 3 ^ 40 * 4611465 * 2
def baseEnd_4611465 : Nat := 789299355461968451893255

theorem tailTrace_4611465 : CollatzResearch.WordTrace tailWord_4611465 prefixEnd_4611465 789299355461968451893255 := by
  unfold tailWord_4611465
  simp only [CollatzResearch.WordTrace]
  refine ⟨168193946238457355365019849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112129297492304903576679899 168193946238457355365019849)
  ·
    refine ⟨126145459678843016523764887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 168193946238457355365019849 126145459678843016523764887)
    ·
      refine ⟨189218189518264524785647331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 126145459678843016523764887 189218189518264524785647331)
      ·
        refine ⟨283827284277396787178470997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 189218189518264524785647331 283827284277396787178470997)
        ·
          refine ⟨3326100987625743599747707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 283827284277396787178470997 3326100987625743599747707)
          ·
            refine ⟨4989151481438615399621561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3326100987625743599747707 4989151481438615399621561)
            ·
              refine ⟨3741863611078961549716171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4989151481438615399621561 3741863611078961549716171)
              ·
                refine ⟨5612795416618442324574257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3741863611078961549716171 5612795416618442324574257)
                ·
                  refine ⟨4209596562463831743430693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5612795416618442324574257 4209596562463831743430693)
                  ·
                    refine ⟨789299355461968451893255, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4209596562463831743430693 789299355461968451893255)
                    ·
                      rfl

theorem cell23_4611465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 8, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 8, 1, 2, 1, 2, 4].length) (baseStart_4611465 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4611465 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4611465 prefixEnd_4611465 := by exact prefixLift 4611465
  have htrace : WordTrace (prefixWord ++ tailWord_4611465) baseStart_4611465 baseEnd_4611465 := by
    simpa [prefixWord, tailWord_4611465, baseEnd_4611465] using wordTrace_append hprefix tailTrace_4611465
  have hstable : (prefixWord ++ tailWord_4611465).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4611465).length < 2 ^ (prefixWord ++ tailWord_4611465).sum := by decide
  have hdescent : baseEnd_4611465 < baseStart_4611465 := by decide
  rcases family_descends (prefixWord ++ tailWord_4611465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4611481 : List Nat := [1, 2, 1, 2, 1, 6, 1, 1, 3, 3, 2]
def baseStart_4611481 : Nat := 118140960795 + 4611481 * 2 ^ 59
def prefixEnd_4611481 : Nat := 4983230072969 + 3 ^ 40 * 4611481 * 2
def baseEnd_4611481 : Nat := 2367906282076377293079691

theorem tailTrace_4611481 : CollatzResearch.WordTrace tailWord_4611481 prefixEnd_4611481 2367906282076377293079691 := by
  unfold tailWord_4611481
  simp only [CollatzResearch.WordTrace]
  refine ⟨168194529806399390097602297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112129686537599593398401531 168194529806399390097602297)
  ·
    refine ⟨126145897354799542573201723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 168194529806399390097602297 126145897354799542573201723)
    ·
      refine ⟨189218846032199313859802585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 126145897354799542573201723 189218846032199313859802585)
      ·
        refine ⟨141914134524149485394851939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 189218846032199313859802585 141914134524149485394851939)
        ·
          refine ⟨212871201786224228092277909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 141914134524149485394851939 212871201786224228092277909)
          ·
            refine ⟨9978337583729260691825527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 212871201786224228092277909 9978337583729260691825527)
            ·
              refine ⟨14967506375593891037738291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9978337583729260691825527 14967506375593891037738291)
              ·
                refine ⟨22451259563390836556607437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14967506375593891037738291 22451259563390836556607437)
                ·
                  refine ⟨8419222336271563708727789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22451259563390836556607437 8419222336271563708727789)
                  ·
                    refine ⟨3157208376101836390772921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8419222336271563708727789 3157208376101836390772921)
                    ·
                      refine ⟨2367906282076377293079691, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3157208376101836390772921 2367906282076377293079691)
                      ·
                        rfl

theorem cell23_4611481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 6, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 6, 1, 1, 3, 3, 2].length) (baseStart_4611481 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4611481 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4611481 prefixEnd_4611481 := by exact prefixLift 4611481
  have htrace : WordTrace (prefixWord ++ tailWord_4611481) baseStart_4611481 baseEnd_4611481 := by
    simpa [prefixWord, tailWord_4611481, baseEnd_4611481] using wordTrace_append hprefix tailTrace_4611481
  have hstable : (prefixWord ++ tailWord_4611481).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4611481).length < 2 ^ (prefixWord ++ tailWord_4611481).sum := by decide
  have hdescent : baseEnd_4611481 < baseStart_4611481 := by decide
  rcases family_descends (prefixWord ++ tailWord_4611481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4611507 : List Nat := [1, 1, 1, 2, 3, 1, 1, 2, 3, 4, 4]
def baseStart_4611507 : Nat := 118140960795 + 4611507 * 2 ^ 59
def prefixEnd_4611507 : Nat := 4983230072969 + 3 ^ 40 * 4611507 * 2
def baseEnd_4611507 : Nat := 2367919632573394191354571

theorem tailTrace_4611507 : CollatzResearch.WordTrace tailWord_4611507 prefixEnd_4611507 2367919632573394191354571 := by
  unfold tailWord_4611507
  simp only [CollatzResearch.WordTrace]
  refine ⟨168195478104305196538048775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112130318736203464358699183 168195478104305196538048775)
  ·
    refine ⟨252293217156457794807073163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 168195478104305196538048775 252293217156457794807073163)
    ·
      refine ⟨378439825734686692210609745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 252293217156457794807073163 378439825734686692210609745)
      ·
        refine ⟨283829869301015019157957309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 378439825734686692210609745 283829869301015019157957309)
        ·
          refine ⟨106436200987880632184233991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 283829869301015019157957309 106436200987880632184233991)
          ·
            refine ⟨159654301481820948276350987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 106436200987880632184233991 159654301481820948276350987)
            ·
              refine ⟨239481452222731422414526481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 159654301481820948276350987 239481452222731422414526481)
              ·
                refine ⟨179611089167048566810894861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 239481452222731422414526481 179611089167048566810894861)
                ·
                  refine ⟨67354158437643212554085573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 179611089167048566810894861 67354158437643212554085573)
                  ·
                    refine ⟨12628904707058102353891045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 67354158437643212554085573 12628904707058102353891045)
                    ·
                      refine ⟨2367919632573394191354571, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12628904707058102353891045 2367919632573394191354571)
                      ·
                        rfl

theorem cell23_4611507_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 2, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 2, 3, 4, 4].length) (baseStart_4611507 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4611507 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4611507 prefixEnd_4611507 := by exact prefixLift 4611507
  have htrace : WordTrace (prefixWord ++ tailWord_4611507) baseStart_4611507 baseEnd_4611507 := by
    simpa [prefixWord, tailWord_4611507, baseEnd_4611507] using wordTrace_append hprefix tailTrace_4611507
  have hstable : (prefixWord ++ tailWord_4611507).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4611507).length < 2 ^ (prefixWord ++ tailWord_4611507).sum := by decide
  have hdescent : baseEnd_4611507 < baseStart_4611507 := by decide
  rcases family_descends (prefixWord ++ tailWord_4611507) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4611528 : List Nat := [2, 1, 3, 1, 3, 1, 1, 5, 2, 2, 2]
def baseStart_4611528 : Nat := 118140960795 + 4611528 * 2 ^ 59
def prefixEnd_4611528 : Nat := 4983230072969 + 3 ^ 40 * 4611528 * 2
def baseEnd_4611528 : Nat := 2367930415667138609191975

theorem tailTrace_4611528 : CollatzResearch.WordTrace tailWord_4611528 prefixEnd_4611528 2367930415667138609191975 := by
  unfold tailWord_4611528
  simp only [CollatzResearch.WordTrace]
  refine ⟨84098122018614558562281619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 112130829358152744749708825 84098122018614558562281619)
  ·
    refine ⟨126147183027921837843422429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84098122018614558562281619 126147183027921837843422429)
    ·
      refine ⟨47305193635470689191283411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 126147183027921837843422429 47305193635470689191283411)
      ·
        refine ⟨70957790453206033786925117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47305193635470689191283411 70957790453206033786925117)
        ·
          refine ⟨26609171419952262670096919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 70957790453206033786925117 26609171419952262670096919)
          ·
            refine ⟨39913757129928394005145379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26609171419952262670096919 39913757129928394005145379)
            ·
              refine ⟨59870635694892591007718069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39913757129928394005145379 59870635694892591007718069)
              ·
                refine ⟨5612872096396180406973569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 59870635694892591007718069 5612872096396180406973569)
                ·
                  refine ⟨4209654072297135305230177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5612872096396180406973569 4209654072297135305230177)
                  ·
                    refine ⟨3157240554222851478922633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4209654072297135305230177 3157240554222851478922633)
                    ·
                      refine ⟨2367930415667138609191975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3157240554222851478922633 2367930415667138609191975)
                      ·
                        rfl

theorem cell23_4611528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 1, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 1, 5, 2, 2, 2].length) (baseStart_4611528 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4611528 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4611528 prefixEnd_4611528 := by exact prefixLift 4611528
  have htrace : WordTrace (prefixWord ++ tailWord_4611528) baseStart_4611528 baseEnd_4611528 := by
    simpa [prefixWord, tailWord_4611528, baseEnd_4611528] using wordTrace_append hprefix tailTrace_4611528
  have hstable : (prefixWord ++ tailWord_4611528).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4611528).length < 2 ^ (prefixWord ++ tailWord_4611528).sum := by decide
  have hdescent : baseEnd_4611528 < baseStart_4611528 := by decide
  rcases family_descends (prefixWord ++ tailWord_4611528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4611551 : List Nat := [1, 1, 2, 3, 3, 1, 4, 3, 5]
def baseStart_4611551 : Nat := 118140960795 + 4611551 * 2 ^ 59
def prefixEnd_4611551 : Nat := 4983230072969 + 3 ^ 40 * 4611551 * 2
def baseEnd_4611551 : Nat := 263104691746910224356041

theorem tailTrace_4611551 : CollatzResearch.WordTrace tailWord_4611551 prefixEnd_4611551 263104691746910224356041 := by
  unfold tailWord_4611551
  simp only [CollatzResearch.WordTrace]
  refine ⟨168197082916145792052650507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112131388610763861368433671 168197082916145792052650507)
  ·
    refine ⟨252295624374218688078975761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 168197082916145792052650507 252295624374218688078975761)
    ·
      refine ⟨189221718280664016059231821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 252295624374218688078975761 189221718280664016059231821)
      ·
        refine ⟨70958144355249006022211933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 189221718280664016059231821 70958144355249006022211933)
        ·
          refine ⟨26609304133218377258329475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 70958144355249006022211933 26609304133218377258329475)
          ·
            refine ⟨39913956199827565887494213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26609304133218377258329475 39913956199827565887494213)
            ·
              refine ⟨7483866787467668603905165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 39913956199827565887494213 7483866787467668603905165)
              ·
                refine ⟨2806450045300375726464437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7483866787467668603905165 2806450045300375726464437)
                ·
                  refine ⟨263104691746910224356041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2806450045300375726464437 263104691746910224356041)
                  ·
                    rfl

theorem cell23_4611551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 4, 3, 5].length) (baseStart_4611551 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4611551 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4611551 prefixEnd_4611551 := by exact prefixLift 4611551
  have htrace : WordTrace (prefixWord ++ tailWord_4611551) baseStart_4611551 baseEnd_4611551 := by
    simpa [prefixWord, tailWord_4611551, baseEnd_4611551] using wordTrace_append hprefix tailTrace_4611551
  have hstable : (prefixWord ++ tailWord_4611551).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4611551).length < 2 ^ (prefixWord ++ tailWord_4611551).sum := by decide
  have hdescent : baseEnd_4611551 < baseStart_4611551 := by decide
  rcases family_descends (prefixWord ++ tailWord_4611551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4611562 : List Nat := [3, 1, 3, 1, 4, 2, 1, 2, 2, 2, 2]
def baseStart_4611562 : Nat := 118140960795 + 4611562 * 2 ^ 59
def prefixEnd_4611562 : Nat := 4983230072969 + 3 ^ 40 * 4611562 * 2
def baseEnd_4611562 : Nat := 2367947874009391476166819

theorem tailTrace_4611562 : CollatzResearch.WordTrace tailWord_4611562 prefixEnd_4611562 2367947874009391476166819 := by
  unfold tailWord_4611562
  simp only [CollatzResearch.WordTrace]
  refine ⟨42049371029776485232825235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 112131656079403960620867293 42049371029776485232825235)
  ·
    refine ⟨63074056544664727849237853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42049371029776485232825235 63074056544664727849237853)
    ·
      refine ⟨23652771204249272943464195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 63074056544664727849237853 23652771204249272943464195)
      ·
        refine ⟨35479156806373909415196293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23652771204249272943464195 35479156806373909415196293)
        ·
          refine ⟨6652341901195108015349305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 35479156806373909415196293 6652341901195108015349305)
          ·
            refine ⟨4989256425896331011511979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6652341901195108015349305 4989256425896331011511979)
            ·
              refine ⟨7483884638844496517267969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4989256425896331011511979 7483884638844496517267969)
              ·
                refine ⟨5612913479133372387950977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7483884638844496517267969 5612913479133372387950977)
                ·
                  refine ⟨4209685109350029290963233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5612913479133372387950977 4209685109350029290963233)
                  ·
                    refine ⟨3157263832012521968222425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4209685109350029290963233 3157263832012521968222425)
                    ·
                      refine ⟨2367947874009391476166819, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3157263832012521968222425 2367947874009391476166819)
                      ·
                        rfl

theorem cell23_4611562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 4, 2, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 4, 2, 1, 2, 2, 2, 2].length) (baseStart_4611562 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4611562 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4611562 prefixEnd_4611562 := by exact prefixLift 4611562
  have htrace : WordTrace (prefixWord ++ tailWord_4611562) baseStart_4611562 baseEnd_4611562 := by
    simpa [prefixWord, tailWord_4611562, baseEnd_4611562] using wordTrace_append hprefix tailTrace_4611562
  have hstable : (prefixWord ++ tailWord_4611562).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4611562).length < 2 ^ (prefixWord ++ tailWord_4611562).sum := by decide
  have hdescent : baseEnd_4611562 < baseStart_4611562 := by decide
  rcases family_descends (prefixWord ++ tailWord_4611562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4611641 : List Nat := [1, 2, 1, 5, 1, 3, 1, 3, 6]
def baseStart_4611641 : Nat := 118140960795 + 4611641 * 2 ^ 59
def prefixEnd_4611641 : Nat := 4983230072969 + 3 ^ 40 * 4611641 * 2
def baseEnd_4611641 : Nat := 263109826553455185230995

theorem tailTrace_4611641 : CollatzResearch.WordTrace tailWord_4611641 prefixEnd_4611641 263109826553455185230995 := by
  unfold tailWord_4611641
  simp only [CollatzResearch.WordTrace]
  refine ⟨168200365485819737423426777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112133576990546491615617851 168200365485819737423426777)
  ·
    refine ⟨126150274114364803067570083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 168200365485819737423426777 126150274114364803067570083)
    ·
      refine ⟨189225411171547204601355125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 126150274114364803067570083 189225411171547204601355125)
      ·
        refine ⟨17739882297332550431377043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 189225411171547204601355125 17739882297332550431377043)
        ·
          refine ⟨26609823445998825647065565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17739882297332550431377043 26609823445998825647065565)
          ·
            refine ⟨9978683792249559617649587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26609823445998825647065565 9978683792249559617649587)
            ·
              refine ⟨14968025688374339426474381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9978683792249559617649587 14968025688374339426474381)
              ·
                refine ⟨5613009633140377284927893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14968025688374339426474381 5613009633140377284927893)
                ·
                  refine ⟨263109826553455185230995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5613009633140377284927893 263109826553455185230995)
                  ·
                    rfl

theorem cell23_4611641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 3, 1, 3, 6].length) (baseStart_4611641 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4611641 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4611641 prefixEnd_4611641 := by exact prefixLift 4611641
  have htrace : WordTrace (prefixWord ++ tailWord_4611641) baseStart_4611641 baseEnd_4611641 := by
    simpa [prefixWord, tailWord_4611641, baseEnd_4611641] using wordTrace_append hprefix tailTrace_4611641
  have hstable : (prefixWord ++ tailWord_4611641).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4611641).length < 2 ^ (prefixWord ++ tailWord_4611641).sum := by decide
  have hdescent : baseEnd_4611641 < baseStart_4611641 := by decide
  rcases family_descends (prefixWord ++ tailWord_4611641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4611721 : List Nat := [1, 2, 1, 1, 4, 1, 4, 2, 1, 2, 4]
def baseStart_4611721 : Nat := 118140960795 + 4611721 * 2 ^ 59
def prefixEnd_4611721 : Nat := 4983230072969 + 3 ^ 40 * 4611721 * 2
def baseEnd_4611721 : Nat := 2368029517433456354078587

theorem tailTrace_4611721 : CollatzResearch.WordTrace tailWord_4611721 prefixEnd_4611721 2368029517433456354078587 := by
  unfold tailWord_4611721
  simp only [CollatzResearch.WordTrace]
  refine ⟨168203283325529911086339017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112135522217019940724226011 168203283325529911086339017)
  ·
    refine ⟨126152462494147433314754263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 168203283325529911086339017 126152462494147433314754263)
    ·
      refine ⟨189228693741221149972131395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 126152462494147433314754263 189228693741221149972131395)
      ·
        refine ⟨283843040611831724958197093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 189228693741221149972131395 283843040611831724958197093)
        ·
          refine ⟨53220570114718448429661955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 283843040611831724958197093 53220570114718448429661955)
          ·
            refine ⟨79830855172077672644492933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53220570114718448429661955 79830855172077672644492933)
            ·
              refine ⟨14968285344764563620842425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 79830855172077672644492933 14968285344764563620842425)
              ·
                refine ⟨11226214008573422715631819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14968285344764563620842425 11226214008573422715631819)
                ·
                  refine ⟨16839321012860134073447729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11226214008573422715631819 16839321012860134073447729)
                  ·
                    refine ⟨12629490759645100555085797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16839321012860134073447729 12629490759645100555085797)
                    ·
                      refine ⟨2368029517433456354078587, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12629490759645100555085797 2368029517433456354078587)
                      ·
                        rfl

theorem cell23_4611721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 4, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 4, 2, 1, 2, 4].length) (baseStart_4611721 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4611721 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4611721 prefixEnd_4611721 := by exact prefixLift 4611721
  have htrace : WordTrace (prefixWord ++ tailWord_4611721) baseStart_4611721 baseEnd_4611721 := by
    simpa [prefixWord, tailWord_4611721, baseEnd_4611721] using wordTrace_append hprefix tailTrace_4611721
  have hstable : (prefixWord ++ tailWord_4611721).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4611721).length < 2 ^ (prefixWord ++ tailWord_4611721).sum := by decide
  have hdescent : baseEnd_4611721 < baseStart_4611721 := by decide
  rcases family_descends (prefixWord ++ tailWord_4611721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4611735 : List Nat := [1, 1, 3, 3, 2, 4, 1, 2, 2, 4]
def baseStart_4611735 : Nat := 118140960795 + 4611735 * 2 ^ 59
def prefixEnd_4611735 : Nat := 4983230072969 + 3 ^ 40 * 4611735 * 2
def baseEnd_4611735 : Nat := 789345568720873099767841

theorem tailTrace_4611735 : CollatzResearch.WordTrace tailWord_4611735 prefixEnd_4611735 789345568720873099767841 := by
  unfold tailWord_4611735
  simp only [CollatzResearch.WordTrace]
  refine ⟨168203793947479191477348659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112135862631652794318232439 168203793947479191477348659)
  ·
    refine ⟨252305690921218787216022989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 168203793947479191477348659 252305690921218787216022989)
    ·
      refine ⟨94614634095457045206008621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 252305690921218787216022989 94614634095457045206008621)
      ·
        refine ⟨35480487785796391952253233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 94614634095457045206008621 35480487785796391952253233)
        ·
          refine ⟨26610365839347293964189925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35480487785796391952253233 26610365839347293964189925)
          ·
            refine ⟨4989443594877617618285611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 26610365839347293964189925 4989443594877617618285611)
            ·
              refine ⟨7484165392316426427428417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4989443594877617618285611 7484165392316426427428417)
              ·
                refine ⟨5613124044237319820571313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7484165392316426427428417 5613124044237319820571313)
                ·
                  refine ⟨4209843033177989865428485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5613124044237319820571313 4209843033177989865428485)
                  ·
                    refine ⟨789345568720873099767841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4209843033177989865428485 789345568720873099767841)
                    ·
                      rfl

theorem cell23_4611735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 4, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 4, 1, 2, 2, 4].length) (baseStart_4611735 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4611735 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4611735 prefixEnd_4611735 := by exact prefixLift 4611735
  have htrace : WordTrace (prefixWord ++ tailWord_4611735) baseStart_4611735 baseEnd_4611735 := by
    simpa [prefixWord, tailWord_4611735, baseEnd_4611735] using wordTrace_append hprefix tailTrace_4611735
  have hstable : (prefixWord ++ tailWord_4611735).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4611735).length < 2 ^ (prefixWord ++ tailWord_4611735).sum := by decide
  have hdescent : baseEnd_4611735 < baseStart_4611735 := by decide
  rcases family_descends (prefixWord ++ tailWord_4611735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4611742 : List Nat := [4, 3, 1, 1, 1, 2, 1, 3, 3, 2, 2]
def baseStart_4611742 : Nat := 118140960795 + 4611742 * 2 ^ 59
def prefixEnd_4611742 : Nat := 4983230072969 + 3 ^ 40 * 4611742 * 2
def baseEnd_4611742 : Nat := 2368040300527200771915991

theorem tailTrace_4611742 : CollatzResearch.WordTrace tailWord_4611742 prefixEnd_4611742 2368040300527200771915991 := by
  unfold tailWord_4611742
  simp only [CollatzResearch.WordTrace]
  refine ⟨21025506157306728959106685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 112136032838969221115235653 21025506157306728959106685)
  ·
    refine ⟨7884564808990023359665007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21025506157306728959106685 7884564808990023359665007)
    ·
      refine ⟨11826847213485035039497511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7884564808990023359665007 11826847213485035039497511)
      ·
        refine ⟨17740270820227552559246267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11826847213485035039497511 17740270820227552559246267)
        ·
          refine ⟨26610406230341328838869401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17740270820227552559246267 26610406230341328838869401)
          ·
            refine ⟨19957804672755996629152051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26610406230341328838869401 19957804672755996629152051)
            ·
              refine ⟨29936707009133994943728077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19957804672755996629152051 29936707009133994943728077)
              ·
                refine ⟨11226265128425248103898029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 29936707009133994943728077 11226265128425248103898029)
                ·
                  refine ⟨4209849423159468038961761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11226265128425248103898029 4209849423159468038961761)
                  ·
                    refine ⟨3157387067369601029221321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4209849423159468038961761 3157387067369601029221321)
                    ·
                      refine ⟨2368040300527200771915991, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3157387067369601029221321 2368040300527200771915991)
                      ·
                        rfl

theorem cell23_4611742_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 1, 3, 3, 2, 2].length) (baseStart_4611742 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4611742 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4611742 prefixEnd_4611742 := by exact prefixLift 4611742
  have htrace : WordTrace (prefixWord ++ tailWord_4611742) baseStart_4611742 baseEnd_4611742 := by
    simpa [prefixWord, tailWord_4611742, baseEnd_4611742] using wordTrace_append hprefix tailTrace_4611742
  have hstable : (prefixWord ++ tailWord_4611742).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4611742).length < 2 ^ (prefixWord ++ tailWord_4611742).sum := by decide
  have hdescent : baseEnd_4611742 < baseStart_4611742 := by decide
  rcases family_descends (prefixWord ++ tailWord_4611742) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4611765 : List Nat := [1, 3, 3, 3, 2, 2, 2, 7]
def baseStart_4611765 : Nat := 118140960795 + 4611765 * 2 ^ 59
def prefixEnd_4611765 : Nat := 4983230072969 + 3 ^ 40 * 4611765 * 2
def baseEnd_4611765 : Nat := 87705633725268673404755

theorem tailTrace_4611765 : CollatzResearch.WordTrace tailWord_4611765 prefixEnd_4611765 87705633725268673404755 := by
  unfold tailWord_4611765
  simp only [CollatzResearch.WordTrace]
  refine ⟨168204888137370506600940749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112136592091580337733960499 168204888137370506600940749)
  ·
    refine ⟨63076833051513939975352781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 168204888137370506600940749 63076833051513939975352781)
    ·
      refine ⟨23653812394317727490757293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 63076833051513939975352781 23653812394317727490757293)
      ·
        refine ⟨8870179647869147809033985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23653812394317727490757293 8870179647869147809033985)
        ·
          refine ⟨6652634735901860856775489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8870179647869147809033985 6652634735901860856775489)
          ·
            refine ⟨4989476051926395642581617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6652634735901860856775489 4989476051926395642581617)
            ·
              refine ⟨3742107038944796731936213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4989476051926395642581617 3742107038944796731936213)
              ·
                refine ⟨87705633725268673404755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3742107038944796731936213 87705633725268673404755)
                ·
                  rfl

theorem cell23_4611765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 2, 2, 2, 7].length) (baseStart_4611765 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4611765 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4611765 prefixEnd_4611765 := by exact prefixLift 4611765
  have htrace : WordTrace (prefixWord ++ tailWord_4611765) baseStart_4611765 baseEnd_4611765 := by
    simpa [prefixWord, tailWord_4611765, baseEnd_4611765] using wordTrace_append hprefix tailTrace_4611765
  have hstable : (prefixWord ++ tailWord_4611765).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4611765).length < 2 ^ (prefixWord ++ tailWord_4611765).sum := by decide
  have hdescent : baseEnd_4611765 < baseStart_4611765 := by decide
  rcases family_descends (prefixWord ++ tailWord_4611765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4611768 : List Nat := [2, 1, 2, 1, 2, 1, 1, 5, 3, 3, 2]
def baseStart_4611768 : Nat := 118140960795 + 4611768 * 2 ^ 59
def prefixEnd_4611768 : Nat := 4983230072969 + 3 ^ 40 * 4611768 * 2
def baseEnd_4611768 : Nat := 2368053651024217670190871

theorem tailTrace_4611768 : CollatzResearch.WordTrace tailWord_4611768 prefixEnd_4611768 2368053651024217670190871 := by
  unfold tailWord_4611768
  simp only [CollatzResearch.WordTrace]
  refine ⟨84102498778179819056649979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 112136665037573092075533305 84102498778179819056649979)
  ·
    refine ⟨126153748167269728584974969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84102498778179819056649979 126153748167269728584974969)
    ·
      refine ⟨94615311125452296438731227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 126153748167269728584974969 94615311125452296438731227)
      ·
        refine ⟨141922966688178444658096841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 94615311125452296438731227 141922966688178444658096841)
        ·
          refine ⟨106442225016133833493572631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 141922966688178444658096841 106442225016133833493572631)
          ·
            refine ⟨159663337524200750240358947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 106442225016133833493572631 159663337524200750240358947)
            ·
              refine ⟨239495006286301125360538421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 159663337524200750240358947 239495006286301125360538421)
              ·
                refine ⟨22452656839340730502550477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 239495006286301125360538421 22452656839340730502550477)
                ·
                  refine ⟨8419746314752773938456429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22452656839340730502550477 8419746314752773938456429)
                  ·
                    refine ⟨3157404868032290226921161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8419746314752773938456429 3157404868032290226921161)
                    ·
                      refine ⟨2368053651024217670190871, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3157404868032290226921161 2368053651024217670190871)
                      ·
                        rfl

theorem cell23_4611768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 5, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 5, 3, 3, 2].length) (baseStart_4611768 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4611768 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4611768 prefixEnd_4611768 := by exact prefixLift 4611768
  have htrace : WordTrace (prefixWord ++ tailWord_4611768) baseStart_4611768 baseEnd_4611768 := by
    simpa [prefixWord, tailWord_4611768, baseEnd_4611768] using wordTrace_append hprefix tailTrace_4611768
  have hstable : (prefixWord ++ tailWord_4611768).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4611768).length < 2 ^ (prefixWord ++ tailWord_4611768).sum := by decide
  have hdescent : baseEnd_4611768 < baseStart_4611768 := by decide
  rcases family_descends (prefixWord ++ tailWord_4611768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4611809 : List Nat := [1, 2, 3, 1, 5, 2, 2, 1, 2, 1, 3]
def baseStart_4611809 : Nat := 118140960795 + 4611809 * 2 ^ 59
def prefixEnd_4611809 : Nat := 4983230072969 + 3 ^ 40 * 4611809 * 2
def baseEnd_4611809 : Nat := 2368074703731052009778183

theorem tailTrace_4611809 : CollatzResearch.WordTrace tailWord_4611809 prefixEnd_4611809 2368074703731052009778183 := by
  unfold tailWord_4611809
  simp only [CollatzResearch.WordTrace]
  refine ⟨168206492949211102115542481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112137661966140734743694987 168206492949211102115542481)
  ·
    refine ⟨126154869711908326586656861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 168206492949211102115542481 126154869711908326586656861)
    ·
      refine ⟨47308076141965622469996323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 126154869711908326586656861 47308076141965622469996323)
      ·
        refine ⟨70962114212948433704994485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47308076141965622469996323 70962114212948433704994485)
        ·
          refine ⟨6652698207463915659843233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 70962114212948433704994485 6652698207463915659843233)
          ·
            refine ⟨4989523655597936744882425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6652698207463915659843233 4989523655597936744882425)
            ·
              refine ⟨3742142741698452558661819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4989523655597936744882425 3742142741698452558661819)
              ·
                refine ⟨5613214112547678837992729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3742142741698452558661819 5613214112547678837992729)
                ·
                  refine ⟨4209910584410759128494547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5613214112547678837992729 4209910584410759128494547)
                  ·
                    refine ⟨6314865876616138692741821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4209910584410759128494547 6314865876616138692741821)
                    ·
                      refine ⟨2368074703731052009778183, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6314865876616138692741821 2368074703731052009778183)
                      ·
                        rfl

theorem cell23_4611809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 5, 2, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 5, 2, 2, 1, 2, 1, 3].length) (baseStart_4611809 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4611809 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4611809 prefixEnd_4611809 := by exact prefixLift 4611809
  have htrace : WordTrace (prefixWord ++ tailWord_4611809) baseStart_4611809 baseEnd_4611809 := by
    simpa [prefixWord, tailWord_4611809, baseEnd_4611809] using wordTrace_append hprefix tailTrace_4611809
  have hstable : (prefixWord ++ tailWord_4611809).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4611809).length < 2 ^ (prefixWord ++ tailWord_4611809).sum := by decide
  have hdescent : baseEnd_4611809 < baseStart_4611809 := by decide
  rcases family_descends (prefixWord ++ tailWord_4611809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4611848 : List Nat := [2, 1, 3, 2, 2, 1, 2, 2, 2, 3, 3]
def baseStart_4611848 : Nat := 118140960795 + 4611848 * 2 ^ 59
def prefixEnd_4611848 : Nat := 4983230072969 + 3 ^ 40 * 4611848 * 2
def baseEnd_4611848 : Nat := 2368094729476577357190503

theorem tailTrace_4611848 : CollatzResearch.WordTrace tailWord_4611848 prefixEnd_4611848 2368094729476577357190503 := by
  unfold tailWord_4611848
  simp only [CollatzResearch.WordTrace]
  refine ⟨84103957698034905888106099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 112138610264046541184141465 84103957698034905888106099)
  ·
    refine ⟨126155936547052358832159149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84103957698034905888106099 126155936547052358832159149)
    ·
      refine ⟨47308476205144634562059681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 126155936547052358832159149 47308476205144634562059681)
      ·
        refine ⟨35481357153858475921544761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47308476205144634562059681 35481357153858475921544761)
        ·
          refine ⟨26611017865393856941158571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35481357153858475921544761 26611017865393856941158571)
          ·
            refine ⟨39916526798090785411737857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26611017865393856941158571 39916526798090785411737857)
            ·
              refine ⟨29937395098568089058803393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 39916526798090785411737857 29937395098568089058803393)
              ·
                refine ⟨22453046323926066794102545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29937395098568089058803393 22453046323926066794102545)
                ·
                  refine ⟨16839784742944550095576909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22453046323926066794102545 16839784742944550095576909)
                  ·
                    refine ⟨6314919278604206285841341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16839784742944550095576909 6314919278604206285841341)
                    ·
                      refine ⟨2368094729476577357190503, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6314919278604206285841341 2368094729476577357190503)
                      ·
                        rfl

theorem cell23_4611848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 2, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 2, 2, 2, 3, 3].length) (baseStart_4611848 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4611848 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4611848 prefixEnd_4611848 := by exact prefixLift 4611848
  have htrace : WordTrace (prefixWord ++ tailWord_4611848) baseStart_4611848 baseEnd_4611848 := by
    simpa [prefixWord, tailWord_4611848, baseEnd_4611848] using wordTrace_append hprefix tailTrace_4611848
  have hstable : (prefixWord ++ tailWord_4611848).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4611848).length < 2 ^ (prefixWord ++ tailWord_4611848).sum := by decide
  have hdescent : baseEnd_4611848 < baseStart_4611848 := by decide
  rcases family_descends (prefixWord ++ tailWord_4611848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4611972 : List Nat := [2, 3, 2, 1, 1, 1, 5, 1, 3, 1, 3]
def baseStart_4611972 : Nat := 118140960795 + 4611972 * 2 ^ 59
def prefixEnd_4611972 : Nat := 4983230072969 + 3 ^ 40 * 4611972 * 2
def baseEnd_4611972 : Nat := 2368158401077734872039933

theorem tailTrace_4611972 : CollatzResearch.WordTrace tailWord_4611972 prefixEnd_4611972 2368158401077734872039933 := by
  unfold tailWord_4611972
  simp only [CollatzResearch.WordTrace]
  refine ⟨84106219023810290476863085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 112141625365080387302484113 84106219023810290476863085)
  ·
    refine ⟨31539832133928858928823657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 84106219023810290476863085 31539832133928858928823657)
    ·
      refine ⟨23654874100446644196617743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31539832133928858928823657 23654874100446644196617743)
      ·
        refine ⟨35482311150669966294926615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23654874100446644196617743 35482311150669966294926615)
        ·
          refine ⟨53223466726004949442389923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35482311150669966294926615 53223466726004949442389923)
          ·
            refine ⟨79835200089007424163584885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53223466726004949442389923 79835200089007424163584885)
            ·
              refine ⟨7484550008344446015336083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 79835200089007424163584885 7484550008344446015336083)
              ·
                refine ⟨11226825012516669023004125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7484550008344446015336083 11226825012516669023004125)
                ·
                  refine ⟨4210059379693750883626547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11226825012516669023004125 4210059379693750883626547)
                  ·
                    refine ⟨6315089069540626325439821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4210059379693750883626547 6315089069540626325439821)
                    ·
                      refine ⟨2368158401077734872039933, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6315089069540626325439821 2368158401077734872039933)
                      ·
                        rfl

theorem cell23_4611972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 5, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 5, 1, 3, 1, 3].length) (baseStart_4611972 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4611972 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4611972 prefixEnd_4611972 := by exact prefixLift 4611972
  have htrace : WordTrace (prefixWord ++ tailWord_4611972) baseStart_4611972 baseEnd_4611972 := by
    simpa [prefixWord, tailWord_4611972, baseEnd_4611972] using wordTrace_append hprefix tailTrace_4611972
  have hstable : (prefixWord ++ tailWord_4611972).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4611972).length < 2 ^ (prefixWord ++ tailWord_4611972).sum := by decide
  have hdescent : baseEnd_4611972 < baseStart_4611972 := by decide
  rcases family_descends (prefixWord ++ tailWord_4611972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4611992 : List Nat := [2, 1, 2, 6, 1, 1, 1, 1, 3, 5]
def baseStart_4611992 : Nat := 118140960795 + 4611992 * 2 ^ 59
def prefixEnd_4611992 : Nat := 4983230072969 + 3 ^ 40 * 4611992 * 2
def baseEnd_4611992 : Nat := 789389556896941597929947

theorem tailTrace_4611992 : CollatzResearch.WordTrace tailWord_4611992 prefixEnd_4611992 789389556896941597929947 := by
  unfold tailWord_4611992
  simp only [CollatzResearch.WordTrace]
  refine ⟨84106583753774062184727115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 112142111671698749579636153 84106583753774062184727115)
  ·
    refine ⟨126159875630661093277090673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84106583753774062184727115 126159875630661093277090673)
    ·
      refine ⟨94619906722995819957818005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 126159875630661093277090673 94619906722995819957818005)
      ·
        refine ⟨4435308127640429060522719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 94619906722995819957818005 4435308127640429060522719)
        ·
          refine ⟨6652962191460643590784079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4435308127640429060522719 6652962191460643590784079)
          ·
            refine ⟨9979443287190965386176119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6652962191460643590784079 9979443287190965386176119)
            ·
              refine ⟨14969164930786448079264179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9979443287190965386176119 14969164930786448079264179)
              ·
                refine ⟨22453747396179672118896269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14969164930786448079264179 22453747396179672118896269)
                ·
                  refine ⟨8420155273567377044586101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22453747396179672118896269 8420155273567377044586101)
                  ·
                    refine ⟨789389556896941597929947, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8420155273567377044586101 789389556896941597929947)
                    ·
                      rfl

theorem cell23_4611992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 1, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 1, 1, 1, 1, 3, 5].length) (baseStart_4611992 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4611992 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4611992 prefixEnd_4611992 := by exact prefixLift 4611992
  have htrace : WordTrace (prefixWord ++ tailWord_4611992) baseStart_4611992 baseEnd_4611992 := by
    simpa [prefixWord, tailWord_4611992, baseEnd_4611992] using wordTrace_append hprefix tailTrace_4611992
  have hstable : (prefixWord ++ tailWord_4611992).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4611992).length < 2 ^ (prefixWord ++ tailWord_4611992).sum := by decide
  have hdescent : baseEnd_4611992 < baseStart_4611992 := by decide
  rcases family_descends (prefixWord ++ tailWord_4611992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4611999 : List Nat := [1, 1, 2, 5, 3, 1, 2, 1, 2, 3, 2]
def baseStart_4611999 : Nat := 118140960795 + 4611999 * 2 ^ 59
def prefixEnd_4611999 : Nat := 4983230072969 + 3 ^ 40 * 4611999 * 2
def baseEnd_4611999 : Nat := 2368172265055406266402309

theorem tailTrace_4611999 : CollatzResearch.WordTrace tailWord_4611999 prefixEnd_4611999 2368172265055406266402309 := by
  unfold tailWord_4611999
  simp only [CollatzResearch.WordTrace]
  refine ⟨168213422818522764564959051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112142281879015176376639367 168213422818522764564959051)
  ·
    refine ⟨252320134227784146847438577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 168213422818522764564959051 252320134227784146847438577)
    ·
      refine ⟨189240100670838110135578933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 252320134227784146847438577 189240100670838110135578933)
      ·
        refine ⟨17741259437891072825210525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 189240100670838110135578933 17741259437891072825210525)
        ·
          refine ⟨6652972289209152309453947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17741259437891072825210525 6652972289209152309453947)
          ·
            refine ⟨9979458433813728464180921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6652972289209152309453947 9979458433813728464180921)
            ·
              refine ⟨7484593825360296348135691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9979458433813728464180921 7484593825360296348135691)
              ·
                refine ⟨11226890738040444522203537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7484593825360296348135691 11226890738040444522203537)
                ·
                  refine ⟨8420168053530333391652653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11226890738040444522203537 8420168053530333391652653)
                  ·
                    refine ⟨3157563020073875021869745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8420168053530333391652653 3157563020073875021869745)
                    ·
                      refine ⟨2368172265055406266402309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3157563020073875021869745 2368172265055406266402309)
                      ·
                        rfl

theorem cell23_4611999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 3, 1, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 3, 1, 2, 1, 2, 3, 2].length) (baseStart_4611999 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4611999 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4611999 prefixEnd_4611999 := by exact prefixLift 4611999
  have htrace : WordTrace (prefixWord ++ tailWord_4611999) baseStart_4611999 baseEnd_4611999 := by
    simpa [prefixWord, tailWord_4611999, baseEnd_4611999] using wordTrace_append hprefix tailTrace_4611999
  have hstable : (prefixWord ++ tailWord_4611999).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4611999).length < 2 ^ (prefixWord ++ tailWord_4611999).sum := by decide
  have hdescent : baseEnd_4611999 < baseStart_4611999 := by decide
  rcases family_descends (prefixWord ++ tailWord_4611999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4612060 : List Nat := [2, 2, 6, 1, 2, 1, 2, 1, 1, 5]
def baseStart_4612060 : Nat := 118140960795 + 4612060 * 2 ^ 59
def prefixEnd_4612060 : Nat := 4983230072969 + 3 ^ 40 * 4612060 * 2
def baseEnd_4612060 : Nat := 789401195791776842579843

theorem tailTrace_4612060 : CollatzResearch.WordTrace tailWord_4612060 prefixEnd_4612060 789401195791776842579843 := by
  unfold tailWord_4612060
  simp only [CollatzResearch.WordTrace]
  refine ⟨84107823835650885991464817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 112143765114201181321953089 84107823835650885991464817)
  ·
    refine ⟨63080867876738164493598613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 84107823835650885991464817 63080867876738164493598613)
    ·
      refine ⟨2956915681722101460637435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 63080867876738164493598613 2956915681722101460637435)
      ·
        refine ⟨4435373522583152190956153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2956915681722101460637435 4435373522583152190956153)
        ·
          refine ⟨3326530141937364143217115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4435373522583152190956153 3326530141937364143217115)
          ·
            refine ⟨4989795212906046214825673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3326530141937364143217115 4989795212906046214825673)
            ·
              refine ⟨3742346409679534661119255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4989795212906046214825673 3742346409679534661119255)
              ·
                refine ⟨5613519614519301991678883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3742346409679534661119255 5613519614519301991678883)
                ·
                  refine ⟨8420279421778952987518325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5613519614519301991678883 8420279421778952987518325)
                  ·
                    refine ⟨789401195791776842579843, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8420279421778952987518325 789401195791776842579843)
                    ·
                      rfl

theorem cell23_4612060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 2, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 2, 1, 2, 1, 1, 5].length) (baseStart_4612060 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4612060 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4612060 prefixEnd_4612060 := by exact prefixLift 4612060
  have htrace : WordTrace (prefixWord ++ tailWord_4612060) baseStart_4612060 baseEnd_4612060 := by
    simpa [prefixWord, tailWord_4612060, baseEnd_4612060] using wordTrace_append hprefix tailTrace_4612060
  have hstable : (prefixWord ++ tailWord_4612060).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4612060).length < 2 ^ (prefixWord ++ tailWord_4612060).sum := by decide
  have hdescent : baseEnd_4612060 < baseStart_4612060 := by decide
  rcases family_descends (prefixWord ++ tailWord_4612060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4612066 : List Nat := [3, 3, 3, 1, 2, 1, 1, 3, 1, 2, 3]
def baseStart_4612066 : Nat := 118140960795 + 4612066 * 2 ^ 59
def prefixEnd_4612066 : Nat := 4983230072969 + 3 ^ 40 * 4612066 * 2
def baseEnd_4612066 : Nat := 2368206668259257504264501

theorem tailTrace_4612066 : CollatzResearch.WordTrace tailWord_4612066 prefixEnd_4612066 2368206668259257504264501 := by
  unfold tailWord_4612066
  simp only [CollatzResearch.WordTrace]
  refine ⟨42053966627320008751912013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 112143911006186690005098701 42053966627320008751912013)
  ·
    refine ⟨15770237485245003281967005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 42053966627320008751912013 15770237485245003281967005)
    ·
      refine ⟨5913839056966876230737627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15770237485245003281967005 5913839056966876230737627)
      ·
        refine ⟨8870758585450314346106441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5913839056966876230737627 8870758585450314346106441)
        ·
          refine ⟨6653068939087735759579831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8870758585450314346106441 6653068939087735759579831)
          ·
            refine ⟨9979603408631603639369747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6653068939087735759579831 9979603408631603639369747)
            ·
              refine ⟨14969405112947405459054621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9979603408631603639369747 14969405112947405459054621)
              ·
                refine ⟨5613526917355277047145483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14969405112947405459054621 5613526917355277047145483)
                ·
                  refine ⟨8420290376032915570718225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5613526917355277047145483 8420290376032915570718225)
                  ·
                    refine ⟨6315217782024686678038669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8420290376032915570718225 6315217782024686678038669)
                    ·
                      refine ⟨2368206668259257504264501, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6315217782024686678038669 2368206668259257504264501)
                      ·
                        rfl

theorem cell23_4612066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 2, 1, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 2, 1, 1, 3, 1, 2, 3].length) (baseStart_4612066 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4612066 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4612066 prefixEnd_4612066 := by exact prefixLift 4612066
  have htrace : WordTrace (prefixWord ++ tailWord_4612066) baseStart_4612066 baseEnd_4612066 := by
    simpa [prefixWord, tailWord_4612066, baseEnd_4612066] using wordTrace_append hprefix tailTrace_4612066
  have hstable : (prefixWord ++ tailWord_4612066).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4612066).length < 2 ^ (prefixWord ++ tailWord_4612066).sum := by decide
  have hdescent : baseEnd_4612066 < baseStart_4612066 := by decide
  rcases family_descends (prefixWord ++ tailWord_4612066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4612106 : List Nat := [3, 1, 2, 2, 4, 1, 2, 2, 1, 3, 2]
def baseStart_4612106 : Nat := 118140960795 + 4612106 * 2 ^ 59
def prefixEnd_4612106 : Nat := 4983230072969 + 3 ^ 40 * 4612106 * 2
def baseEnd_4612106 : Nat := 2368227207485437347764317

theorem tailTrace_4612106 : CollatzResearch.WordTrace tailWord_4612106 prefixEnd_4612106 2368227207485437347764317 := by
  unfold tailWord_4612106
  simp only [CollatzResearch.WordTrace]
  refine ⟨42054331357283780459776043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 112144883619423414559402781 42054331357283780459776043)
  ·
    refine ⟨63081497035925670689664065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42054331357283780459776043 63081497035925670689664065)
    ·
      refine ⟨47311122776944253017248049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 63081497035925670689664065 47311122776944253017248049)
      ·
        refine ⟨35483342082708189762936037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47311122776944253017248049 35483342082708189762936037)
        ·
          refine ⟨6653126640507785580550507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 35483342082708189762936037 6653126640507785580550507)
          ·
            refine ⟨9979689960761678370825761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6653126640507785580550507 9979689960761678370825761)
            ·
              refine ⟨7484767470571258778119321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9979689960761678370825761 7484767470571258778119321)
              ·
                refine ⟨5613575602928444083589491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7484767470571258778119321 5613575602928444083589491)
                ·
                  refine ⟨8420363404392666125384237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5613575602928444083589491 8420363404392666125384237)
                  ·
                    refine ⟨3157636276647249797019089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8420363404392666125384237 3157636276647249797019089)
                    ·
                      refine ⟨2368227207485437347764317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3157636276647249797019089 2368227207485437347764317)
                      ·
                        rfl

theorem cell23_4612106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 4, 1, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 4, 1, 2, 2, 1, 3, 2].length) (baseStart_4612106 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4612106 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4612106 prefixEnd_4612106 := by exact prefixLift 4612106
  have htrace : WordTrace (prefixWord ++ tailWord_4612106) baseStart_4612106 baseEnd_4612106 := by
    simpa [prefixWord, tailWord_4612106, baseEnd_4612106] using wordTrace_append hprefix tailTrace_4612106
  have hstable : (prefixWord ++ tailWord_4612106).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4612106).length < 2 ^ (prefixWord ++ tailWord_4612106).sum := by decide
  have hdescent : baseEnd_4612106 < baseStart_4612106 := by decide
  rcases family_descends (prefixWord ++ tailWord_4612106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4612142 : List Nat := [4, 1, 3, 1, 1, 2, 3, 1, 7]
def baseStart_4612142 : Nat := 118140960795 + 4612142 * 2 ^ 59
def prefixEnd_4612142 : Nat := 4983230072969 + 3 ^ 40 * 4612142 * 2
def baseEnd_4612142 : Nat := 263138410309888800768239

theorem tailTrace_4612142 : CollatzResearch.WordTrace tailWord_4612142 prefixEnd_4612142 263138410309888800768239 := by
  unfold tailWord_4612142
  simp only [CollatzResearch.WordTrace]
  refine ⟨21027329807125587498426835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 112145758971336466658276453 21027329807125587498426835)
  ·
    refine ⟨31540994710688381247640253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21027329807125587498426835 31540994710688381247640253)
    ·
      refine ⟨11827873016508142967865095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31540994710688381247640253 11827873016508142967865095)
      ·
        refine ⟨17741809524762214451797643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11827873016508142967865095 17741809524762214451797643)
        ·
          refine ⟨26612714287143321677696465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17741809524762214451797643 26612714287143321677696465)
          ·
            refine ⟨19959535715357491258272349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26612714287143321677696465 19959535715357491258272349)
            ·
              refine ⟨7484825893259059221852131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19959535715357491258272349 7484825893259059221852131)
              ·
                refine ⟨11227238839888588832778197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7484825893259059221852131 11227238839888588832778197)
                ·
                  refine ⟨263138410309888800768239, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11227238839888588832778197 263138410309888800768239)
                  ·
                    rfl

theorem cell23_4612142_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 3, 1, 7].length) (baseStart_4612142 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4612142 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4612142 prefixEnd_4612142 := by exact prefixLift 4612142
  have htrace : WordTrace (prefixWord ++ tailWord_4612142) baseStart_4612142 baseEnd_4612142 := by
    simpa [prefixWord, tailWord_4612142, baseEnd_4612142] using wordTrace_append hprefix tailTrace_4612142
  have hstable : (prefixWord ++ tailWord_4612142).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4612142).length < 2 ^ (prefixWord ++ tailWord_4612142).sum := by decide
  have hdescent : baseEnd_4612142 < baseStart_4612142 := by decide
  rcases family_descends (prefixWord ++ tailWord_4612142) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4612175 : List Nat := [1, 1, 2, 1, 1, 2, 2, 2, 6, 1, 4]
def baseStart_4612175 : Nat := 118140960795 + 4612175 * 2 ^ 59
def prefixEnd_4612175 : Nat := 4983230072969 + 3 ^ 40 * 4612175 * 2
def baseEnd_4612175 : Nat := 2368262637650597577801499

theorem tailTrace_4612175 : CollatzResearch.WordTrace tailWord_4612175 prefixEnd_4612175 2368262637650597577801499 := by
  unfold tailWord_4612175
  simp only [CollatzResearch.WordTrace]
  refine ⟨168219842065885146623365979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112146561377256764415577319 168219842065885146623365979)
  ·
    refine ⟨252329763098827719935048969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 168219842065885146623365979 252329763098827719935048969)
    ·
      refine ⟨189247322324120789951286727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 252329763098827719935048969 189247322324120789951286727)
      ·
        refine ⟨283870983486181184926930091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 189247322324120789951286727 283870983486181184926930091)
        ·
          refine ⟨425806475229271777390395137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 283870983486181184926930091 425806475229271777390395137)
          ·
            refine ⟨319354856421953833042796353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 425806475229271777390395137 319354856421953833042796353)
            ·
              refine ⟨239516142316465374782097265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 319354856421953833042796353 239516142316465374782097265)
              ·
                refine ⟨179637106737349031086572949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 239516142316465374782097265 179637106737349031086572949)
                ·
                  refine ⟨8420489378313235832183107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 179637106737349031086572949 8420489378313235832183107)
                  ·
                    refine ⟨12630734067469853748274661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8420489378313235832183107 12630734067469853748274661)
                    ·
                      refine ⟨2368262637650597577801499, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12630734067469853748274661 2368262637650597577801499)
                      ·
                        rfl

theorem cell23_4612175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 2, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 2, 6, 1, 4].length) (baseStart_4612175 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4612175 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4612175 prefixEnd_4612175 := by exact prefixLift 4612175
  have htrace : WordTrace (prefixWord ++ tailWord_4612175) baseStart_4612175 baseEnd_4612175 := by
    simpa [prefixWord, tailWord_4612175, baseEnd_4612175] using wordTrace_append hprefix tailTrace_4612175
  have hstable : (prefixWord ++ tailWord_4612175).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4612175).length < 2 ^ (prefixWord ++ tailWord_4612175).sum := by decide
  have hdescent : baseEnd_4612175 < baseStart_4612175 := by decide
  rcases family_descends (prefixWord ++ tailWord_4612175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4612189 : List Nat := [1, 4, 4, 1, 1, 1, 2, 2, 2, 5]
def baseStart_4612189 : Nat := 118140960795 + 4612189 * 2 ^ 59
def prefixEnd_4612189 : Nat := 4983230072969 + 3 ^ 40 * 4612189 * 2
def baseEnd_4612189 : Nat := 789423275459920174342145

theorem tailTrace_4612189 : CollatzResearch.WordTrace tailWord_4612189 prefixEnd_4612189 789423275459920174342145 := by
  unfold tailWord_4612189
  simp only [CollatzResearch.WordTrace]
  refine ⟨168220352687834427014375621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112146901791889618009583747 168220352687834427014375621)
  ·
    refine ⟨31541316128968955065195429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 168220352687834427014375621 31541316128968955065195429)
    ·
      refine ⟨5913996774181679074724143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 31541316128968955065195429 5913996774181679074724143)
      ·
        refine ⟨8870995161272518612086215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5913996774181679074724143 8870995161272518612086215)
        ·
          refine ⟨13306492741908777918129323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8870995161272518612086215 13306492741908777918129323)
          ·
            refine ⟨19959739112863166877193985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13306492741908777918129323 19959739112863166877193985)
            ·
              refine ⟨14969804334647375157895489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19959739112863166877193985 14969804334647375157895489)
              ·
                refine ⟨11227353250985531368421617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14969804334647375157895489 11227353250985531368421617)
                ·
                  refine ⟨8420514938239148526316213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11227353250985531368421617 8420514938239148526316213)
                  ·
                    refine ⟨789423275459920174342145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8420514938239148526316213 789423275459920174342145)
                    ·
                      rfl

theorem cell23_4612189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 2, 2, 2, 5].length) (baseStart_4612189 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4612189 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4612189 prefixEnd_4612189 := by exact prefixLift 4612189
  have htrace : WordTrace (prefixWord ++ tailWord_4612189) baseStart_4612189 baseEnd_4612189 := by
    simpa [prefixWord, tailWord_4612189, baseEnd_4612189] using wordTrace_append hprefix tailTrace_4612189
  have hstable : (prefixWord ++ tailWord_4612189).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4612189).length < 2 ^ (prefixWord ++ tailWord_4612189).sum := by decide
  have hdescent : baseEnd_4612189 < baseStart_4612189 := by decide
  rcases family_descends (prefixWord ++ tailWord_4612189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4612192 : List Nat := [2, 1, 1, 3, 2, 3, 2, 2, 2, 1, 4]
def baseStart_4612192 : Nat := 118140960795 + 4612192 * 2 ^ 59
def prefixEnd_4612192 : Nat := 4983230072969 + 3 ^ 40 * 4612192 * 2
def baseEnd_4612192 : Nat := 2368271366821724011288921

theorem tailTrace_4612192 : CollatzResearch.WordTrace tailWord_4612192 prefixEnd_4612192 2368271366821724011288921 := by
  unfold tailWord_4612192
  simp only [CollatzResearch.WordTrace]
  refine ⟨84110231053411779263367415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 112146974737882372351156553 84110231053411779263367415)
  ·
    refine ⟨126165346580117668895051123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84110231053411779263367415 126165346580117668895051123)
    ·
      refine ⟨189248019870176503342576685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 126165346580117668895051123 189248019870176503342576685)
      ·
        refine ⟨70968007451316188753466257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 189248019870176503342576685 70968007451316188753466257)
        ·
          refine ⟨53226005588487141565099693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 70968007451316188753466257 53226005588487141565099693)
          ·
            refine ⟨19959752095682678086912385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 53226005588487141565099693 19959752095682678086912385)
            ·
              refine ⟨14969814071762008565184289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19959752095682678086912385 14969814071762008565184289)
              ·
                refine ⟨11227360553821506423888217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14969814071762008565184289 11227360553821506423888217)
                ·
                  refine ⟨8420520415366129817916163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11227360553821506423888217 8420520415366129817916163)
                  ·
                    refine ⟨12630780623049194726874245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8420520415366129817916163 12630780623049194726874245)
                    ·
                      refine ⟨2368271366821724011288921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12630780623049194726874245 2368271366821724011288921)
                      ·
                        rfl

theorem cell23_4612192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 2, 2, 2, 1, 4].length) (baseStart_4612192 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4612192 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4612192 prefixEnd_4612192 := by exact prefixLift 4612192
  have htrace : WordTrace (prefixWord ++ tailWord_4612192) baseStart_4612192 baseEnd_4612192 := by
    simpa [prefixWord, tailWord_4612192, baseEnd_4612192] using wordTrace_append hprefix tailTrace_4612192
  have hstable : (prefixWord ++ tailWord_4612192).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4612192).length < 2 ^ (prefixWord ++ tailWord_4612192).sum := by decide
  have hdescent : baseEnd_4612192 < baseStart_4612192 := by decide
  rcases family_descends (prefixWord ++ tailWord_4612192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4612229 : List Nat := [1, 3, 1, 1, 5, 1, 3, 1, 2, 2, 3]
def baseStart_4612229 : Nat := 118140960795 + 4612229 * 2 ^ 59
def prefixEnd_4612229 : Nat := 4983230072969 + 3 ^ 40 * 4612229 * 2
def baseEnd_4612229 : Nat := 2368290365605940366526251

theorem tailTrace_4612229 : CollatzResearch.WordTrace tailWord_4612229 prefixEnd_4612229 2368290365605940366526251 := by
  unfold tailWord_4612229
  simp only [CollatzResearch.WordTrace]
  refine ⟨168221811607689513845831741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112147874405126342563887827 168221811607689513845831741)
  ·
    refine ⟨63083179352883567692186903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 168221811607689513845831741 63083179352883567692186903)
    ·
      refine ⟨94624769029325351538280355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63083179352883567692186903 94624769029325351538280355)
      ·
        refine ⟨141937153543988027307420533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 94624769029325351538280355 141937153543988027307420533)
        ·
          refine ⟨13306608144748877560070675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 141937153543988027307420533 13306608144748877560070675)
          ·
            refine ⟨19959912217123316340106013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13306608144748877560070675 19959912217123316340106013)
            ·
              refine ⟨7484967081421243627539755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19959912217123316340106013 7484967081421243627539755)
              ·
                refine ⟨11227450622131865441309633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7484967081421243627539755 11227450622131865441309633)
                ·
                  refine ⟨8420587966598899080982225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11227450622131865441309633 8420587966598899080982225)
                  ·
                    refine ⟨6315440974949174310736669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8420587966598899080982225 6315440974949174310736669)
                    ·
                      refine ⟨2368290365605940366526251, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6315440974949174310736669 2368290365605940366526251)
                      ·
                        rfl

theorem cell23_4612229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 3, 1, 2, 2, 3].length) (baseStart_4612229 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4612229 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4612229 prefixEnd_4612229 := by exact prefixLift 4612229
  have htrace : WordTrace (prefixWord ++ tailWord_4612229) baseStart_4612229 baseEnd_4612229 := by
    simpa [prefixWord, tailWord_4612229, baseEnd_4612229] using wordTrace_append hprefix tailTrace_4612229
  have hstable : (prefixWord ++ tailWord_4612229).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4612229).length < 2 ^ (prefixWord ++ tailWord_4612229).sum := by decide
  have hdescent : baseEnd_4612229 < baseStart_4612229 := by decide
  rcases family_descends (prefixWord ++ tailWord_4612229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4612279 : List Nat := [1, 1, 3, 1, 4, 3, 2, 2, 1, 5]
def baseStart_4612279 : Nat := 118140960795 + 4612279 * 2 ^ 59
def prefixEnd_4612279 : Nat := 4983230072969 + 3 ^ 40 * 4612279 * 2
def baseEnd_4612279 : Nat := 789438679879555056967007

theorem tailTrace_4612279 : CollatzResearch.WordTrace tailWord_4612279 prefixEnd_4612279 789438679879555056967007 := by
  unfold tailWord_4612279
  simp only [CollatzResearch.WordTrace]
  refine ⟨168223635257508372385151891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112149090171672248256767927 168223635257508372385151891)
  ·
    refine ⟨252335452886262558577727837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 168223635257508372385151891 252335452886262558577727837)
    ·
      refine ⟨94625794832348459466647939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 252335452886262558577727837 94625794832348459466647939)
      ·
        refine ⟨141938692248522689199971909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 94625794832348459466647939 141938692248522689199971909)
        ·
          refine ⟨26613504796598004224994733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 141938692248522689199971909 26613504796598004224994733)
          ·
            refine ⟨9980064298724251584373025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26613504796598004224994733 9980064298724251584373025)
            ·
              refine ⟨7485048224043188688279769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9980064298724251584373025 7485048224043188688279769)
              ·
                refine ⟨5613786168032391516209827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7485048224043188688279769 5613786168032391516209827)
                ·
                  refine ⟨8420679252048587274314741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5613786168032391516209827 8420679252048587274314741)
                  ·
                    refine ⟨789438679879555056967007, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8420679252048587274314741 789438679879555056967007)
                    ·
                      rfl

theorem cell23_4612279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 3, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 3, 2, 2, 1, 5].length) (baseStart_4612279 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4612279 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4612279 prefixEnd_4612279 := by exact prefixLift 4612279
  have htrace : WordTrace (prefixWord ++ tailWord_4612279) baseStart_4612279 baseEnd_4612279 := by
    simpa [prefixWord, tailWord_4612279, baseEnd_4612279] using wordTrace_append hprefix tailTrace_4612279
  have hstable : (prefixWord ++ tailWord_4612279).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4612279).length < 2 ^ (prefixWord ++ tailWord_4612279).sum := by decide
  have hdescent : baseEnd_4612279 < baseStart_4612279 := by decide
  rcases family_descends (prefixWord ++ tailWord_4612279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4612282 : List Nat := [3, 1, 1, 1, 2, 2, 2, 3, 3, 1, 4]
def baseStart_4612282 : Nat := 118140960795 + 4612282 * 2 ^ 59
def prefixEnd_4612282 : Nat := 4983230072969 + 3 ^ 40 * 4612282 * 2
def baseEnd_4612282 : Nat := 2368317580080628659163507

theorem tailTrace_4612282 : CollatzResearch.WordTrace tailWord_4612282 prefixEnd_4612282 2368317580080628659163507 := by
  unfold tailWord_4612282
  simp only [CollatzResearch.WordTrace]
  refine ⟨42055936169124375974377775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 112149163117665002598340733 42055936169124375974377775)
  ·
    refine ⟨63083904253686563961566663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42055936169124375974377775 63083904253686563961566663)
    ·
      refine ⟨94625856380529845942349995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63083904253686563961566663 94625856380529845942349995)
      ·
        refine ⟨141938784570794768913524993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 94625856380529845942349995 141938784570794768913524993)
        ·
          refine ⟨106454088428096076685143745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 141938784570794768913524993 106454088428096076685143745)
          ·
            refine ⟨79840566321072057513857809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 106454088428096076685143745 79840566321072057513857809)
            ·
              refine ⟨59880424740804043135393357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 79840566321072057513857809 59880424740804043135393357)
              ·
                refine ⟨22455159277801516175772509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 59880424740804043135393357 22455159277801516175772509)
                ·
                  refine ⟨8420684729175568565914691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22455159277801516175772509 8420684729175568565914691)
                  ·
                    refine ⟨12631027093763352848872037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8420684729175568565914691 12631027093763352848872037)
                    ·
                      refine ⟨2368317580080628659163507, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12631027093763352848872037 2368317580080628659163507)
                      ·
                        rfl

theorem cell23_4612282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 2, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 2, 3, 3, 1, 4].length) (baseStart_4612282 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4612282 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4612282 prefixEnd_4612282 := by exact prefixLift 4612282
  have htrace : WordTrace (prefixWord ++ tailWord_4612282) baseStart_4612282 baseEnd_4612282 := by
    simpa [prefixWord, tailWord_4612282, baseEnd_4612282] using wordTrace_append hprefix tailTrace_4612282
  have hstable : (prefixWord ++ tailWord_4612282).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4612282).length < 2 ^ (prefixWord ++ tailWord_4612282).sum := by decide
  have hdescent : baseEnd_4612282 < baseStart_4612282 := by decide
  rcases family_descends (prefixWord ++ tailWord_4612282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4612305 : List Nat := [1, 2, 2, 1, 2, 2, 13]
def baseStart_4612305 : Nat := 118140960795 + 4612305 * 2 ^ 59
def prefixEnd_4612305 : Nat := 4983230072969 + 3 ^ 40 * 4612305 * 2
def baseEnd_4612305 : Nat := 29238634446119531718221

theorem tailTrace_4612305 : CollatzResearch.WordTrace tailWord_4612305 prefixEnd_4612305 29238634446119531718221 := by
  unfold tailWord_4612305
  simp only [CollatzResearch.WordTrace]
  refine ⟨168224583555414178825598369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112149722370276119217065579 168224583555414178825598369)
  ·
    refine ⟨126168437666560634119198777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 168224583555414178825598369 126168437666560634119198777)
    ·
      refine ⟨94626328249920475589399083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 126168437666560634119198777 94626328249920475589399083)
      ·
        refine ⟨141939492374880713384098625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 94626328249920475589399083 141939492374880713384098625)
        ·
          refine ⟨106454619281160535038073969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 141939492374880713384098625 106454619281160535038073969)
          ·
            refine ⟨79840964460870401278555477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 106454619281160535038073969 79840964460870401278555477)
            ·
              refine ⟨29238634446119531718221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 13 79840964460870401278555477 29238634446119531718221)
              ·
                rfl

theorem cell23_4612305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 13].length) (baseStart_4612305 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4612305 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4612305 prefixEnd_4612305 := by exact prefixLift 4612305
  have htrace : WordTrace (prefixWord ++ tailWord_4612305) baseStart_4612305 baseEnd_4612305 := by
    simpa [prefixWord, tailWord_4612305, baseEnd_4612305] using wordTrace_append hprefix tailTrace_4612305
  have hstable : (prefixWord ++ tailWord_4612305).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4612305).length < 2 ^ (prefixWord ++ tailWord_4612305).sum := by decide
  have hdescent : baseEnd_4612305 < baseStart_4612305 := by decide
  rcases family_descends (prefixWord ++ tailWord_4612305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4612310 : List Nat := [5, 2, 1, 2, 1, 3, 1, 1, 3, 1, 3]
def baseStart_4612310 : Nat := 118140960795 + 4612310 * 2 ^ 59
def prefixEnd_4612310 : Nat := 4983230072969 + 3 ^ 40 * 4612310 * 2
def baseEnd_4612310 : Nat := 2368331957538954549613379

theorem tailTrace_4612310 : CollatzResearch.WordTrace tailWord_4612310 prefixEnd_4612310 2368331957538954549613379 := by
  unfold tailWord_4612310
  simp only [CollatzResearch.WordTrace]
  refine ⟨10514047870024754042470649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 112149843946930709786353589 10514047870024754042470649)
  ·
    refine ⟨7885535902518565531852987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10514047870024754042470649 7885535902518565531852987)
    ·
      refine ⟨11828303853777848297779481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7885535902518565531852987 11828303853777848297779481)
      ·
        refine ⟨8871227890333386223334611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11828303853777848297779481 8871227890333386223334611)
        ·
          refine ⟨13306841835500079335001917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8871227890333386223334611 13306841835500079335001917)
          ·
            refine ⟨4990065688312529750625719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13306841835500079335001917 4990065688312529750625719)
            ·
              refine ⟨7485098532468794625938579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4990065688312529750625719 7485098532468794625938579)
              ·
                refine ⟨11227647798703191938907869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7485098532468794625938579 11227647798703191938907869)
                ·
                  refine ⟨4210367924513696977090451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11227647798703191938907869 4210367924513696977090451)
                  ·
                    refine ⟨6315551886770545465635677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4210367924513696977090451 6315551886770545465635677)
                    ·
                      refine ⟨2368331957538954549613379, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6315551886770545465635677 2368331957538954549613379)
                      ·
                        rfl

theorem cell23_4612310_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 3, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 3, 1, 1, 3, 1, 3].length) (baseStart_4612310 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4612310 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4612310 prefixEnd_4612310 := by exact prefixLift 4612310
  have htrace : WordTrace (prefixWord ++ tailWord_4612310) baseStart_4612310 baseEnd_4612310 := by
    simpa [prefixWord, tailWord_4612310, baseEnd_4612310] using wordTrace_append hprefix tailTrace_4612310
  have hstable : (prefixWord ++ tailWord_4612310).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4612310).length < 2 ^ (prefixWord ++ tailWord_4612310).sum := by decide
  have hdescent : baseEnd_4612310 < baseStart_4612310 := by decide
  rcases family_descends (prefixWord ++ tailWord_4612310) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4612312 : List Nat := [2, 1, 2, 2, 4, 1, 1, 2, 1, 1, 6]
def baseStart_4612312 : Nat := 118140960795 + 4612312 * 2 ^ 59
def prefixEnd_4612312 : Nat := 4983230072969 + 3 ^ 40 * 4612312 * 2
def baseEnd_4612312 : Nat := 2368332984500263541788369

theorem tailTrace_4612312 : CollatzResearch.WordTrace tailWord_4612312 prefixEnd_4612312 2368332984500263541788369 := by
  unfold tailWord_4612312
  simp only [CollatzResearch.WordTrace]
  refine ⟨84112419433194409510551595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 112149892577592546014068793 84112419433194409510551595)
  ·
    refine ⟨126168629149791614265827393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84112419433194409510551595 126168629149791614265827393)
    ·
      refine ⟨94626471862343710699370545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 126168629149791614265827393 94626471862343710699370545)
      ·
        refine ⟨70969853896757783024527909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 94626471862343710699370545 70969853896757783024527909)
        ·
          refine ⟨13306847605642084317098983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 70969853896757783024527909 13306847605642084317098983)
          ·
            refine ⟨19960271408463126475648475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13306847605642084317098983 19960271408463126475648475)
            ·
              refine ⟨29940407112694689713472713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19960271408463126475648475 29940407112694689713472713)
              ·
                refine ⟨22455305334521017285104535, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29940407112694689713472713 22455305334521017285104535)
                ·
                  refine ⟨33682958001781525927656803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22455305334521017285104535 33682958001781525927656803)
                  ·
                    refine ⟨50524437002672288891485205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 33682958001781525927656803 50524437002672288891485205)
                    ·
                      refine ⟨2368332984500263541788369, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 50524437002672288891485205 2368332984500263541788369)
                      ·
                        rfl

theorem cell23_4612312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 1, 2, 1, 1, 6].length) (baseStart_4612312 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4612312 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4612312 prefixEnd_4612312 := by exact prefixLift 4612312
  have htrace : WordTrace (prefixWord ++ tailWord_4612312) baseStart_4612312 baseEnd_4612312 := by
    simpa [prefixWord, tailWord_4612312, baseEnd_4612312] using wordTrace_append hprefix tailTrace_4612312
  have hstable : (prefixWord ++ tailWord_4612312).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4612312).length < 2 ^ (prefixWord ++ tailWord_4612312).sum := by decide
  have hdescent : baseEnd_4612312 < baseStart_4612312 := by decide
  rcases family_descends (prefixWord ++ tailWord_4612312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4612315 : List Nat := [1, 1, 1, 1, 1, 1, 1, 5, 2, 2, 7]
def baseStart_4612315 : Nat := 118140960795 + 4612315 * 2 ^ 59
def prefixEnd_4612315 : Nat := 4983230072969 + 3 ^ 40 * 4612315 * 2
def baseEnd_4612315 : Nat := 2368334524942227030050855

theorem tailTrace_4612315 : CollatzResearch.WordTrace tailWord_4612315 prefixEnd_4612315 2368334524942227030050855 := by
  unfold tailWord_4612315
  simp only [CollatzResearch.WordTrace]
  refine ⟨168224948285377950533462399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112149965523585300355641599 168224948285377950533462399)
  ·
    refine ⟨252337422428066925800193599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 168224948285377950533462399 252337422428066925800193599)
    ·
      refine ⟨378506133642100388700290399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 252337422428066925800193599 378506133642100388700290399)
      ·
        refine ⟨567759200463150583050435599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 378506133642100388700290399 567759200463150583050435599)
        ·
          refine ⟨851638800694725874575653399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 567759200463150583050435599 851638800694725874575653399)
          ·
            refine ⟨1277458201042088811863480099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 851638800694725874575653399 1277458201042088811863480099)
            ·
              refine ⟨1916187301563133217795220149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1277458201042088811863480099 1916187301563133217795220149)
              ·
                refine ⟨179642559521543739168301889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1916187301563133217795220149 179642559521543739168301889)
                ·
                  refine ⟨134731919641157804376226417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 179642559521543739168301889 134731919641157804376226417)
                  ·
                    refine ⟨101048939730868353282169813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 134731919641157804376226417 101048939730868353282169813)
                    ·
                      refine ⟨2368334524942227030050855, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 101048939730868353282169813 2368334524942227030050855)
                      ·
                        rfl

theorem cell23_4612315_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 5, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 5, 2, 2, 7].length) (baseStart_4612315 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4612315 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4612315 prefixEnd_4612315 := by exact prefixLift 4612315
  have htrace : WordTrace (prefixWord ++ tailWord_4612315) baseStart_4612315 baseEnd_4612315 := by
    simpa [prefixWord, tailWord_4612315, baseEnd_4612315] using wordTrace_append hprefix tailTrace_4612315
  have hstable : (prefixWord ++ tailWord_4612315).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4612315).length < 2 ^ (prefixWord ++ tailWord_4612315).sum := by decide
  have hdescent : baseEnd_4612315 < baseStart_4612315 := by decide
  rcases family_descends (prefixWord ++ tailWord_4612315) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4612333 : List Nat := [1, 5, 1, 2, 3, 2, 1, 2, 1, 1, 4]
def baseStart_4612333 : Nat := 118140960795 + 4612333 * 2 ^ 59
def prefixEnd_4612333 : Nat := 4983230072969 + 3 ^ 40 * 4612333 * 2
def baseEnd_4612333 : Nat := 2368343767594007959625773

theorem tailTrace_4612333 : CollatzResearch.WordTrace tailWord_4612333 prefixEnd_4612333 2368343767594007959625773 := by
  unfold tailWord_4612333
  simp only [CollatzResearch.WordTrace]
  refine ⟨168225604799312739607617653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112150403199541826405078435 168225604799312739607617653)
  ·
    refine ⟨15771150449935569338214155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 168225604799312739607617653 15771150449935569338214155)
    ·
      refine ⟨23656725674903354007321233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15771150449935569338214155 23656725674903354007321233)
      ·
        refine ⟨17742544256177515505490925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23656725674903354007321233 17742544256177515505490925)
        ·
          refine ⟨6653454096066568314559097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17742544256177515505490925 6653454096066568314559097)
          ·
            refine ⟨4990090572049926235919323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6653454096066568314559097 4990090572049926235919323)
            ·
              refine ⟨7485135858074889353878985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4990090572049926235919323 7485135858074889353878985)
              ·
                refine ⟨5613851893556167015409239, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7485135858074889353878985 5613851893556167015409239)
                ·
                  refine ⟨8420777840334250523113859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5613851893556167015409239 8420777840334250523113859)
                  ·
                    refine ⟨12631166760501375784670789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8420777840334250523113859 12631166760501375784670789)
                    ·
                      refine ⟨2368343767594007959625773, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12631166760501375784670789 2368343767594007959625773)
                      ·
                        rfl

theorem cell23_4612333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 3, 2, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 3, 2, 1, 2, 1, 1, 4].length) (baseStart_4612333 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4612333 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4612333 prefixEnd_4612333 := by exact prefixLift 4612333
  have htrace : WordTrace (prefixWord ++ tailWord_4612333) baseStart_4612333 baseEnd_4612333 := by
    simpa [prefixWord, tailWord_4612333, baseEnd_4612333] using wordTrace_append hprefix tailTrace_4612333
  have hstable : (prefixWord ++ tailWord_4612333).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4612333).length < 2 ^ (prefixWord ++ tailWord_4612333).sum := by decide
  have hdescent : baseEnd_4612333 < baseStart_4612333 := by decide
  rcases family_descends (prefixWord ++ tailWord_4612333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4612349 : List Nat := [1, 4, 1, 1, 1, 1, 1, 3, 6, 1, 3]
def baseStart_4612349 : Nat := 118140960795 + 4612349 * 2 ^ 59
def prefixEnd_4612349 : Nat := 4983230072969 + 3 ^ 40 * 4612349 * 2
def baseEnd_4612349 : Nat := 2368351983284479897025699

theorem tailTrace_4612349 : CollatzResearch.WordTrace tailWord_4612349 prefixEnd_4612349 2368351983284479897025699 := by
  unfold tailWord_4612349
  simp only [CollatzResearch.WordTrace]
  refine ⟨168226188367254774340200101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112150792244836516226800067 168226188367254774340200101)
  ·
    refine ⟨31542410318860270188787519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 168226188367254774340200101 31542410318860270188787519)
    ·
      refine ⟨47313615478290405283181279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31542410318860270188787519 47313615478290405283181279)
      ·
        refine ⟨70970423217435607924771919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47313615478290405283181279 70970423217435607924771919)
        ·
          refine ⟨106455634826153411887157879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 70970423217435607924771919 106455634826153411887157879)
          ·
            refine ⟨159683452239230117830736819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 106455634826153411887157879 159683452239230117830736819)
            ·
              refine ⟨239525178358845176746105229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 159683452239230117830736819 239525178358845176746105229)
              ·
                refine ⟨89821941884566941279789461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 239525178358845176746105229 89821941884566941279789461)
                ·
                  refine ⟨4210403525839075372490131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 89821941884566941279789461 4210403525839075372490131)
                  ·
                    refine ⟨6315605288758613058735197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4210403525839075372490131 6315605288758613058735197)
                    ·
                      refine ⟨2368351983284479897025699, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6315605288758613058735197 2368351983284479897025699)
                      ·
                        rfl

theorem cell23_4612349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 3, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 3, 6, 1, 3].length) (baseStart_4612349 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4612349 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4612349 prefixEnd_4612349 := by exact prefixLift 4612349
  have htrace : WordTrace (prefixWord ++ tailWord_4612349) baseStart_4612349 baseEnd_4612349 := by
    simpa [prefixWord, tailWord_4612349, baseEnd_4612349] using wordTrace_append hprefix tailTrace_4612349
  have hstable : (prefixWord ++ tailWord_4612349).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4612349).length < 2 ^ (prefixWord ++ tailWord_4612349).sum := by decide
  have hdescent : baseEnd_4612349 < baseStart_4612349 := by decide
  rcases family_descends (prefixWord ++ tailWord_4612349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4612350 : List Nat := [4, 2, 2, 1, 1, 1, 2, 5, 1, 2, 2]
def baseStart_4612350 : Nat := 118140960795 + 4612350 * 2 ^ 59
def prefixEnd_4612350 : Nat := 4983230072969 + 3 ^ 40 * 4612350 * 2
def baseEnd_4612350 : Nat := 2368352496765134393113195

theorem tailTrace_4612350 : CollatzResearch.WordTrace tailWord_4612350 prefixEnd_4612350 2368352496765134393113195 := by
  unfold tailWord_4612350
  simp only [CollatzResearch.WordTrace]
  refine ⟨21028278105031393938873313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 112150816560167434340657669 21028278105031393938873313)
  ·
    refine ⟨15771208578773545454154985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21028278105031393938873313 15771208578773545454154985)
    ·
      refine ⟨11828406434080159090616239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15771208578773545454154985 11828406434080159090616239)
      ·
        refine ⟨17742609651120238635924359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11828406434080159090616239 17742609651120238635924359)
        ·
          refine ⟨26613914476680357953886539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17742609651120238635924359 26613914476680357953886539)
          ·
            refine ⟨39920871715020536930829809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26613914476680357953886539 39920871715020536930829809)
            ·
              refine ⟨29940653786265402698122357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 39920871715020536930829809 29940653786265402698122357)
              ·
                refine ⟨2806936292462381502948971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 29940653786265402698122357 2806936292462381502948971)
                ·
                  refine ⟨4210404438693572254423457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2806936292462381502948971 4210404438693572254423457)
                  ·
                    refine ⟨3157803329020179190817593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4210404438693572254423457 3157803329020179190817593)
                    ·
                      refine ⟨2368352496765134393113195, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3157803329020179190817593 2368352496765134393113195)
                      ·
                        rfl

theorem cell23_4612350_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 2, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 2, 5, 1, 2, 2].length) (baseStart_4612350 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4612350 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4612350 prefixEnd_4612350 := by exact prefixLift 4612350
  have htrace : WordTrace (prefixWord ++ tailWord_4612350) baseStart_4612350 baseEnd_4612350 := by
    simpa [prefixWord, tailWord_4612350, baseEnd_4612350] using wordTrace_append hprefix tailTrace_4612350
  have hstable : (prefixWord ++ tailWord_4612350).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4612350).length < 2 ^ (prefixWord ++ tailWord_4612350).sum := by decide
  have hdescent : baseEnd_4612350 < baseStart_4612350 := by decide
  rcases family_descends (prefixWord ++ tailWord_4612350) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4612362 : List Nat := [3, 1, 2, 2, 1, 1, 2, 2, 2, 2, 5]
def baseStart_4612362 : Nat := 118140960795 + 4612362 * 2 ^ 59
def prefixEnd_4612362 : Nat := 4983230072969 + 3 ^ 40 * 4612362 * 2
def baseEnd_4612362 : Nat := 2368358658532988346163139

theorem tailTrace_4612362 : CollatzResearch.WordTrace tailWord_4612362 prefixEnd_4612362 2368358658532988346163139 := by
  unfold tailWord_4612362
  simp only [CollatzResearch.WordTrace]
  refine ⟨42056665629051919390105835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 112151108344138451706948893 42056665629051919390105835)
  ·
    refine ⟨63084998443577879085158753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42056665629051919390105835 63084998443577879085158753)
    ·
      refine ⟨47313748832683409313869065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 63084998443577879085158753 47313748832683409313869065)
      ·
        refine ⟨35485311624512556985401799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47313748832683409313869065 35485311624512556985401799)
        ·
          refine ⟨53227967436768835478102699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35485311624512556985401799 53227967436768835478102699)
          ·
            refine ⟨79841951155153253217154049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53227967436768835478102699 79841951155153253217154049)
            ·
              refine ⟨59881463366364939912865537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 79841951155153253217154049 59881463366364939912865537)
              ·
                refine ⟨44911097524773704934649153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 59881463366364939912865537 44911097524773704934649153)
                ·
                  refine ⟨33683323143580278700986865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 44911097524773704934649153 33683323143580278700986865)
                  ·
                    refine ⟨25262492357685209025740149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 33683323143580278700986865 25262492357685209025740149)
                    ·
                      refine ⟨2368358658532988346163139, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25262492357685209025740149 2368358658532988346163139)
                      ·
                        rfl

theorem cell23_4612362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 2, 2, 2, 2, 5].length) (baseStart_4612362 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4612362 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4612362 prefixEnd_4612362 := by exact prefixLift 4612362
  have htrace : WordTrace (prefixWord ++ tailWord_4612362) baseStart_4612362 baseEnd_4612362 := by
    simpa [prefixWord, tailWord_4612362, baseEnd_4612362] using wordTrace_append hprefix tailTrace_4612362
  have hstable : (prefixWord ++ tailWord_4612362).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4612362).length < 2 ^ (prefixWord ++ tailWord_4612362).sum := by decide
  have hdescent : baseEnd_4612362 < baseStart_4612362 := by decide
  rcases family_descends (prefixWord ++ tailWord_4612362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4612410 : List Nat := [3, 1, 1, 1, 4, 4, 2, 1, 1, 3, 2]
def baseStart_4612410 : Nat := 118140960795 + 4612410 * 2 ^ 59
def prefixEnd_4612410 : Nat := 4983230072969 + 3 ^ 40 * 4612410 * 2
def baseEnd_4612410 : Nat := 2368383305604404158362919

theorem tailTrace_4612410 : CollatzResearch.WordTrace tailWord_4612410 prefixEnd_4612410 2368383305604404158362919 := by
  unfold tailWord_4612410
  simp only [CollatzResearch.WordTrace]
  refine ⟨42057103305008445439542671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 112152275480022521172113789 42057103305008445439542671)
  ·
    refine ⟨63085654957512668159314007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42057103305008445439542671 63085654957512668159314007)
    ·
      refine ⟨94628482436269002238971011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63085654957512668159314007 94628482436269002238971011)
      ·
        refine ⟨141942723654403503358456517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 94628482436269002238971011 141942723654403503358456517)
        ·
          refine ⟨26614260685200656879710597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 141942723654403503358456517 26614260685200656879710597)
          ·
            refine ⟨4990173878475123164945737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 26614260685200656879710597 4990173878475123164945737)
            ·
              refine ⟨3742630408856342373709303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4990173878475123164945737 3742630408856342373709303)
              ·
                refine ⟨5613945613284513560563955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3742630408856342373709303 5613945613284513560563955)
                ·
                  refine ⟨8420918419926770340845933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5613945613284513560563955 8420918419926770340845933)
                  ·
                    refine ⟨3157844407472538877817225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8420918419926770340845933 3157844407472538877817225)
                    ·
                      refine ⟨2368383305604404158362919, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3157844407472538877817225 2368383305604404158362919)
                      ·
                        rfl

theorem cell23_4612410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 4, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 4, 2, 1, 1, 3, 2].length) (baseStart_4612410 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4612410 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4612410 prefixEnd_4612410 := by exact prefixLift 4612410
  have htrace : WordTrace (prefixWord ++ tailWord_4612410) baseStart_4612410 baseEnd_4612410 := by
    simpa [prefixWord, tailWord_4612410, baseEnd_4612410] using wordTrace_append hprefix tailTrace_4612410
  have hstable : (prefixWord ++ tailWord_4612410).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4612410).length < 2 ^ (prefixWord ++ tailWord_4612410).sum := by decide
  have hdescent : baseEnd_4612410 < baseStart_4612410 := by decide
  rcases family_descends (prefixWord ++ tailWord_4612410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4612412 : List Nat := [2, 2, 2, 2, 1, 2, 1, 2, 9]
def baseStart_4612412 : Nat := 118140960795 + 4612412 * 2 ^ 59
def prefixEnd_4612412 : Nat := 4983230072969 + 3 ^ 40 * 4612412 * 2
def baseEnd_4612412 : Nat := 263153814729523683393101

theorem tailTrace_4612412 : CollatzResearch.WordTrace tailWord_4612412 prefixEnd_4612412 263153814729523683393101 := by
  unfold tailWord_4612412
  simp only [CollatzResearch.WordTrace]
  refine ⟨84114243083013268049871745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 112152324110684357399828993 84114243083013268049871745)
  ·
    refine ⟨63085682312259951037403809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 84114243083013268049871745 63085682312259951037403809)
    ·
      refine ⟨47314261734194963278052857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 63085682312259951037403809 47314261734194963278052857)
      ·
        refine ⟨35485696300646222458539643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47314261734194963278052857 35485696300646222458539643)
        ·
          refine ⟨53228544450969333687809465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35485696300646222458539643 53228544450969333687809465)
          ·
            refine ⟨39921408338227000265857099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 53228544450969333687809465 39921408338227000265857099)
            ·
              refine ⟨59882112507340500398785649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39921408338227000265857099 59882112507340500398785649)
              ·
                refine ⟨44911584380505375299089237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 59882112507340500398785649 44911584380505375299089237)
                ·
                  refine ⟨263153814729523683393101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 44911584380505375299089237 263153814729523683393101)
                  ·
                    rfl

theorem cell23_4612412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 1, 2, 9].length) (baseStart_4612412 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4612412 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4612412 prefixEnd_4612412 := by exact prefixLift 4612412
  have htrace : WordTrace (prefixWord ++ tailWord_4612412) baseStart_4612412 baseEnd_4612412 := by
    simpa [prefixWord, tailWord_4612412, baseEnd_4612412] using wordTrace_append hprefix tailTrace_4612412
  have hstable : (prefixWord ++ tailWord_4612412).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4612412).length < 2 ^ (prefixWord ++ tailWord_4612412).sum := by decide
  have hdescent : baseEnd_4612412 < baseStart_4612412 := by decide
  rcases family_descends (prefixWord ++ tailWord_4612412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4612417 : List Nat := [1, 2, 5, 2, 3, 1, 1, 2, 2, 1, 3]
def baseStart_4612417 : Nat := 118140960795 + 4612417 * 2 ^ 59
def prefixEnd_4612417 : Nat := 4983230072969 + 3 ^ 40 * 4612417 * 2
def baseEnd_4612417 : Nat := 2368386899968985630975387

theorem tailTrace_4612417 : CollatzResearch.WordTrace tailWord_4612417 prefixEnd_4612417 2368386899968985630975387 := by
  unfold tailWord_4612417
  simp only [CollatzResearch.WordTrace]
  refine ⟨168228668531008421953675505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112152445687338947969117003 168228668531008421953675505)
  ·
    refine ⟨126171501398256316465256629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 168228668531008421953675505 126171501398256316465256629)
    ·
      refine ⟨11828578256086529668617809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 126171501398256316465256629 11828578256086529668617809)
      ·
        refine ⟨8871433692064897251463357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11828578256086529668617809 8871433692064897251463357)
        ·
          refine ⟨3326787634524336469298759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8871433692064897251463357 3326787634524336469298759)
          ·
            refine ⟨4990181451786504703948139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3326787634524336469298759 4990181451786504703948139)
            ·
              refine ⟨7485272177679757055922209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4990181451786504703948139 7485272177679757055922209)
              ·
                refine ⟨5613954133259817791941657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7485272177679757055922209 5613954133259817791941657)
                ·
                  refine ⟨4210465599944863343956243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5613954133259817791941657 4210465599944863343956243)
                  ·
                    refine ⟨6315698399917295015934365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4210465599944863343956243 6315698399917295015934365)
                    ·
                      refine ⟨2368386899968985630975387, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6315698399917295015934365 2368386899968985630975387)
                      ·
                        rfl

theorem cell23_4612417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 3, 1, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 3, 1, 1, 2, 2, 1, 3].length) (baseStart_4612417 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4612417 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4612417 prefixEnd_4612417 := by exact prefixLift 4612417
  have htrace : WordTrace (prefixWord ++ tailWord_4612417) baseStart_4612417 baseEnd_4612417 := by
    simpa [prefixWord, tailWord_4612417, baseEnd_4612417] using wordTrace_append hprefix tailTrace_4612417
  have hstable : (prefixWord ++ tailWord_4612417).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4612417).length < 2 ^ (prefixWord ++ tailWord_4612417).sum := by decide
  have hdescent : baseEnd_4612417 < baseStart_4612417 := by decide
  rcases family_descends (prefixWord ++ tailWord_4612417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4612439 : List Nat := [1, 1, 3, 2, 3, 1, 1, 3, 2, 3, 3]
def baseStart_4612439 : Nat := 118140960795 + 4612439 * 2 ^ 59
def prefixEnd_4612439 : Nat := 4983230072969 + 3 ^ 40 * 4612439 * 2
def baseEnd_4612439 : Nat := 2368398196543384544900285

theorem tailTrace_4612439 : CollatzResearch.WordTrace tailWord_4612439 prefixEnd_4612439 2368398196543384544900285 := by
  unfold tailWord_4612439
  simp only [CollatzResearch.WordTrace]
  refine ⟨168229470936928719710976371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112152980624619146473984247 168229470936928719710976371)
  ·
    refine ⟨252344206405393079566464557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 168229470936928719710976371 252344206405393079566464557)
    ·
      refine ⟨94629077402022404837424209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 252344206405393079566464557 94629077402022404837424209)
      ·
        refine ⟨70971808051516803628068157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 94629077402022404837424209 70971808051516803628068157)
        ·
          refine ⟨26614428019318801360525559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 70971808051516803628068157 26614428019318801360525559)
          ·
            refine ⟨39921642028978202040788339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26614428019318801360525559 39921642028978202040788339)
            ·
              refine ⟨59882463043467303061182509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39921642028978202040788339 59882463043467303061182509)
              ·
                refine ⟨22455923641300238647943441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 59882463043467303061182509 22455923641300238647943441)
                ·
                  refine ⟨16841942730975178985957581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22455923641300238647943441 16841942730975178985957581)
                  ·
                    refine ⟨6315728524115692119734093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16841942730975178985957581 6315728524115692119734093)
                    ·
                      refine ⟨2368398196543384544900285, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6315728524115692119734093 2368398196543384544900285)
                      ·
                        rfl

theorem cell23_4612439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 1, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 1, 3, 2, 3, 3].length) (baseStart_4612439 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4612439 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4612439 prefixEnd_4612439 := by exact prefixLift 4612439
  have htrace : WordTrace (prefixWord ++ tailWord_4612439) baseStart_4612439 baseEnd_4612439 := by
    simpa [prefixWord, tailWord_4612439, baseEnd_4612439] using wordTrace_append hprefix tailTrace_4612439
  have hstable : (prefixWord ++ tailWord_4612439).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4612439).length < 2 ^ (prefixWord ++ tailWord_4612439).sum := by decide
  have hdescent : baseEnd_4612439 < baseStart_4612439 := by decide
  rcases family_descends (prefixWord ++ tailWord_4612439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4612479 : List Nat := [1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 4]
def baseStart_4612479 : Nat := 118140960795 + 4612479 * 2 ^ 59
def prefixEnd_4612479 : Nat := 4983230072969 + 3 ^ 40 * 4612479 * 2
def baseEnd_4612479 : Nat := 2368418735769564388400101

theorem tailTrace_4612479 : CollatzResearch.WordTrace tailWord_4612479 prefixEnd_4612479 2368418735769564388400101 := by
  unfold tailWord_4612479
  simp only [CollatzResearch.WordTrace]
  refine ⟨168230929856783806542432491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112153953237855871028288327 168230929856783806542432491)
  ·
    refine ⟨252346394785175709813648737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 168230929856783806542432491 252346394785175709813648737)
    ·
      refine ⟨189259796088881782360236553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 252346394785175709813648737 189259796088881782360236553)
      ·
        refine ⟨141944847066661336770177415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 189259796088881782360236553 141944847066661336770177415)
        ·
          refine ⟨212917270599992005155266123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 141944847066661336770177415 212917270599992005155266123)
          ·
            refine ⟨319375905899988007732899185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 212917270599992005155266123 319375905899988007732899185)
            ·
              refine ⟨239531929424991005799674389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 319375905899988007732899185 239531929424991005799674389)
              ·
                refine ⟨11228059191796453396859737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 239531929424991005799674389 11228059191796453396859737)
                ·
                  refine ⟨8421044393847340047644803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11228059191796453396859737 8421044393847340047644803)
                  ·
                    refine ⟨12631566590771010071467205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8421044393847340047644803 12631566590771010071467205)
                    ·
                      refine ⟨2368418735769564388400101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12631566590771010071467205 2368418735769564388400101)
                      ·
                        rfl

theorem cell23_4612479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 4].length) (baseStart_4612479 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4612479 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4612479 prefixEnd_4612479 := by exact prefixLift 4612479
  have htrace : WordTrace (prefixWord ++ tailWord_4612479) baseStart_4612479 baseEnd_4612479 := by
    simpa [prefixWord, tailWord_4612479, baseEnd_4612479] using wordTrace_append hprefix tailTrace_4612479
  have hstable : (prefixWord ++ tailWord_4612479).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4612479).length < 2 ^ (prefixWord ++ tailWord_4612479).sum := by decide
  have hdescent : baseEnd_4612479 < baseStart_4612479 := by decide
  rcases family_descends (prefixWord ++ tailWord_4612479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4612516 : List Nat := [2, 3, 1, 2, 1, 1, 3, 3, 2, 2, 3]
def baseStart_4612516 : Nat := 118140960795 + 4612516 * 2 ^ 59
def prefixEnd_4612516 : Nat := 4983230072969 + 3 ^ 40 * 4612516 * 2
def baseEnd_4612516 : Nat := 2368437734553780743637431

theorem tailTrace_4612516 : CollatzResearch.WordTrace tailWord_4612516 prefixEnd_4612516 2368437734553780743637431 := by
  unfold tailWord_4612516
  simp only [CollatzResearch.WordTrace]
  refine ⟨84116139678824880930764701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 112154852905099841241019601 84116139678824880930764701)
  ·
    refine ⟨31543552379559330349036763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 84116139678824880930764701 31543552379559330349036763)
    ·
      refine ⟨47315328569338995523555145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31543552379559330349036763 47315328569338995523555145)
      ·
        refine ⟨35486496427004246642666359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47315328569338995523555145 35486496427004246642666359)
        ·
          refine ⟨53229744640506369963999539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35486496427004246642666359 53229744640506369963999539)
          ·
            refine ⟨79844616960759554945999309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53229744640506369963999539 79844616960759554945999309)
            ·
              refine ⟨29941731360284833104749741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 79844616960759554945999309 29941731360284833104749741)
              ·
                refine ⟨11228149260106812414281153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 29941731360284833104749741 11228149260106812414281153)
                ·
                  refine ⟨8421111945080109310710865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11228149260106812414281153 8421111945080109310710865)
                  ·
                    refine ⟨6315833958810081983033149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8421111945080109310710865 6315833958810081983033149)
                    ·
                      refine ⟨2368437734553780743637431, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6315833958810081983033149 2368437734553780743637431)
                      ·
                        rfl

theorem cell23_4612516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 3, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 3, 3, 2, 2, 3].length) (baseStart_4612516 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4612516 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4612516 prefixEnd_4612516 := by exact prefixLift 4612516
  have htrace : WordTrace (prefixWord ++ tailWord_4612516) baseStart_4612516 baseEnd_4612516 := by
    simpa [prefixWord, tailWord_4612516, baseEnd_4612516] using wordTrace_append hprefix tailTrace_4612516
  have hstable : (prefixWord ++ tailWord_4612516).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4612516).length < 2 ^ (prefixWord ++ tailWord_4612516).sum := by decide
  have hdescent : baseEnd_4612516 < baseStart_4612516 := by decide
  rcases family_descends (prefixWord ++ tailWord_4612516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4612540 : List Nat := [2, 2, 2, 4, 1, 2, 1, 4, 1, 4]
def baseStart_4612540 : Nat := 118140960795 + 4612540 * 2 ^ 59
def prefixEnd_4612540 : Nat := 4983230072969 + 3 ^ 40 * 4612540 * 2
def baseEnd_4612540 : Nat := 789483352696496216579107

theorem tailTrace_4612540 : CollatzResearch.WordTrace tailWord_4612540 prefixEnd_4612540 789483352696496216579107 := by
  unfold tailWord_4612540
  simp only [CollatzResearch.WordTrace]
  refine ⟨84116577354781406980201537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 112155436473041875973602049 84116577354781406980201537)
  ·
    refine ⟨63087433016086055235151153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 84116577354781406980201537 63087433016086055235151153)
    ·
      refine ⟨47315574762064541426363365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 63087433016086055235151153 47315574762064541426363365)
      ·
        refine ⟨8871670267887101517443131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 47315574762064541426363365 8871670267887101517443131)
        ·
          refine ⟨13307505401830652276164697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8871670267887101517443131 13307505401830652276164697)
          ·
            refine ⟨9980629051372989207123523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13307505401830652276164697 9980629051372989207123523)
            ·
              refine ⟨14970943577059483810685285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9980629051372989207123523 14970943577059483810685285)
              ·
                refine ⟨2807051920698653214503491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14970943577059483810685285 2807051920698653214503491)
                ·
                  refine ⟨4210577881047979821755237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2807051920698653214503491 4210577881047979821755237)
                  ·
                    refine ⟨789483352696496216579107, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4210577881047979821755237 789483352696496216579107)
                    ·
                      rfl

theorem cell23_4612540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 2, 1, 4, 1, 4].length) (baseStart_4612540 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4612540 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4612540 prefixEnd_4612540 := by exact prefixLift 4612540
  have htrace : WordTrace (prefixWord ++ tailWord_4612540) baseStart_4612540 baseEnd_4612540 := by
    simpa [prefixWord, tailWord_4612540, baseEnd_4612540] using wordTrace_append hprefix tailTrace_4612540
  have hstable : (prefixWord ++ tailWord_4612540).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4612540).length < 2 ^ (prefixWord ++ tailWord_4612540).sum := by decide
  have hdescent : baseEnd_4612540 < baseStart_4612540 := by decide
  rcases family_descends (prefixWord ++ tailWord_4612540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4612573 : List Nat := [1, 4, 3, 1, 1, 1, 3, 1, 1, 5, 2]
def baseStart_4612573 : Nat := 118140960795 + 4612573 * 2 ^ 59
def prefixEnd_4612573 : Nat := 4983230072969 + 3 ^ 40 * 4612573 * 2
def baseEnd_4612573 : Nat := 2368467002951087020624669

theorem tailTrace_4612573 : CollatzResearch.WordTrace tailWord_4612573 prefixEnd_4612573 2368467002951087020624669 := by
  unfold tailWord_4612573
  simp only [CollatzResearch.WordTrace]
  refine ⟨168234358318443260596354373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112156238878962173730902915 168234358318443260596354373)
  ·
    refine ⟨31543942184708111361816445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 168234358318443260596354373 31543942184708111361816445)
    ·
      refine ⟨11828978319265541760681167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31543942184708111361816445 11828978319265541760681167)
      ·
        refine ⟨17743467478898312641021751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11828978319265541760681167 17743467478898312641021751)
        ·
          refine ⟨26615201218347468961532627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17743467478898312641021751 26615201218347468961532627)
          ·
            refine ⟨39922801827521203442298941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26615201218347468961532627 39922801827521203442298941)
            ·
              refine ⟨14971050685320451290862103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 39922801827521203442298941 14971050685320451290862103)
              ·
                refine ⟨22456576027980676936293155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14971050685320451290862103 22456576027980676936293155)
                ·
                  refine ⟨33684864041971015404439733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22456576027980676936293155 33684864041971015404439733)
                  ·
                    refine ⟨3157956003934782694166225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 33684864041971015404439733 3157956003934782694166225)
                    ·
                      refine ⟨2368467002951087020624669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3157956003934782694166225 2368467002951087020624669)
                      ·
                        rfl

theorem cell23_4612573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 3, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 3, 1, 1, 5, 2].length) (baseStart_4612573 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4612573 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4612573 prefixEnd_4612573 := by exact prefixLift 4612573
  have htrace : WordTrace (prefixWord ++ tailWord_4612573) baseStart_4612573 baseEnd_4612573 := by
    simpa [prefixWord, tailWord_4612573, baseEnd_4612573] using wordTrace_append hprefix tailTrace_4612573
  have hstable : (prefixWord ++ tailWord_4612573).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4612573).length < 2 ^ (prefixWord ++ tailWord_4612573).sum := by decide
  have hdescent : baseEnd_4612573 < baseStart_4612573 := by decide
  rcases family_descends (prefixWord ++ tailWord_4612573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4612597 : List Nat := [1, 3, 5, 1, 2, 1, 2, 1, 3, 1, 3]
def baseStart_4612597 : Nat := 118140960795 + 4612597 * 2 ^ 59
def prefixEnd_4612597 : Nat := 4983230072969 + 3 ^ 40 * 4612597 * 2
def baseEnd_4612597 : Nat := 2368479326486794926724559

theorem tailTrace_4612597 : CollatzResearch.WordTrace tailWord_4612597 prefixEnd_4612597 2368479326486794926724559 := by
  unfold tailWord_4612597
  simp only [CollatzResearch.WordTrace]
  refine ⟨168235233670356312695228045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112156822446904208463485363 168235233670356312695228045)
  ·
    refine ⟨63088212626383617260710517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 168235233670356312695228045 63088212626383617260710517)
    ·
      refine ⟨5914519933723464118191611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 63088212626383617260710517 5914519933723464118191611)
      ·
        refine ⟨8871779900585196177287417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5914519933723464118191611 8871779900585196177287417)
        ·
          refine ⟨6653834925438897132965563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8871779900585196177287417 6653834925438897132965563)
          ·
            refine ⟨9980752388158345699448345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6653834925438897132965563 9980752388158345699448345)
            ·
              refine ⟨7485564291118759274586259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9980752388158345699448345 7485564291118759274586259)
              ·
                refine ⟨11228346436678138911879389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7485564291118759274586259 11228346436678138911879389)
                ·
                  refine ⟨4210629913754302091954771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11228346436678138911879389 4210629913754302091954771)
                  ·
                    refine ⟨6315944870631453137932157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4210629913754302091954771 6315944870631453137932157)
                    ·
                      refine ⟨2368479326486794926724559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6315944870631453137932157 2368479326486794926724559)
                      ·
                        rfl

theorem cell23_4612597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 2, 1, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 2, 1, 2, 1, 3, 1, 3].length) (baseStart_4612597 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4612597 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4612597 prefixEnd_4612597 := by exact prefixLift 4612597
  have htrace : WordTrace (prefixWord ++ tailWord_4612597) baseStart_4612597 baseEnd_4612597 := by
    simpa [prefixWord, tailWord_4612597, baseEnd_4612597] using wordTrace_append hprefix tailTrace_4612597
  have hstable : (prefixWord ++ tailWord_4612597).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4612597).length < 2 ^ (prefixWord ++ tailWord_4612597).sum := by decide
  have hdescent : baseEnd_4612597 < baseStart_4612597 := by decide
  rcases family_descends (prefixWord ++ tailWord_4612597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4612614 : List Nat := [6, 2, 1, 1, 1, 1, 2, 2, 3, 1, 3]
def baseStart_4612614 : Nat := 118140960795 + 4612614 * 2 ^ 59
def prefixEnd_4612614 : Nat := 4983230072969 + 3 ^ 40 * 4612614 * 2
def baseEnd_4612614 : Nat := 2368488055657921360211981

theorem tailTrace_4612614 : CollatzResearch.WordTrace tailWord_4612614 prefixEnd_4612614 2368488055657921360211981 := by
  unfold tailWord_4612614
  simp only [CollatzResearch.WordTrace]
  refine ⟨5257370428477960143706153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 112157235807529816399064597 5257370428477960143706153)
  ·
    refine ⟨3943027821358470107779615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5257370428477960143706153 3943027821358470107779615)
    ·
      refine ⟨5914541732037705161669423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3943027821358470107779615 5914541732037705161669423)
      ·
        refine ⟨8871812598056557742504135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5914541732037705161669423 8871812598056557742504135)
        ·
          refine ⟨13307718897084836613756203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8871812598056557742504135 13307718897084836613756203)
          ·
            refine ⟨19961578345627254920634305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13307718897084836613756203 19961578345627254920634305)
            ·
              refine ⟨14971183759220441190475729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19961578345627254920634305 14971183759220441190475729)
              ·
                refine ⟨11228387819415330892856797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14971183759220441190475729 11228387819415330892856797)
                ·
                  refine ⟨4210645432280749084821299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11228387819415330892856797 4210645432280749084821299)
                  ·
                    refine ⟨6315968148421123627231949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4210645432280749084821299 6315968148421123627231949)
                    ·
                      refine ⟨2368488055657921360211981, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6315968148421123627231949 2368488055657921360211981)
                      ·
                        rfl

theorem cell23_4612614_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 2, 2, 3, 1, 3].length) (baseStart_4612614 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4612614 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4612614 prefixEnd_4612614 := by exact prefixLift 4612614
  have htrace : WordTrace (prefixWord ++ tailWord_4612614) baseStart_4612614 baseEnd_4612614 := by
    simpa [prefixWord, tailWord_4612614, baseEnd_4612614] using wordTrace_append hprefix tailTrace_4612614
  have hstable : (prefixWord ++ tailWord_4612614).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4612614).length < 2 ^ (prefixWord ++ tailWord_4612614).sum := by decide
  have hdescent : baseEnd_4612614 < baseStart_4612614 := by decide
  rcases family_descends (prefixWord ++ tailWord_4612614) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4612620 : List Nat := [2, 2, 1, 2, 4, 1, 2, 2, 3, 2, 2]
def baseStart_4612620 : Nat := 118140960795 + 4612620 * 2 ^ 59
def prefixEnd_4612620 : Nat := 4983230072969 + 3 ^ 40 * 4612620 * 2
def baseEnd_4612620 : Nat := 2368491136541848336736953

theorem tailTrace_4612620 : CollatzResearch.WordTrace tailWord_4612620 prefixEnd_4612620 2368491136541848336736953 := by
  unfold tailWord_4612620
  simp only [CollatzResearch.WordTrace]
  refine ⟨84118036274636493811657657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 112157381699515325082210209 84118036274636493811657657)
  ·
    refine ⟨63088527205977370358743243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 84118036274636493811657657 63088527205977370358743243)
    ·
      refine ⟨94632790808966055538114865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63088527205977370358743243 94632790808966055538114865)
      ·
        refine ⟨70974593106724541653586149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 94632790808966055538114865 70974593106724541653586149)
        ·
          refine ⟨13307736207510851560047403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 70974593106724541653586149 13307736207510851560047403)
          ·
            refine ⟨19961604311266277340071105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13307736207510851560047403 19961604311266277340071105)
            ·
              refine ⟨14971203233449708005053329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19961604311266277340071105 14971203233449708005053329)
              ·
                refine ⟨11228402425087281003789997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14971203233449708005053329 11228402425087281003789997)
                ·
                  refine ⟨4210650909407730376421249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11228402425087281003789997 4210650909407730376421249)
                  ·
                    refine ⟨3157988182055797782315937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4210650909407730376421249 3157988182055797782315937)
                    ·
                      refine ⟨2368491136541848336736953, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3157988182055797782315937 2368491136541848336736953)
                      ·
                        rfl

theorem cell23_4612620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 2, 2, 3, 2, 2].length) (baseStart_4612620 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4612620 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4612620 prefixEnd_4612620 := by exact prefixLift 4612620
  have htrace : WordTrace (prefixWord ++ tailWord_4612620) baseStart_4612620 baseEnd_4612620 := by
    simpa [prefixWord, tailWord_4612620, baseEnd_4612620] using wordTrace_append hprefix tailTrace_4612620
  have hstable : (prefixWord ++ tailWord_4612620).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4612620).length < 2 ^ (prefixWord ++ tailWord_4612620).sum := by decide
  have hdescent : baseEnd_4612620 < baseStart_4612620 := by decide
  rcases family_descends (prefixWord ++ tailWord_4612620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4612631 : List Nat := [1, 1, 3, 6, 2, 1, 1, 3, 1, 1, 3]
def baseStart_4612631 : Nat := 118140960795 + 4612631 * 2 ^ 59
def prefixEnd_4612631 : Nat := 4983230072969 + 3 ^ 40 * 4612631 * 2
def baseEnd_4612631 : Nat := 2368496784829047793699403

theorem tailTrace_4612631 : CollatzResearch.WordTrace tailWord_4612631 prefixEnd_4612631 2368496784829047793699403 := by
  unfold tailWord_4612631
  simp only [CollatzResearch.WordTrace]
  refine ⟨168236473752233136501965747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112157649168155424334643831 168236473752233136501965747)
  ·
    refine ⟨252354710628349704752948621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 168236473752233136501965747 252354710628349704752948621)
    ·
      refine ⟨94633016485631139282355733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 252354710628349704752948621 94633016485631139282355733)
      ·
        refine ⟨4435922647763959653860425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 94633016485631139282355733 4435922647763959653860425)
        ·
          refine ⟨3326941985822969740395319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4435922647763959653860425 3326941985822969740395319)
          ·
            refine ⟨4990412978734454610592979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3326941985822969740395319 4990412978734454610592979)
            ·
              refine ⟨7485619468101681915889469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4990412978734454610592979 7485619468101681915889469)
              ·
                refine ⟨2807107300538130718458551, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7485619468101681915889469 2807107300538130718458551)
                ·
                  refine ⟨4210660950807196077687827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2807107300538130718458551 4210660950807196077687827)
                  ·
                    refine ⟨6315991426210794116531741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4210660950807196077687827 6315991426210794116531741)
                    ·
                      refine ⟨2368496784829047793699403, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6315991426210794116531741 2368496784829047793699403)
                      ·
                        rfl

theorem cell23_4612631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 2, 1, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 2, 1, 1, 3, 1, 1, 3].length) (baseStart_4612631 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4612631 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4612631 prefixEnd_4612631 := by exact prefixLift 4612631
  have htrace : WordTrace (prefixWord ++ tailWord_4612631) baseStart_4612631 baseEnd_4612631 := by
    simpa [prefixWord, tailWord_4612631, baseEnd_4612631] using wordTrace_append hprefix tailTrace_4612631
  have hstable : (prefixWord ++ tailWord_4612631).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4612631).length < 2 ^ (prefixWord ++ tailWord_4612631).sum := by decide
  have hdescent : baseEnd_4612631 < baseStart_4612631 := by decide
  rcases family_descends (prefixWord ++ tailWord_4612631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4612639 : List Nat := [1, 1, 2, 4, 1, 1, 1, 2, 1, 9]
def baseStart_4612639 : Nat := 118140960795 + 4612639 * 2 ^ 59
def prefixEnd_4612639 : Nat := 4983230072969 + 3 ^ 40 * 4612639 * 2
def baseEnd_4612639 : Nat := 789500297558094587466455

theorem tailTrace_4612639 : CollatzResearch.WordTrace tailWord_4612639 prefixEnd_4612639 789500297558094587466455 := by
  unfold tailWord_4612639
  simp only [CollatzResearch.WordTrace]
  refine ⟨168236765536204153868256971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112157843690802769245504647 168236765536204153868256971)
  ·
    refine ⟨252355148304306230802385457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 168236765536204153868256971 252355148304306230802385457)
    ·
      refine ⟨189266361228229673101789093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 252355148304306230802385457 189266361228229673101789093)
      ·
        refine ⟨35487442730293063706585455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 189266361228229673101789093 35487442730293063706585455)
        ·
          refine ⟨53231164095439595559878183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35487442730293063706585455 53231164095439595559878183)
          ·
            refine ⟨79846746143159393339817275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53231164095439595559878183 79846746143159393339817275)
            ·
              refine ⟨119770119214739090009725913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 79846746143159393339817275 119770119214739090009725913)
              ·
                refine ⟨89827589411054317507294435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 119770119214739090009725913 89827589411054317507294435)
                ·
                  refine ⟨134741384116581476260941653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 89827589411054317507294435 134741384116581476260941653)
                  ·
                    refine ⟨789500297558094587466455, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 134741384116581476260941653 789500297558094587466455)
                    ·
                      rfl

theorem cell23_4612639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 1, 2, 1, 9].length) (baseStart_4612639 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4612639 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4612639 prefixEnd_4612639 := by exact prefixLift 4612639
  have htrace : WordTrace (prefixWord ++ tailWord_4612639) baseStart_4612639 baseEnd_4612639 := by
    simpa [prefixWord, tailWord_4612639, baseEnd_4612639] using wordTrace_append hprefix tailTrace_4612639
  have hstable : (prefixWord ++ tailWord_4612639).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4612639).length < 2 ^ (prefixWord ++ tailWord_4612639).sum := by decide
  have hdescent : baseEnd_4612639 < baseStart_4612639 := by decide
  rcases family_descends (prefixWord ++ tailWord_4612639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4612654 : List Nat := [4, 1, 3, 1, 3, 2, 1, 1, 3, 2, 2]
def baseStart_4612654 : Nat := 118140960795 + 4612654 * 2 ^ 59
def prefixEnd_4612654 : Nat := 4983230072969 + 3 ^ 40 * 4612654 * 2
def baseEnd_4612654 : Nat := 2368508594884101203711797

theorem tailTrace_4612654 : CollatzResearch.WordTrace tailWord_4612654 prefixEnd_4612654 2368508594884101203711797 := by
  unfold tailWord_4612654
  simp only [CollatzResearch.WordTrace]
  refine ⟨21029664078893726428756627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 112158208420766540953368677 21029664078893726428756627)
  ·
    refine ⟨31544496118340589643134941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21029664078893726428756627 31544496118340589643134941)
    ·
      refine ⟨11829186044377721116175603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31544496118340589643134941 11829186044377721116175603)
      ·
        refine ⟨17743779066566581674263405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11829186044377721116175603 17743779066566581674263405)
        ·
          refine ⟨6653917149962468127848777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17743779066566581674263405 6653917149962468127848777)
          ·
            refine ⟨4990437862471851095886583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6653917149962468127848777 4990437862471851095886583)
            ·
              refine ⟨7485656793707776643829875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4990437862471851095886583 7485656793707776643829875)
              ·
                refine ⟨11228485190561664965744813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7485656793707776643829875 11228485190561664965744813)
                ·
                  refine ⟨4210681946460624362154305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11228485190561664965744813 4210681946460624362154305)
                  ·
                    refine ⟨3158011459845468271615729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4210681946460624362154305 3158011459845468271615729)
                    ·
                      refine ⟨2368508594884101203711797, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3158011459845468271615729 2368508594884101203711797)
                      ·
                        rfl

theorem cell23_4612654_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 3, 2, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 3, 2, 1, 1, 3, 2, 2].length) (baseStart_4612654 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4612654 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4612654 prefixEnd_4612654 := by exact prefixLift 4612654
  have htrace : WordTrace (prefixWord ++ tailWord_4612654) baseStart_4612654 baseEnd_4612654 := by
    simpa [prefixWord, tailWord_4612654, baseEnd_4612654] using wordTrace_append hprefix tailTrace_4612654
  have hstable : (prefixWord ++ tailWord_4612654).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4612654).length < 2 ^ (prefixWord ++ tailWord_4612654).sum := by decide
  have hdescent : baseEnd_4612654 < baseStart_4612654 := by decide
  rcases family_descends (prefixWord ++ tailWord_4612654) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4612660 : List Nat := [2, 5, 1, 3, 1, 1, 2, 8]
def baseStart_4612660 : Nat := 118140960795 + 4612660 * 2 ^ 59
def prefixEnd_4612660 : Nat := 4983230072969 + 3 ^ 40 * 4612660 * 2
def baseEnd_4612660 : Nat := 87722654658075117786547

theorem tailTrace_4612660 : CollatzResearch.WordTrace tailWord_4612660 prefixEnd_4612660 87722654658075117786547 := by
  unfold tailWord_4612660
  simp only [CollatzResearch.WordTrace]
  refine ⟨84118765734564037227385717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 112158354312752049636514289 84118765734564037227385717)
  ·
    refine ⟨7886134287615378490067411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 84118765734564037227385717 7886134287615378490067411)
    ·
      refine ⟨11829201431423067735101117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7886134287615378490067411 11829201431423067735101117)
      ·
        refine ⟨4435950536783650400662919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11829201431423067735101117 4435950536783650400662919)
        ·
          refine ⟨6653925805175475600994379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4435950536783650400662919 6653925805175475600994379)
          ·
            refine ⟨9980888707763213401491569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6653925805175475600994379 9980888707763213401491569)
            ·
              refine ⟨7485666530822410051118677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9980888707763213401491569 7485666530822410051118677)
              ·
                refine ⟨87722654658075117786547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 7485666530822410051118677 87722654658075117786547)
                ·
                  rfl

theorem cell23_4612660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 1, 1, 2, 8].length) (baseStart_4612660 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4612660 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4612660 prefixEnd_4612660 := by exact prefixLift 4612660
  have htrace : WordTrace (prefixWord ++ tailWord_4612660) baseStart_4612660 baseEnd_4612660 := by
    simpa [prefixWord, tailWord_4612660, baseEnd_4612660] using wordTrace_append hprefix tailTrace_4612660
  have hstable : (prefixWord ++ tailWord_4612660).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4612660).length < 2 ^ (prefixWord ++ tailWord_4612660).sum := by decide
  have hdescent : baseEnd_4612660 < baseStart_4612660 := by decide
  rcases family_descends (prefixWord ++ tailWord_4612660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4612663 : List Nat := [1, 1, 3, 1, 2, 3, 2, 2, 3, 3, 2]
def baseStart_4612663 : Nat := 118140960795 + 4612663 * 2 ^ 59
def prefixEnd_4612663 : Nat := 4983230072969 + 3 ^ 40 * 4612663 * 2
def baseEnd_4612663 : Nat := 2368513216209991668499255

theorem tailTrace_4612663 : CollatzResearch.WordTrace tailWord_4612663 prefixEnd_4612663 2368513216209991668499255 := by
  unfold tailWord_4612663
  simp only [CollatzResearch.WordTrace]
  refine ⟨168237640888117205967130643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112158427258744803978087095 168237640888117205967130643)
  ·
    refine ⟨252356461332175808950695965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 168237640888117205967130643 252356461332175808950695965)
    ·
      refine ⟨94633672999565928356510987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 252356461332175808950695965 94633672999565928356510987)
      ·
        refine ⟨141950509499348892534766481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 94633672999565928356510987 141950509499348892534766481)
        ·
          refine ⟨106462882124511669401074861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 141950509499348892534766481 106462882124511669401074861)
          ·
            refine ⟨39923580796691876025403073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 106462882124511669401074861 39923580796691876025403073)
            ·
              refine ⟨29942685597518907019052305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 39923580796691876025403073 29942685597518907019052305)
              ·
                refine ⟨22457014198139180264289229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29942685597518907019052305 22457014198139180264289229)
                ·
                  refine ⟨8421380324302192599108461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22457014198139180264289229 8421380324302192599108461)
                  ·
                    refine ⟨3158017621613322224665673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8421380324302192599108461 3158017621613322224665673)
                    ·
                      refine ⟨2368513216209991668499255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3158017621613322224665673 2368513216209991668499255)
                      ·
                        rfl

theorem cell23_4612663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 2, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 2, 2, 3, 3, 2].length) (baseStart_4612663 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4612663 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4612663 prefixEnd_4612663 := by exact prefixLift 4612663
  have htrace : WordTrace (prefixWord ++ tailWord_4612663) baseStart_4612663 baseEnd_4612663 := by
    simpa [prefixWord, tailWord_4612663, baseEnd_4612663] using wordTrace_append hprefix tailTrace_4612663
  have hstable : (prefixWord ++ tailWord_4612663).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4612663).length < 2 ^ (prefixWord ++ tailWord_4612663).sum := by decide
  have hdescent : baseEnd_4612663 < baseStart_4612663 := by decide
  rcases family_descends (prefixWord ++ tailWord_4612663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4612693 : List Nat := [1, 3, 2, 2, 1, 1, 3, 1, 3, 4, 2]
def baseStart_4612693 : Nat := 118140960795 + 4612693 * 2 ^ 59
def prefixEnd_4612693 : Nat := 4983230072969 + 3 ^ 40 * 4612693 * 2
def baseEnd_4612693 : Nat := 2368528620629626551124117

theorem tailTrace_4612693 : CollatzResearch.WordTrace tailWord_4612693 prefixEnd_4612693 2368528620629626551124117 := by
  unfold tailWord_4612693
  simp only [CollatzResearch.WordTrace]
  refine ⟨168238735078008521090722733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112159156718672347393815155 168238735078008521090722733)
  ·
    refine ⟨63089525654253195409021025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 168238735078008521090722733 63089525654253195409021025)
    ·
      refine ⟨47317144240689896556765769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 63089525654253195409021025 47317144240689896556765769)
      ·
        refine ⟨35487858180517422417574327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47317144240689896556765769 35487858180517422417574327)
        ·
          refine ⟨53231787270776133626361491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35487858180517422417574327 53231787270776133626361491)
          ·
            refine ⟨79847680906164200439542237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53231787270776133626361491 79847680906164200439542237)
            ·
              refine ⟨29942880339811575164828339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 79847680906164200439542237 29942880339811575164828339)
              ·
                refine ⟨44914320509717362747242509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29942880339811575164828339 44914320509717362747242509)
                ·
                  refine ⟨16842870191144011030215941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 44914320509717362747242509 16842870191144011030215941)
                  ·
                    refine ⟨3158038160839502068165489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16842870191144011030215941 3158038160839502068165489)
                    ·
                      refine ⟨2368528620629626551124117, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3158038160839502068165489 2368528620629626551124117)
                      ·
                        rfl

theorem cell23_4612693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 3, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 3, 1, 3, 4, 2].length) (baseStart_4612693 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4612693 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4612693 prefixEnd_4612693 := by exact prefixLift 4612693
  have htrace : WordTrace (prefixWord ++ tailWord_4612693) baseStart_4612693 baseEnd_4612693 := by
    simpa [prefixWord, tailWord_4612693, baseEnd_4612693] using wordTrace_append hprefix tailTrace_4612693
  have hstable : (prefixWord ++ tailWord_4612693).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4612693).length < 2 ^ (prefixWord ++ tailWord_4612693).sum := by decide
  have hdescent : baseEnd_4612693 < baseStart_4612693 := by decide
  rcases family_descends (prefixWord ++ tailWord_4612693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4612696 : List Nat := [2, 1, 2, 2, 1, 2, 4, 1, 2, 1, 5]
def baseStart_4612696 : Nat := 118140960795 + 4612696 * 2 ^ 59
def prefixEnd_4612696 : Nat := 4983230072969 + 3 ^ 40 * 4612696 * 2
def baseEnd_4612696 : Nat := 2368530161071590039386603

theorem tailTrace_4612696 : CollatzResearch.WordTrace tailWord_4612696 prefixEnd_4612696 2368530161071590039386603 := by
  unfold tailWord_4612696
  simp only [CollatzResearch.WordTrace]
  refine ⟨84119422248498826301540971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 112159229664665101735387961 84119422248498826301540971)
  ·
    refine ⟨126179133372748239452311457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84119422248498826301540971 126179133372748239452311457)
    ·
      refine ⟨94634350029561179589233593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 126179133372748239452311457 94634350029561179589233593)
      ·
        refine ⟨70975762522170884691925195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 94634350029561179589233593 70975762522170884691925195)
        ·
          refine ⟨106463643783256327037887793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 70975762522170884691925195 106463643783256327037887793)
          ·
            refine ⟨79847732837442245278415845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 106463643783256327037887793 79847732837442245278415845)
            ·
              refine ⟨14971449907020420989702971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 79847732837442245278415845 14971449907020420989702971)
              ·
                refine ⟨22457174860530631484554457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14971449907020420989702971 22457174860530631484554457)
                ·
                  refine ⟨16842881145397973613415843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22457174860530631484554457 16842881145397973613415843)
                  ·
                    refine ⟨25264321718096960420123765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16842881145397973613415843 25264321718096960420123765)
                    ·
                      refine ⟨2368530161071590039386603, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25264321718096960420123765 2368530161071590039386603)
                      ·
                        rfl

theorem cell23_4612696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 4, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 4, 1, 2, 1, 5].length) (baseStart_4612696 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4612696 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4612696 prefixEnd_4612696 := by exact prefixLift 4612696
  have htrace : WordTrace (prefixWord ++ tailWord_4612696) baseStart_4612696 baseEnd_4612696 := by
    simpa [prefixWord, tailWord_4612696, baseEnd_4612696] using wordTrace_append hprefix tailTrace_4612696
  have hstable : (prefixWord ++ tailWord_4612696).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4612696).length < 2 ^ (prefixWord ++ tailWord_4612696).sum := by decide
  have hdescent : baseEnd_4612696 < baseStart_4612696 := by decide
  rcases family_descends (prefixWord ++ tailWord_4612696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4612733 : List Nat := [1, 4, 1, 1, 5, 1, 1, 2, 7]
def baseStart_4612733 : Nat := 118140960795 + 4612733 * 2 ^ 59
def prefixEnd_4612733 : Nat := 4983230072969 + 3 ^ 40 * 4612733 * 2
def baseEnd_4612733 : Nat := 263172128872867377180437

theorem tailTrace_4612733 : CollatzResearch.WordTrace tailWord_4612733 prefixEnd_4612733 263172128872867377180437 := by
  unfold tailWord_4612733
  simp only [CollatzResearch.WordTrace]
  refine ⟨168240193997863607922178853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112160129331909071948119235 168240193997863607922178853)
  ·
    refine ⟨31545036374599426485408535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 168240193997863607922178853 31545036374599426485408535)
    ·
      refine ⟨47317554561899139728112803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31545036374599426485408535 47317554561899139728112803)
      ·
        refine ⟨70976331842848709592169205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47317554561899139728112803 70976331842848709592169205)
        ·
          refine ⟨6654031110267066524265863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 70976331842848709592169205 6654031110267066524265863)
          ·
            refine ⟨9981046665400599786398795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6654031110267066524265863 9981046665400599786398795)
            ·
              refine ⟨14971569998100899679598193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9981046665400599786398795 14971569998100899679598193)
              ·
                refine ⟨11228677498575674759698645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14971569998100899679598193 11228677498575674759698645)
                ·
                  refine ⟨263172128872867377180437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11228677498575674759698645 263172128872867377180437)
                  ·
                    rfl

theorem cell23_4612733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 5, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 5, 1, 1, 2, 7].length) (baseStart_4612733 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4612733 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4612733 prefixEnd_4612733 := by exact prefixLift 4612733
  have htrace : WordTrace (prefixWord ++ tailWord_4612733) baseStart_4612733 baseEnd_4612733 := by
    simpa [prefixWord, tailWord_4612733, baseEnd_4612733] using wordTrace_append hprefix tailTrace_4612733
  have hstable : (prefixWord ++ tailWord_4612733).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4612733).length < 2 ^ (prefixWord ++ tailWord_4612733).sum := by decide
  have hdescent : baseEnd_4612733 < baseStart_4612733 := by decide
  rcases family_descends (prefixWord ++ tailWord_4612733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4612750 : List Nat := [4, 1, 1, 3, 1, 1, 4, 3, 5]
def baseStart_4612750 : Nat := 118140960795 + 4612750 * 2 ^ 59
def prefixEnd_4612750 : Nat := 4983230072969 + 3 ^ 40 * 4612750 * 2
def baseEnd_4612750 : Nat := 263173098780770314234595

theorem tailTrace_4612750 : CollatzResearch.WordTrace tailWord_4612750 prefixEnd_4612750 263173098780770314234595 := by
  unfold tailWord_4612750
  simp only [CollatzResearch.WordTrace]
  refine ⟨21030101754850252478193463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 112160542692534679883698469 21030101754850252478193463)
  ·
    refine ⟨31545152632275378717290195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21030101754850252478193463 31545152632275378717290195)
    ·
      refine ⟨47317728948413068075935293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31545152632275378717290195 47317728948413068075935293)
      ·
        refine ⟨17744148355654900528475735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 47317728948413068075935293 17744148355654900528475735)
        ·
          refine ⟨26616222533482350792713603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17744148355654900528475735 26616222533482350792713603)
          ·
            refine ⟨39924333800223526189070405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26616222533482350792713603 39924333800223526189070405)
            ·
              refine ⟨7485812587541911160450701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 39924333800223526189070405 7485812587541911160450701)
              ·
                refine ⟨2807179720328216685169013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7485812587541911160450701 2807179720328216685169013)
                ·
                  refine ⟨263173098780770314234595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2807179720328216685169013 263173098780770314234595)
                  ·
                    rfl

theorem cell23_4612750_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 4, 3, 5].length) (baseStart_4612750 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4612750 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4612750 prefixEnd_4612750 := by exact prefixLift 4612750
  have htrace : WordTrace (prefixWord ++ tailWord_4612750) baseStart_4612750 baseEnd_4612750 := by
    simpa [prefixWord, tailWord_4612750, baseEnd_4612750] using wordTrace_append hprefix tailTrace_4612750
  have hstable : (prefixWord ++ tailWord_4612750).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4612750).length < 2 ^ (prefixWord ++ tailWord_4612750).sum := by decide
  have hdescent : baseEnd_4612750 < baseStart_4612750 := by decide
  rcases family_descends (prefixWord ++ tailWord_4612750) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4612778 : List Nat := [3, 1, 5, 2, 1, 1, 3, 1, 2, 2, 2]
def baseStart_4612778 : Nat := 118140960795 + 4612778 * 2 ^ 59
def prefixEnd_4612778 : Nat := 4983230072969 + 3 ^ 40 * 4612778 * 2
def baseEnd_4612778 : Nat := 2368572266485258718561227

theorem tailTrace_4612778 : CollatzResearch.WordTrace tailWord_4612778 prefixEnd_4612778 2368572266485258718561227 := by
  unfold tailWord_4612778
  simp only [CollatzResearch.WordTrace]
  refine ⟨42060458820675145151891747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 112161223521800387071711325 42060458820675145151891747)
  ·
    refine ⟨63090688231012717727837621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42060458820675145151891747 63090688231012717727837621)
    ·
      refine ⟨5914752021657442286984777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 63090688231012717727837621 5914752021657442286984777)
      ·
        refine ⟨4436064016243081715238583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5914752021657442286984777 4436064016243081715238583)
        ·
          refine ⟨6654096024364622572857875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4436064016243081715238583 6654096024364622572857875)
          ·
            refine ⟨9981144036546933859286813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6654096024364622572857875 9981144036546933859286813)
            ·
              refine ⟨3742929013705100197232555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9981144036546933859286813 3742929013705100197232555)
              ·
                refine ⟨5614393520557650295848833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3742929013705100197232555 5614393520557650295848833)
                ·
                  refine ⟨4210795140418237721886625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5614393520557650295848833 4210795140418237721886625)
                  ·
                    refine ⟨3158096355313678291414969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4210795140418237721886625 3158096355313678291414969)
                    ·
                      refine ⟨2368572266485258718561227, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3158096355313678291414969 2368572266485258718561227)
                      ·
                        rfl

theorem cell23_4612778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 1, 1, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 1, 1, 3, 1, 2, 2, 2].length) (baseStart_4612778 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4612778 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4612778 prefixEnd_4612778 := by exact prefixLift 4612778
  have htrace : WordTrace (prefixWord ++ tailWord_4612778) baseStart_4612778 baseEnd_4612778 := by
    simpa [prefixWord, tailWord_4612778, baseEnd_4612778] using wordTrace_append hprefix tailTrace_4612778
  have hstable : (prefixWord ++ tailWord_4612778).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4612778).length < 2 ^ (prefixWord ++ tailWord_4612778).sum := by decide
  have hdescent : baseEnd_4612778 < baseStart_4612778 := by decide
  rcases family_descends (prefixWord ++ tailWord_4612778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4612801 : List Nat := [1, 2, 6, 2, 2, 1, 1, 3, 5]
def baseStart_4612801 : Nat := 118140960795 + 4612801 * 2 ^ 59
def prefixEnd_4612801 : Nat := 4983230072969 + 3 ^ 40 * 4612801 * 2
def baseEnd_4612801 : Nat := 263176008504479125397069

theorem tailTrace_4612801 : CollatzResearch.WordTrace tailWord_4612801 prefixEnd_4612801 263176008504479125397069 := by
  unfold tailWord_4612801
  simp only [CollatzResearch.WordTrace]
  refine ⟨168242674161617255535654257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112161782774411503690436171 168242674161617255535654257)
  ·
    refine ⟨126182005621212941651740693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 168242674161617255535654257 126182005621212941651740693)
    ·
      refine ⟨5914781513494356639925345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 126182005621212941651740693 5914781513494356639925345)
      ·
        refine ⟨4436086135120767479944009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5914781513494356639925345 4436086135120767479944009)
        ·
          refine ⟨3327064601340575609958007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4436086135120767479944009 3327064601340575609958007)
          ·
            refine ⟨4990596902010863414937011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3327064601340575609958007 4990596902010863414937011)
            ·
              refine ⟨7485895353016295122405517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4990596902010863414937011 7485895353016295122405517)
              ·
                refine ⟨2807210757381110670902069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7485895353016295122405517 2807210757381110670902069)
                ·
                  refine ⟨263176008504479125397069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2807210757381110670902069 263176008504479125397069)
                  ·
                    rfl

theorem cell23_4612801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 2, 1, 1, 3, 5].length) (baseStart_4612801 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4612801 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4612801 prefixEnd_4612801 := by exact prefixLift 4612801
  have htrace : WordTrace (prefixWord ++ tailWord_4612801) baseStart_4612801 baseEnd_4612801 := by
    simpa [prefixWord, tailWord_4612801, baseEnd_4612801] using wordTrace_append hprefix tailTrace_4612801
  have hstable : (prefixWord ++ tailWord_4612801).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4612801).length < 2 ^ (prefixWord ++ tailWord_4612801).sum := by decide
  have hdescent : baseEnd_4612801 < baseStart_4612801 := by decide
  rcases family_descends (prefixWord ++ tailWord_4612801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4612840 : List Nat := [2, 1, 4, 1, 4, 1, 1, 3, 6]
def baseStart_4612840 : Nat := 118140960795 + 4612840 * 2 ^ 59
def prefixEnd_4612840 : Nat := 4983230072969 + 3 ^ 40 * 4612840 * 2
def baseEnd_4612840 : Nat := 263178233587315275109549

theorem tailTrace_4612840 : CollatzResearch.WordTrace tailWord_4612840 prefixEnd_4612840 263178233587315275109549 := by
  unfold tailWord_4612840
  simp only [CollatzResearch.WordTrace]
  refine ⟨84122048304237982598161987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 112162731072317310130882649 84122048304237982598161987)
  ·
    refine ⟨126183072456356973897242981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84122048304237982598161987 126183072456356973897242981)
    ·
      refine ⟨23659326085566932605733059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 126183072456356973897242981 23659326085566932605733059)
      ·
        refine ⟨35488989128350398908599589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23659326085566932605733059 35488989128350398908599589)
        ·
          refine ⟨6654185461565699795362423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 35488989128350398908599589 6654185461565699795362423)
          ·
            refine ⟨9981278192348549693043635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6654185461565699795362423 9981278192348549693043635)
            ·
              refine ⟨14971917288522824539565453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9981278192348549693043635 14971917288522824539565453)
              ·
                refine ⟨5614468983196059202337045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14971917288522824539565453 5614468983196059202337045)
                ·
                  refine ⟨263178233587315275109549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5614468983196059202337045 263178233587315275109549)
                  ·
                    rfl

theorem cell23_4612840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 4, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 4, 1, 1, 3, 6].length) (baseStart_4612840 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4612840 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4612840 prefixEnd_4612840 := by exact prefixLift 4612840
  have htrace : WordTrace (prefixWord ++ tailWord_4612840) baseStart_4612840 baseEnd_4612840 := by
    simpa [prefixWord, tailWord_4612840, baseEnd_4612840] using wordTrace_append hprefix tailTrace_4612840
  have hstable : (prefixWord ++ tailWord_4612840).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4612840).length < 2 ^ (prefixWord ++ tailWord_4612840).sum := by decide
  have hdescent : baseEnd_4612840 < baseStart_4612840 := by decide
  rcases family_descends (prefixWord ++ tailWord_4612840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4612867 : List Nat := [1, 1, 1, 3, 2, 2, 1, 7, 1, 1, 3]
def baseStart_4612867 : Nat := 118140960795 + 4612867 * 2 ^ 59
def prefixEnd_4612867 : Nat := 4983230072969 + 3 ^ 40 * 4612867 * 2
def baseEnd_4612867 : Nat := 2368617966263508870348317

theorem tailTrace_4612867 : CollatzResearch.WordTrace tailWord_4612867 prefixEnd_4612867 2368617966263508870348317 := by
  unfold tailWord_4612867
  simp only [CollatzResearch.WordTrace]
  refine ⟨168245081379378148807556855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112163387586252099205037903 168245081379378148807556855)
  ·
    refine ⟨252367622069067223211335283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 168245081379378148807556855 252367622069067223211335283)
    ·
      refine ⟨378551433103600834817002925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 252367622069067223211335283 378551433103600834817002925)
      ·
        refine ⟨141956787413850313056376097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 378551433103600834817002925 141956787413850313056376097)
        ·
          refine ⟨106467590560387734792282073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 141956787413850313056376097 106467590560387734792282073)
          ·
            refine ⟨79850692920290801094211555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 106467590560387734792282073 79850692920290801094211555)
            ·
              refine ⟨119776039380436201641317333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 79850692920290801094211555 119776039380436201641317333)
              ·
                refine ⟨2807250922978973475968375, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 119776039380436201641317333 2807250922978973475968375)
                ·
                  refine ⟨4210876384468460213952563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2807250922978973475968375 4210876384468460213952563)
                  ·
                    refine ⟨6316314576702690320928845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4210876384468460213952563 6316314576702690320928845)
                    ·
                      refine ⟨2368617966263508870348317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6316314576702690320928845 2368617966263508870348317)
                      ·
                        rfl

theorem cell23_4612867_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 1, 7, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 1, 7, 1, 1, 3].length) (baseStart_4612867 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4612867 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4612867 prefixEnd_4612867 := by exact prefixLift 4612867
  have htrace : WordTrace (prefixWord ++ tailWord_4612867) baseStart_4612867 baseEnd_4612867 := by
    simpa [prefixWord, tailWord_4612867, baseEnd_4612867] using wordTrace_append hprefix tailTrace_4612867
  have hstable : (prefixWord ++ tailWord_4612867).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4612867).length < 2 ^ (prefixWord ++ tailWord_4612867).sum := by decide
  have hdescent : baseEnd_4612867 < baseStart_4612867 := by decide
  rcases family_descends (prefixWord ++ tailWord_4612867) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4612918 : List Nat := [5, 1, 2, 2, 2, 1, 2, 3, 1, 1, 3]
def baseStart_4612918 : Nat := 118140960795 + 4612918 * 2 ^ 59
def prefixEnd_4612918 : Nat := 4983230072969 + 3 ^ 40 * 4612918 * 2
def baseEnd_4612918 : Nat := 2368644153776888170810583

theorem tailTrace_4612918 : CollatzResearch.WordTrace tailWord_4612918 prefixEnd_4612918 2368644153776888170810583 := by
  unfold tailWord_4612918
  simp only [CollatzResearch.WordTrace]
  refine ⟨10515433843887086532353963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 112164627668128923011775605 10515433843887086532353963)
  ·
    refine ⟨15773150765830629798530945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10515433843887086532353963 15773150765830629798530945)
    ·
      refine ⟨11829863074372972348898209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15773150765830629798530945 11829863074372972348898209)
      ·
        refine ⟨8872397305779729261673657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11829863074372972348898209 8872397305779729261673657)
        ·
          refine ⟨6654297979334796946255243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8872397305779729261673657 6654297979334796946255243)
          ·
            refine ⟨9981446969002195419382865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6654297979334796946255243 9981446969002195419382865)
            ·
              refine ⟨7486085226751646564537149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9981446969002195419382865 7486085226751646564537149)
              ·
                refine ⟨2807281960031867461701431, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7486085226751646564537149 2807281960031867461701431)
                ·
                  refine ⟨4210922940047801192552147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2807281960031867461701431 4210922940047801192552147)
                  ·
                    refine ⟨6316384410071701788828221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4210922940047801192552147 6316384410071701788828221)
                    ·
                      refine ⟨2368644153776888170810583, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6316384410071701788828221 2368644153776888170810583)
                      ·
                        rfl

theorem cell23_4612918_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 2, 1, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 2, 1, 2, 3, 1, 1, 3].length) (baseStart_4612918 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4612918 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4612918 prefixEnd_4612918 := by exact prefixLift 4612918
  have htrace : WordTrace (prefixWord ++ tailWord_4612918) baseStart_4612918 baseEnd_4612918 := by
    simpa [prefixWord, tailWord_4612918, baseEnd_4612918] using wordTrace_append hprefix tailTrace_4612918
  have hstable : (prefixWord ++ tailWord_4612918).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4612918).length < 2 ^ (prefixWord ++ tailWord_4612918).sum := by decide
  have hdescent : baseEnd_4612918 < baseStart_4612918 := by decide
  rcases family_descends (prefixWord ++ tailWord_4612918) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4612927 : List Nat := [1, 1, 2, 2, 5, 2, 1, 3, 1, 2, 3]
def baseStart_4612927 : Nat := 118140960795 + 4612927 * 2 ^ 59
def prefixEnd_4612927 : Nat := 4983230072969 + 3 ^ 40 * 4612927 * 2
def baseEnd_4612927 : Nat := 2368648775102778635598041

theorem tailTrace_4612927 : CollatzResearch.WordTrace tailWord_4612927 prefixEnd_4612927 2368648775102778635598041 := by
  unfold tailWord_4612927
  simp only [CollatzResearch.WordTrace]
  refine ⟨168247269759160779054741035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112164846506107186036494023 168247269759160779054741035)
  ·
    refine ⟨252370904638741168582111553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 168247269759160779054741035 252370904638741168582111553)
    ·
      refine ⟨189278178479055876436583665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 252370904638741168582111553 189278178479055876436583665)
      ·
        refine ⟨141958633859291907327437749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 189278178479055876436583665 141958633859291907327437749)
        ·
          refine ⟨13308621924308616311947289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 141958633859291907327437749 13308621924308616311947289)
          ·
            refine ⟨9981466443231462233960467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13308621924308616311947289 9981466443231462233960467)
            ·
              refine ⟨14972199664847193350940701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9981466443231462233960467 14972199664847193350940701)
              ·
                refine ⟨5614574874317697506602763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14972199664847193350940701 5614574874317697506602763)
                ·
                  refine ⟨8421862311476546259904145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5614574874317697506602763 8421862311476546259904145)
                  ·
                    refine ⟨6316396733607409694928109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8421862311476546259904145 6316396733607409694928109)
                    ·
                      refine ⟨2368648775102778635598041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6316396733607409694928109 2368648775102778635598041)
                      ·
                        rfl

theorem cell23_4612927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 2, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 2, 1, 3, 1, 2, 3].length) (baseStart_4612927 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4612927 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4612927 prefixEnd_4612927 := by exact prefixLift 4612927
  have htrace : WordTrace (prefixWord ++ tailWord_4612927) baseStart_4612927 baseEnd_4612927 := by
    simpa [prefixWord, tailWord_4612927, baseEnd_4612927] using wordTrace_append hprefix tailTrace_4612927
  have hstable : (prefixWord ++ tailWord_4612927).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4612927).length < 2 ^ (prefixWord ++ tailWord_4612927).sum := by decide
  have hdescent : baseEnd_4612927 < baseStart_4612927 := by decide
  rcases family_descends (prefixWord ++ tailWord_4612927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4613018 : List Nat := [3, 1, 1, 4, 4, 1, 1, 2, 1, 3, 2]
def baseStart_4613018 : Nat := 118140960795 + 4613018 * 2 ^ 59
def prefixEnd_4613018 : Nat := 4983230072969 + 3 ^ 40 * 4613018 * 2
def baseEnd_4613018 : Nat := 2368695501842337779560123

theorem tailTrace_4613018 : CollatzResearch.WordTrace tailWord_4613018 prefixEnd_4613018 2368695501842337779560123 := by
  unfold tailWord_4613018
  simp only [CollatzResearch.WordTrace]
  refine ⟨42062647200457775399075927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 112167059201220734397535805 42062647200457775399075927)
  ·
    refine ⟨63093970800686663098613891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42062647200457775399075927 63093970800686663098613891)
    ·
      refine ⟨94640956201029994647920837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63093970800686663098613891 94640956201029994647920837)
      ·
        refine ⟨17745179287693123996485157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 94640956201029994647920837 17745179287693123996485157)
        ·
          refine ⟨3327221116442460749340967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 17745179287693123996485157 3327221116442460749340967)
          ·
            refine ⟨4990831674663691124011451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3327221116442460749340967 4990831674663691124011451)
            ·
              refine ⟨7486247511995536686017177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4990831674663691124011451 7486247511995536686017177)
              ·
                refine ⟨5614685633996652514512883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7486247511995536686017177 5614685633996652514512883)
                ·
                  refine ⟨8422028450994978771769325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5614685633996652514512883 8422028450994978771769325)
                  ·
                    refine ⟨3158260669123117039413497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8422028450994978771769325 3158260669123117039413497)
                    ·
                      refine ⟨2368695501842337779560123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3158260669123117039413497 2368695501842337779560123)
                      ·
                        rfl

theorem cell23_4613018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 4, 1, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 4, 1, 1, 2, 1, 3, 2].length) (baseStart_4613018 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4613018 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4613018 prefixEnd_4613018 := by exact prefixLift 4613018
  have htrace : WordTrace (prefixWord ++ tailWord_4613018) baseStart_4613018 baseEnd_4613018 := by
    simpa [prefixWord, tailWord_4613018, baseEnd_4613018] using wordTrace_append hprefix tailTrace_4613018
  have hstable : (prefixWord ++ tailWord_4613018).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4613018).length < 2 ^ (prefixWord ++ tailWord_4613018).sum := by decide
  have hdescent : baseEnd_4613018 < baseStart_4613018 := by decide
  rcases family_descends (prefixWord ++ tailWord_4613018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4613050 : List Nat := [3, 1, 1, 1, 2, 1, 3, 4, 2, 5]
def baseStart_4613050 : Nat := 118140960795 + 4613050 * 2 ^ 59
def prefixEnd_4613050 : Nat := 4983230072969 + 3 ^ 40 * 4613050 * 2
def baseEnd_4613050 : Nat := 789570644407760551453325

theorem tailTrace_4613050 : CollatzResearch.WordTrace tailWord_4613050 prefixEnd_4613050 789570644407760551453325 := by
  unfold tailWord_4613050
  simp only [CollatzResearch.WordTrace]
  refine ⟨42062938984428792765367151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 112167837291810114040979069 42062938984428792765367151)
  ·
    refine ⟨63094408476643189148050727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42062938984428792765367151 63094408476643189148050727)
    ·
      refine ⟨94641612714964783722076091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63094408476643189148050727 94641612714964783722076091)
      ·
        refine ⟨141962419072447175583114137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 94641612714964783722076091 141962419072447175583114137)
        ·
          refine ⟨106471814304335381687335603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 141962419072447175583114137 106471814304335381687335603)
          ·
            refine ⟨159707721456503072531003405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 106471814304335381687335603 159707721456503072531003405)
            ·
              refine ⟨59890395546188652199126277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 159707721456503072531003405 59890395546188652199126277)
              ·
                refine ⟨11229449164910372287336177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 59890395546188652199126277 11229449164910372287336177)
                ·
                  refine ⟨8422086873682779215502133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11229449164910372287336177 8422086873682779215502133)
                  ·
                    refine ⟨789570644407760551453325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8422086873682779215502133 789570644407760551453325)
                    ·
                      rfl

theorem cell23_4613050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 3, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 3, 4, 2, 5].length) (baseStart_4613050 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4613050 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4613050 prefixEnd_4613050 := by exact prefixLift 4613050
  have htrace : WordTrace (prefixWord ++ tailWord_4613050) baseStart_4613050 baseEnd_4613050 := by
    simpa [prefixWord, tailWord_4613050, baseEnd_4613050] using wordTrace_append hprefix tailTrace_4613050
  have hstable : (prefixWord ++ tailWord_4613050).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4613050).length < 2 ^ (prefixWord ++ tailWord_4613050).sum := by decide
  have hdescent : baseEnd_4613050 < baseStart_4613050 := by decide
  rcases family_descends (prefixWord ++ tailWord_4613050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4613087 : List Nat := [1, 1, 2, 3, 5, 1, 1, 1, 1, 3, 4]
def baseStart_4613087 : Nat := 118140960795 + 4613087 * 2 ^ 59
def prefixEnd_4613087 : Nat := 4983230072969 + 3 ^ 40 * 4613087 * 2
def baseEnd_4613087 : Nat := 2368730932007498009597305

theorem tailTrace_4613087 : CollatzResearch.WordTrace tailWord_4613087 prefixEnd_4613087 2368730932007498009597305 := by
  unfold tailWord_4613087
  simp only [CollatzResearch.WordTrace]
  refine ⟨168253105438581126380565515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112168736959054084253710343 168253105438581126380565515)
  ·
    refine ⟨252379658157871689570848273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 168253105438581126380565515 252379658157871689570848273)
    ·
      refine ⟨189284743618403767178136205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 252379658157871689570848273 189284743618403767178136205)
      ·
        refine ⟨70981778856901412691801077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 189284743618403767178136205 70981778856901412691801077)
        ·
          refine ⟨6654541767834507439856351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 70981778856901412691801077 6654541767834507439856351)
          ·
            refine ⟨9981812651751761159784527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6654541767834507439856351 9981812651751761159784527)
            ·
              refine ⟨14972718977627641739676791, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9981812651751761159784527 14972718977627641739676791)
              ·
                refine ⟨22459078466441462609515187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14972718977627641739676791 22459078466441462609515187)
                ·
                  refine ⟨33688617699662193914272781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22459078466441462609515187 33688617699662193914272781)
                  ·
                    refine ⟨12633231637373322717852293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 33688617699662193914272781 12633231637373322717852293)
                    ·
                      refine ⟨2368730932007498009597305, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12633231637373322717852293 2368730932007498009597305)
                      ·
                        rfl

theorem cell23_4613087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 5, 1, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 5, 1, 1, 1, 1, 3, 4].length) (baseStart_4613087 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4613087 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4613087 prefixEnd_4613087 := by exact prefixLift 4613087
  have htrace : WordTrace (prefixWord ++ tailWord_4613087) baseStart_4613087 baseEnd_4613087 := by
    simpa [prefixWord, tailWord_4613087, baseEnd_4613087] using wordTrace_append hprefix tailTrace_4613087
  have hstable : (prefixWord ++ tailWord_4613087).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4613087).length < 2 ^ (prefixWord ++ tailWord_4613087).sum := by decide
  have hdescent : baseEnd_4613087 < baseStart_4613087 := by decide
  rcases family_descends (prefixWord ++ tailWord_4613087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4613148 : List Nat := [2, 2, 3, 1, 4, 2, 1, 3, 1, 4]
def baseStart_4613148 : Nat := 118140960795 + 4613148 * 2 ^ 59
def prefixEnd_4613148 : Nat := 4983230072969 + 3 ^ 40 * 4613148 * 2
def baseEnd_4613148 : Nat := 789587418109140756978175

theorem tailTrace_4613148 : CollatzResearch.WordTrace tailWord_4613148 prefixEnd_4613148 789587418109140756978175 := by
  unfold tailWord_4613148
  simp only [CollatzResearch.WordTrace]
  refine ⟨84127665145680066899268049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 112170220194240089199024065 84127665145680066899268049)
  ·
    refine ⟨63095748859260050174451037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 84127665145680066899268049 63095748859260050174451037)
    ·
      refine ⟨23660905822222518815419139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 63095748859260050174451037 23660905822222518815419139)
      ·
        refine ⟨35491358733333778223128709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23660905822222518815419139 35491358733333778223128709)
        ·
          refine ⟨6654629762500083416836633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 35491358733333778223128709 6654629762500083416836633)
          ·
            refine ⟨4990972321875062562627475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6654629762500083416836633 4990972321875062562627475)
            ·
              refine ⟨7486458482812593843941213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4990972321875062562627475 7486458482812593843941213)
              ·
                refine ⟨2807421931054722691477955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7486458482812593843941213 2807421931054722691477955)
                ·
                  refine ⟨4211132896582084037216933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2807421931054722691477955 4211132896582084037216933)
                  ·
                    refine ⟨789587418109140756978175, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4211132896582084037216933 789587418109140756978175)
                    ·
                      rfl

theorem cell23_4613148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 4, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 4, 2, 1, 3, 1, 4].length) (baseStart_4613148 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4613148 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4613148 prefixEnd_4613148 := by exact prefixLift 4613148
  have htrace : WordTrace (prefixWord ++ tailWord_4613148) baseStart_4613148 baseEnd_4613148 := by
    simpa [prefixWord, tailWord_4613148, baseEnd_4613148] using wordTrace_append hprefix tailTrace_4613148
  have hstable : (prefixWord ++ tailWord_4613148).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4613148).length < 2 ^ (prefixWord ++ tailWord_4613148).sum := by decide
  have hdescent : baseEnd_4613148 < baseStart_4613148 := by decide
  rcases family_descends (prefixWord ++ tailWord_4613148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4613157 : List Nat := [1, 3, 1, 2, 2, 2, 1, 5, 1, 5]
def baseStart_4613157 : Nat := 118140960795 + 4613157 * 2 ^ 59
def prefixEnd_4613157 : Nat := 4983230072969 + 3 ^ 40 * 4613157 * 2
def baseEnd_4613157 : Nat := 789588958551104245240661

theorem tailTrace_4613157 : CollatzResearch.WordTrace tailWord_4613157 prefixEnd_4613157 789588958551104245240661 := by
  unfold tailWord_4613157
  simp only [CollatzResearch.WordTrace]
  refine ⟨168255658548327528335613725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112170439032218352223742483 168255658548327528335613725)
  ·
    refine ⟨63095871955622823125855147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 168255658548327528335613725 63095871955622823125855147)
    ·
      refine ⟨94643807933434234688782721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63095871955622823125855147 94643807933434234688782721)
      ·
        refine ⟨70982855950075676016587041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 94643807933434234688782721 70982855950075676016587041)
        ·
          refine ⟨53237141962556757012440281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 70982855950075676016587041 53237141962556757012440281)
          ·
            refine ⟨39927856471917567759330211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 53237141962556757012440281 39927856471917567759330211)
            ·
              refine ⟨59891784707876351638995317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39927856471917567759330211 59891784707876351638995317)
              ·
                refine ⟨5614854816363407966155811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 59891784707876351638995317 5614854816363407966155811)
                ·
                  refine ⟨8422282224545111949233717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5614854816363407966155811 8422282224545111949233717)
                  ·
                    refine ⟨789588958551104245240661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8422282224545111949233717 789588958551104245240661)
                    ·
                      rfl

theorem cell23_4613157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 1, 5, 1, 5].length) (baseStart_4613157 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4613157 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4613157 prefixEnd_4613157 := by exact prefixLift 4613157
  have htrace : WordTrace (prefixWord ++ tailWord_4613157) baseStart_4613157 baseEnd_4613157 := by
    simpa [prefixWord, tailWord_4613157, baseEnd_4613157] using wordTrace_append hprefix tailTrace_4613157
  have hstable : (prefixWord ++ tailWord_4613157).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4613157).length < 2 ^ (prefixWord ++ tailWord_4613157).sum := by decide
  have hdescent : baseEnd_4613157 < baseStart_4613157 := by decide
  rcases family_descends (prefixWord ++ tailWord_4613157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4613164 : List Nat := [2, 2, 1, 1, 1, 2, 5, 2, 2, 3, 2]
def baseStart_4613164 : Nat := 118140960795 + 4613164 * 2 ^ 59
def prefixEnd_4613164 : Nat := 4983230072969 + 3 ^ 40 * 4613164 * 2
def baseEnd_4613164 : Nat := 2368770470017894208334451

theorem tailTrace_4613164 : CollatzResearch.WordTrace tailWord_4613164 prefixEnd_4613164 2368770470017894208334451 := by
  unfold tailWord_4613164
  simp only [CollatzResearch.WordTrace]
  refine ⟨84127956929651084265559273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 112170609239534779020745697 84127956929651084265559273)
  ·
    refine ⟨63095967697238313199169455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 84127956929651084265559273 63095967697238313199169455)
    ·
      refine ⟨94643951545857469798754183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63095967697238313199169455 94643951545857469798754183)
      ·
        refine ⟨141965927318786204698131275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 94643951545857469798754183 141965927318786204698131275)
        ·
          refine ⟨212948890978179307047196913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 141965927318786204698131275 212948890978179307047196913)
          ·
            refine ⟨159711668233634480285397685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 212948890978179307047196913 159711668233634480285397685)
            ·
              refine ⟨14972968896903232526756033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 159711668233634480285397685 14972968896903232526756033)
              ·
                refine ⟨11229726672677424395067025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14972968896903232526756033 11229726672677424395067025)
                ·
                  refine ⟨8422295004508068296300269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11229726672677424395067025 8422295004508068296300269)
                  ·
                    refine ⟨3158360626690525611112601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8422295004508068296300269 3158360626690525611112601)
                    ·
                      refine ⟨2368770470017894208334451, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3158360626690525611112601 2368770470017894208334451)
                      ·
                        rfl

theorem cell23_4613164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 2, 3, 2].length) (baseStart_4613164 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4613164 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4613164 prefixEnd_4613164 := by exact prefixLift 4613164
  have htrace : WordTrace (prefixWord ++ tailWord_4613164) baseStart_4613164 baseEnd_4613164 := by
    simpa [prefixWord, tailWord_4613164, baseEnd_4613164] using wordTrace_append hprefix tailTrace_4613164
  have hstable : (prefixWord ++ tailWord_4613164).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4613164).length < 2 ^ (prefixWord ++ tailWord_4613164).sum := by decide
  have hdescent : baseEnd_4613164 < baseStart_4613164 := by decide
  rcases family_descends (prefixWord ++ tailWord_4613164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4613194 : List Nat := [3, 1, 2, 1, 1, 2, 5, 2, 1, 1, 4]
def baseStart_4613194 : Nat := 118140960795 + 4613194 * 2 ^ 59
def prefixEnd_4613194 : Nat := 4983230072969 + 3 ^ 40 * 4613194 * 2
def baseEnd_4613194 : Nat := 2368785874437529090959313

theorem tailTrace_4613194 : CollatzResearch.WordTrace tailWord_4613194 prefixEnd_4613194 2368785874437529090959313 := by
  unfold tailWord_4613194
  simp only [CollatzResearch.WordTrace]
  refine ⟨42064252012298370913677659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 112171338699462322436473757 42064252012298370913677659)
  ·
    refine ⟨63096378018447556370516489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42064252012298370913677659 63096378018447556370516489)
    ·
      refine ⟨47322283513835667277887367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 63096378018447556370516489 47322283513835667277887367)
      ·
        refine ⟨70983425270753500916831051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47322283513835667277887367 70983425270753500916831051)
        ·
          refine ⟨106475137906130251375246577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 70983425270753500916831051 106475137906130251375246577)
          ·
            refine ⟨79856353429597688531434933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 106475137906130251375246577 79856353429597688531434933)
            ·
              refine ⟨7486533134024783299822025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 79856353429597688531434933 7486533134024783299822025)
              ·
                refine ⟨5614899850518587474866519, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7486533134024783299822025 5614899850518587474866519)
                ·
                  refine ⟨8422349775777881212299779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5614899850518587474866519 8422349775777881212299779)
                  ·
                    refine ⟨12633524663666821818449669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8422349775777881212299779 12633524663666821818449669)
                    ·
                      refine ⟨2368785874437529090959313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12633524663666821818449669 2368785874437529090959313)
                      ·
                        rfl

theorem cell23_4613194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 5, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 5, 2, 1, 1, 4].length) (baseStart_4613194 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4613194 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4613194 prefixEnd_4613194 := by exact prefixLift 4613194
  have htrace : WordTrace (prefixWord ++ tailWord_4613194) baseStart_4613194 baseEnd_4613194 := by
    simpa [prefixWord, tailWord_4613194, baseEnd_4613194] using wordTrace_append hprefix tailTrace_4613194
  have hstable : (prefixWord ++ tailWord_4613194).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4613194).length < 2 ^ (prefixWord ++ tailWord_4613194).sum := by decide
  have hdescent : baseEnd_4613194 < baseStart_4613194 := by decide
  rcases family_descends (prefixWord ++ tailWord_4613194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4613228 : List Nat := [2, 2, 1, 1, 3, 2, 3, 4, 1, 2, 2]
def baseStart_4613228 : Nat := 118140960795 + 4613228 * 2 ^ 59
def prefixEnd_4613228 : Nat := 4983230072969 + 3 ^ 40 * 4613228 * 2
def baseEnd_4613228 : Nat := 2368803332779781957934157

theorem tailTrace_4613228 : CollatzResearch.WordTrace tailWord_4613228 prefixEnd_4613228 2368803332779781957934157 := by
  unfold tailWord_4613228
  simp only [CollatzResearch.WordTrace]
  refine ⟨84129124065535153730724169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 112172165420713538307632225 84129124065535153730724169)
  ·
    refine ⟨63096843049151365298043127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 84129124065535153730724169 63096843049151365298043127)
    ·
      refine ⟨94645264573727047947064691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63096843049151365298043127 94645264573727047947064691)
      ·
        refine ⟨141967896860590571920597037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 94645264573727047947064691 141967896860590571920597037)
        ·
          refine ⟨53237961322721464470223889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 141967896860590571920597037 53237961322721464470223889)
          ·
            refine ⟨39928470992041098352667917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 53237961322721464470223889 39928470992041098352667917)
            ·
              refine ⟨14973176622015411882250469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 39928470992041098352667917 14973176622015411882250469)
              ·
                refine ⟨2807470616627889727921963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14973176622015411882250469 2807470616627889727921963)
                ·
                  refine ⟨4211205924941834591882945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2807470616627889727921963 4211205924941834591882945)
                  ·
                    refine ⟨3158404443706375943912209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4211205924941834591882945 3158404443706375943912209)
                    ·
                      refine ⟨2368803332779781957934157, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3158404443706375943912209 2368803332779781957934157)
                      ·
                        rfl

theorem cell23_4613228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 3, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 3, 4, 1, 2, 2].length) (baseStart_4613228 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4613228 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4613228 prefixEnd_4613228 := by exact prefixLift 4613228
  have htrace : WordTrace (prefixWord ++ tailWord_4613228) baseStart_4613228 baseEnd_4613228 := by
    simpa [prefixWord, tailWord_4613228, baseEnd_4613228] using wordTrace_append hprefix tailTrace_4613228
  have hstable : (prefixWord ++ tailWord_4613228).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4613228).length < 2 ^ (prefixWord ++ tailWord_4613228).sum := by decide
  have hdescent : baseEnd_4613228 < baseStart_4613228 := by decide
  rcases family_descends (prefixWord ++ tailWord_4613228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4613244 : List Nat := [2, 2, 2, 1, 1, 3, 4, 1, 1, 3, 3]
def baseStart_4613244 : Nat := 118140960795 + 4613244 * 2 ^ 59
def prefixEnd_4613244 : Nat := 4983230072969 + 3 ^ 40 * 4613244 * 2
def baseEnd_4613244 : Nat := 2368811548470253895334083

theorem tailTrace_4613244 : CollatzResearch.WordTrace tailWord_4613244 prefixEnd_4613244 2368811548470253895334083 := by
  unfold tailWord_4613244
  simp only [CollatzResearch.WordTrace]
  refine ⟨84129415849506171097015393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 112172554466008228129353857 84129415849506171097015393)
  ·
    refine ⟨63097061887129628322761545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 84129415849506171097015393 63097061887129628322761545)
    ·
      refine ⟨47322796415347221242071159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 63097061887129628322761545 47322796415347221242071159)
      ·
        refine ⟨70984194623020831863106739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47322796415347221242071159 70984194623020831863106739)
        ·
          refine ⟨106476291934531247794660109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 70984194623020831863106739 106476291934531247794660109)
          ·
            refine ⟨39928609475449217922997541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 106476291934531247794660109 39928609475449217922997541)
            ·
              refine ⟨7486614276646728360562039, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 39928609475449217922997541 7486614276646728360562039)
              ·
                refine ⟨11229921414970092540843059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7486614276646728360562039 11229921414970092540843059)
                ·
                  refine ⟨16844882122455138811264589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11229921414970092540843059 16844882122455138811264589)
                  ·
                    refine ⟨6316830795920677054224221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16844882122455138811264589 6316830795920677054224221)
                    ·
                      refine ⟨2368811548470253895334083, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6316830795920677054224221 2368811548470253895334083)
                      ·
                        rfl

theorem cell23_4613244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 4, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 4, 1, 1, 3, 3].length) (baseStart_4613244 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4613244 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4613244 prefixEnd_4613244 := by exact prefixLift 4613244
  have htrace : WordTrace (prefixWord ++ tailWord_4613244) baseStart_4613244 baseEnd_4613244 := by
    simpa [prefixWord, tailWord_4613244, baseEnd_4613244] using wordTrace_append hprefix tailTrace_4613244
  have hstable : (prefixWord ++ tailWord_4613244).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4613244).length < 2 ^ (prefixWord ++ tailWord_4613244).sum := by decide
  have hdescent : baseEnd_4613244 < baseStart_4613244 := by decide
  rcases family_descends (prefixWord ++ tailWord_4613244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4613277 : List Nat := [1, 4, 2, 1, 1, 2, 1, 1, 4, 6]
def baseStart_4613277 : Nat := 118140960795 + 4613277 * 2 ^ 59
def prefixEnd_4613277 : Nat := 4983230072969 + 3 ^ 40 * 4613277 * 2
def baseEnd_4613277 : Nat := 789609497777284088740477

theorem tailTrace_4613277 : CollatzResearch.WordTrace tailWord_4613277 prefixEnd_4613277 789609497777284088740477 := by
  unfold tailWord_4613277
  simp only [CollatzResearch.WordTrace]
  refine ⟨168260035307892788829982085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112173356871928525886654723 168260035307892788829982085)
  ·
    refine ⟨31548756620229897905621641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 168260035307892788829982085 31548756620229897905621641)
    ·
      refine ⟨23661567465172423429216231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31548756620229897905621641 23661567465172423429216231)
      ·
        refine ⟨35492351197758635143824347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23661567465172423429216231 35492351197758635143824347)
        ·
          refine ⟨53238526796637952715736521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35492351197758635143824347 53238526796637952715736521)
          ·
            refine ⟨39928895097478464536802391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 53238526796637952715736521 39928895097478464536802391)
            ·
              refine ⟨59893342646217696805203587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39928895097478464536802391 59893342646217696805203587)
              ·
                refine ⟨89840013969326545207805381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 59893342646217696805203587 89840013969326545207805381)
                ·
                  refine ⟨16845002619248727226463509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 89840013969326545207805381 16845002619248727226463509)
                  ·
                    refine ⟨789609497777284088740477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16845002619248727226463509 789609497777284088740477)
                    ·
                      rfl

theorem cell23_4613277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 1, 1, 4, 6].length) (baseStart_4613277 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4613277 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4613277 prefixEnd_4613277 := by exact prefixLift 4613277
  have htrace : WordTrace (prefixWord ++ tailWord_4613277) baseStart_4613277 baseEnd_4613277 := by
    simpa [prefixWord, tailWord_4613277, baseEnd_4613277] using wordTrace_append hprefix tailTrace_4613277
  have hstable : (prefixWord ++ tailWord_4613277).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4613277).length < 2 ^ (prefixWord ++ tailWord_4613277).sum := by decide
  have hdescent : baseEnd_4613277 < baseStart_4613277 := by decide
  rcases family_descends (prefixWord ++ tailWord_4613277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4613278 : List Nat := [4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3]
def baseStart_4613278 : Nat := 118140960795 + 4613278 * 2 ^ 59
def prefixEnd_4613278 : Nat := 4983230072969 + 3 ^ 40 * 4613278 * 2
def baseEnd_4613278 : Nat := 2368829006812506762308927

theorem tailTrace_4613278 : CollatzResearch.WordTrace tailWord_4613278 prefixEnd_4613278 2368829006812506762308927 := by
  unfold tailWord_4613278
  simp only [CollatzResearch.WordTrace]
  refine ⟨21032508972611145750096061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 112173381187259444000512325 21032508972611145750096061)
  ·
    refine ⟨7887190864729179656286023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21032508972611145750096061 7887190864729179656286023)
    ·
      refine ⟨11830786297093769484429035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7887190864729179656286023 11830786297093769484429035)
      ·
        refine ⟨17746179445640654226643553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11830786297093769484429035 17746179445640654226643553)
        ·
          refine ⟨13309634584230490669982665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17746179445640654226643553 13309634584230490669982665)
          ·
            refine ⟨9982225938172868002486999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13309634584230490669982665 9982225938172868002486999)
            ·
              refine ⟨14973338907259302003730499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9982225938172868002486999 14973338907259302003730499)
              ·
                refine ⟨22460008360888953005595749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14973338907259302003730499 22460008360888953005595749)
                ·
                  refine ⟨4211251567666678688549203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 22460008360888953005595749 4211251567666678688549203)
                  ·
                    refine ⟨6316877351500018032823805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4211251567666678688549203 6316877351500018032823805)
                    ·
                      refine ⟨2368829006812506762308927, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6316877351500018032823805 2368829006812506762308927)
                      ·
                        rfl

theorem cell23_4613278_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3].length) (baseStart_4613278 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4613278 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4613278 prefixEnd_4613278 := by exact prefixLift 4613278
  have htrace : WordTrace (prefixWord ++ tailWord_4613278) baseStart_4613278 baseEnd_4613278 := by
    simpa [prefixWord, tailWord_4613278, baseEnd_4613278] using wordTrace_append hprefix tailTrace_4613278
  have hstable : (prefixWord ++ tailWord_4613278).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4613278).length < 2 ^ (prefixWord ++ tailWord_4613278).sum := by decide
  have hdescent : baseEnd_4613278 < baseStart_4613278 := by decide
  rcases family_descends (prefixWord ++ tailWord_4613278) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4613408 : List Nat := [2, 1, 1, 5, 3, 1, 1, 1, 2, 4, 2]
def baseStart_4613408 : Nat := 118140960795 + 4613408 * 2 ^ 59
def prefixEnd_4613408 : Nat := 4983230072969 + 3 ^ 40 * 4613408 * 2
def baseEnd_4613408 : Nat := 2368895759297591253683329

theorem tailTrace_4613408 : CollatzResearch.WordTrace tailWord_4613408 prefixEnd_4613408 2368895759297591253683329 := by
  unfold tailWord_4613408
  simp only [CollatzResearch.WordTrace]
  refine ⟨84132406635209099101500439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 112176542180278798802000585 84132406635209099101500439)
  ·
    refine ⟨126198609952813648652250659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84132406635209099101500439 126198609952813648652250659)
    ·
      refine ⟨189297914929220472978375989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 126198609952813648652250659 189297914929220472978375989)
      ·
        refine ⟨17746679524614419341722749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 189297914929220472978375989 17746679524614419341722749)
        ·
          refine ⟨6655004821730407253146031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17746679524614419341722749 6655004821730407253146031)
          ·
            refine ⟨9982507232595610879719047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6655004821730407253146031 9982507232595610879719047)
            ·
              refine ⟨14973760848893416319578571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9982507232595610879719047 14973760848893416319578571)
              ·
                refine ⟨22460641273340124479367857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14973760848893416319578571 22460641273340124479367857)
                ·
                  refine ⟨16845480955005093359525893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22460641273340124479367857 16845480955005093359525893)
                  ·
                    refine ⟨3158527679063455004911105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16845480955005093359525893 3158527679063455004911105)
                    ·
                      refine ⟨2368895759297591253683329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3158527679063455004911105 2368895759297591253683329)
                      ·
                        rfl

theorem cell23_4613408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 3, 1, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 3, 1, 1, 1, 2, 4, 2].length) (baseStart_4613408 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4613408 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4613408 prefixEnd_4613408 := by exact prefixLift 4613408
  have htrace : WordTrace (prefixWord ++ tailWord_4613408) baseStart_4613408 baseEnd_4613408 := by
    simpa [prefixWord, tailWord_4613408, baseEnd_4613408] using wordTrace_append hprefix tailTrace_4613408
  have hstable : (prefixWord ++ tailWord_4613408).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4613408).length < 2 ^ (prefixWord ++ tailWord_4613408).sum := by decide
  have hdescent : baseEnd_4613408 < baseStart_4613408 := by decide
  rcases family_descends (prefixWord ++ tailWord_4613408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4613418 : List Nat := [3, 1, 4, 2, 1, 2, 1, 2, 3, 4]
def baseStart_4613418 : Nat := 118140960795 + 4613418 * 2 ^ 59
def prefixEnd_4613418 : Nat := 4983230072969 + 3 ^ 40 * 4613418 * 2
def baseEnd_4613418 : Nat := 789633631368045404852761

theorem tailTrace_4613418 : CollatzResearch.WordTrace tailWord_4613418 prefixEnd_4613418 789633631368045404852761 := by
  unfold tailWord_4613418
  simp only [CollatzResearch.WordTrace]
  refine ⟨42066294500095492477716227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 112176785333587979940576605 42066294500095492477716227)
  ·
    refine ⟨63099441750143238716574341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42066294500095492477716227 63099441750143238716574341)
    ·
      refine ⟨11831145328151857259357689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 63099441750143238716574341 11831145328151857259357689)
      ·
        refine ⟨8873358996113892944518267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11831145328151857259357689 8873358996113892944518267)
        ·
          refine ⟨13310038494170839416777401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8873358996113892944518267 13310038494170839416777401)
          ·
            refine ⟨9982528870628129562583051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13310038494170839416777401 9982528870628129562583051)
            ·
              refine ⟨14973793305942194343874577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9982528870628129562583051 14973793305942194343874577)
              ·
                refine ⟨11230344979456645757905933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14973793305942194343874577 11230344979456645757905933)
                ·
                  refine ⟨4211379367296242159214725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11230344979456645757905933 4211379367296242159214725)
                  ·
                    refine ⟨789633631368045404852761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4211379367296242159214725 789633631368045404852761)
                    ·
                      rfl

theorem cell23_4613418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 2, 1, 2, 3, 4].length) (baseStart_4613418 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4613418 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4613418 prefixEnd_4613418 := by exact prefixLift 4613418
  have htrace : WordTrace (prefixWord ++ tailWord_4613418) baseStart_4613418 baseEnd_4613418 := by
    simpa [prefixWord, tailWord_4613418, baseEnd_4613418] using wordTrace_append hprefix tailTrace_4613418
  have hstable : (prefixWord ++ tailWord_4613418).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4613418).length < 2 ^ (prefixWord ++ tailWord_4613418).sum := by decide
  have hdescent : baseEnd_4613418 < baseStart_4613418 := by decide
  rcases family_descends (prefixWord ++ tailWord_4613418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4613501 : List Nat := [1, 4, 1, 1, 2, 2, 4, 1, 1, 1, 5]
def baseStart_4613501 : Nat := 118140960795 + 4613501 * 2 ^ 59
def prefixEnd_4613501 : Nat := 4983230072969 + 3 ^ 40 * 4613501 * 2
def baseEnd_4613501 : Nat := 2368943512998459389820401

theorem tailTrace_4613501 : CollatzResearch.WordTrace tailWord_4613501 prefixEnd_4613501 2368943512998459389820401 := by
  unfold tailWord_4613501
  simp only [CollatzResearch.WordTrace]
  refine ⟨168268205259081275086136357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112178803506054183390757571 168268205259081275086136357)
  ·
    refine ⟨31550288486077739078650567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 168268205259081275086136357 31550288486077739078650567)
    ·
      refine ⟨47325432729116608617975851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31550288486077739078650567 47325432729116608617975851)
      ·
        refine ⟨70988149093674912926963777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47325432729116608617975851 70988149093674912926963777)
        ·
          refine ⟨53241111820256184695222833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 70988149093674912926963777 53241111820256184695222833)
          ·
            refine ⟨39930833865192138521417125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 53241111820256184695222833 39930833865192138521417125)
            ·
              refine ⟨7487031349723525972765711, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 39930833865192138521417125 7487031349723525972765711)
              ·
                refine ⟨11230547024585288959148567, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7487031349723525972765711 11230547024585288959148567)
                ·
                  refine ⟨16845820536877933438722851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11230547024585288959148567 16845820536877933438722851)
                  ·
                    refine ⟨25268730805316900158084277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16845820536877933438722851 25268730805316900158084277)
                    ·
                      refine ⟨2368943512998459389820401, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25268730805316900158084277 2368943512998459389820401)
                      ·
                        rfl

theorem cell23_4613501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 4, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 4, 1, 1, 1, 5].length) (baseStart_4613501 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4613501 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4613501 prefixEnd_4613501 := by exact prefixLift 4613501
  have htrace : WordTrace (prefixWord ++ tailWord_4613501) baseStart_4613501 baseEnd_4613501 := by
    simpa [prefixWord, tailWord_4613501, baseEnd_4613501] using wordTrace_append hprefix tailTrace_4613501
  have hstable : (prefixWord ++ tailWord_4613501).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4613501).length < 2 ^ (prefixWord ++ tailWord_4613501).sum := by decide
  have hdescent : baseEnd_4613501 < baseStart_4613501 := by decide
  rcases family_descends (prefixWord ++ tailWord_4613501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4613532 : List Nat := [2, 2, 3, 4, 1, 2, 1, 2, 1, 1, 4]
def baseStart_4613532 : Nat := 118140960795 + 4613532 * 2 ^ 59
def prefixEnd_4613532 : Nat := 4983230072969 + 3 ^ 40 * 4613532 * 2
def baseEnd_4613532 : Nat := 2368959430898748768532759

theorem tailTrace_4613532 : CollatzResearch.WordTrace tailWord_4613532 prefixEnd_4613532 2368959430898748768532759 := by
  unfold tailWord_4613532
  simp only [CollatzResearch.WordTrace]
  refine ⟨84134667960984483690257425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 112179557281312644920343233 84134667960984483690257425)
  ·
    refine ⟨63101000970738362767693069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 84134667960984483690257425 63101000970738362767693069)
    ·
      refine ⟨23662875364026886037884901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 63101000970738362767693069 23662875364026886037884901)
      ·
        refine ⟨4436789130755041132103419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 23662875364026886037884901 4436789130755041132103419)
        ·
          refine ⟨6655183696132561698155129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4436789130755041132103419 6655183696132561698155129)
          ·
            refine ⟨4991387772099421273616347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6655183696132561698155129 4991387772099421273616347)
            ·
              refine ⟨7487081658149131910424521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4991387772099421273616347 7487081658149131910424521)
              ·
                refine ⟨5615311243611848932818391, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7487081658149131910424521 5615311243611848932818391)
                ·
                  refine ⟨8422966865417773399227587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5615311243611848932818391 8422966865417773399227587)
                  ·
                    refine ⟨12634450298126660098841381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8422966865417773399227587 12634450298126660098841381)
                    ·
                      refine ⟨2368959430898748768532759, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12634450298126660098841381 2368959430898748768532759)
                      ·
                        rfl

theorem cell23_4613532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 1, 2, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 1, 2, 1, 2, 1, 1, 4].length) (baseStart_4613532 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4613532 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4613532 prefixEnd_4613532 := by exact prefixLift 4613532
  have htrace : WordTrace (prefixWord ++ tailWord_4613532) baseStart_4613532 baseEnd_4613532 := by
    simpa [prefixWord, tailWord_4613532, baseEnd_4613532] using wordTrace_append hprefix tailTrace_4613532
  have hstable : (prefixWord ++ tailWord_4613532).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4613532).length < 2 ^ (prefixWord ++ tailWord_4613532).sum := by decide
  have hdescent : baseEnd_4613532 < baseStart_4613532 := by decide
  rcases family_descends (prefixWord ++ tailWord_4613532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4613535 : List Nat := [1, 1, 2, 5, 1, 4, 1, 2, 1, 2, 3]
def baseStart_4613535 : Nat := 118140960795 + 4613535 * 2 ^ 59
def prefixEnd_4613535 : Nat := 4983230072969 + 3 ^ 40 * 4613535 * 2
def baseEnd_4613535 : Nat := 2368960971340712256795245

theorem tailTrace_4613535 : CollatzResearch.WordTrace tailWord_4613535 prefixEnd_4613535 2368960971340712256795245 := by
  unfold tailWord_4613535
  simp only [CollatzResearch.WordTrace]
  refine ⟨168269445340958098892874059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112179630227305399261916039 168269445340958098892874059)
  ·
    refine ⟨252404168011437148339311089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 168269445340958098892874059 252404168011437148339311089)
    ·
      refine ⟨189303126008577861254483317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 252404168011437148339311089 189303126008577861254483317)
      ·
        refine ⟨17747168063304174492607811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 189303126008577861254483317 17747168063304174492607811)
        ·
          refine ⟨26620752094956261738911717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17747168063304174492607811 26620752094956261738911717)
          ·
            refine ⟨4991391017804299076045947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 26620752094956261738911717 4991391017804299076045947)
            ·
              refine ⟨7487086526706448614068921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4991391017804299076045947 7487086526706448614068921)
              ·
                refine ⟨5615314895029836460551691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7487086526706448614068921 5615314895029836460551691)
                ·
                  refine ⟨8422972342544754690827537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5615314895029836460551691 8422972342544754690827537)
                  ·
                    refine ⟨6317229256908566018120653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8422972342544754690827537 6317229256908566018120653)
                    ·
                      refine ⟨2368960971340712256795245, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6317229256908566018120653 2368960971340712256795245)
                      ·
                        rfl

theorem cell23_4613535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 4, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 4, 1, 2, 1, 2, 3].length) (baseStart_4613535 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4613535 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4613535 prefixEnd_4613535 := by exact prefixLift 4613535
  have htrace : WordTrace (prefixWord ++ tailWord_4613535) baseStart_4613535 baseEnd_4613535 := by
    simpa [prefixWord, tailWord_4613535, baseEnd_4613535] using wordTrace_append hprefix tailTrace_4613535
  have hstable : (prefixWord ++ tailWord_4613535).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4613535).length < 2 ^ (prefixWord ++ tailWord_4613535).sum := by decide
  have hdescent : baseEnd_4613535 < baseStart_4613535 := by decide
  rcases family_descends (prefixWord ++ tailWord_4613535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4613565 : List Nat := [1, 4, 1, 2, 2, 1, 4, 2, 2, 1, 3]
def baseStart_4613565 : Nat := 118140960795 + 4613565 * 2 ^ 59
def prefixEnd_4613565 : Nat := 4983230072969 + 3 ^ 40 * 4613565 * 2
def baseEnd_4613565 : Nat := 2368976375760347139420107

theorem tailTrace_4613565 : CollatzResearch.WordTrace tailWord_4613565 prefixEnd_4613565 2368976375760347139420107 := by
  unfold tailWord_4613565
  simp only [CollatzResearch.WordTrace]
  refine ⟨168270539530849414016466149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112180359687232942677644099 168270539530849414016466149)
  ·
    refine ⟨31550726162034265128087403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 168270539530849414016466149 31550726162034265128087403)
    ·
      refine ⟨47326089243051397692131105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31550726162034265128087403 47326089243051397692131105)
      ·
        refine ⟨35494566932288548269098329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47326089243051397692131105 35494566932288548269098329)
        ·
          refine ⟨26620925199216411201823747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35494566932288548269098329 26620925199216411201823747)
          ·
            refine ⟨39931387798824616802735621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26620925199216411201823747 39931387798824616802735621)
            ·
              refine ⟨7487135212279615650512929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 39931387798824616802735621 7487135212279615650512929)
              ·
                refine ⟨5615351409209711737884697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7487135212279615650512929 5615351409209711737884697)
                ·
                  refine ⟨4211513556907283803413523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5615351409209711737884697 4211513556907283803413523)
                  ·
                    refine ⟨6317270335360925705120285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4211513556907283803413523 6317270335360925705120285)
                    ·
                      refine ⟨2368976375760347139420107, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6317270335360925705120285 2368976375760347139420107)
                      ·
                        rfl

theorem cell23_4613565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 4, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 4, 2, 2, 1, 3].length) (baseStart_4613565 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4613565 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4613565 prefixEnd_4613565 := by exact prefixLift 4613565
  have htrace : WordTrace (prefixWord ++ tailWord_4613565) baseStart_4613565 baseEnd_4613565 := by
    simpa [prefixWord, tailWord_4613565, baseEnd_4613565] using wordTrace_append hprefix tailTrace_4613565
  have hstable : (prefixWord ++ tailWord_4613565).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4613565).length < 2 ^ (prefixWord ++ tailWord_4613565).sum := by decide
  have hdescent : baseEnd_4613565 < baseStart_4613565 := by decide
  rcases family_descends (prefixWord ++ tailWord_4613565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4613584 : List Nat := [2, 1, 1, 1, 1, 2, 2, 2, 2, 3, 6]
def baseStart_4613584 : Nat := 118140960795 + 4613584 * 2 ^ 59
def prefixEnd_4613584 : Nat := 4983230072969 + 3 ^ 40 * 4613584 * 2
def baseEnd_4613584 : Nat := 2368986131892782565082519

theorem tailTrace_4613584 : CollatzResearch.WordTrace tailWord_4613584 prefixEnd_4613584 2368986131892782565082519 := by
  unfold tailWord_4613584
  simp only [CollatzResearch.WordTrace]
  refine ⟨84135616258890290130703903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 112180821678520386840938537 84135616258890290130703903)
  ·
    refine ⟨126203424388335435196055855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84135616258890290130703903 126203424388335435196055855)
    ·
      refine ⟨189305136582503152794083783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 126203424388335435196055855 189305136582503152794083783)
      ·
        refine ⟨283957704873754729191125675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 189305136582503152794083783 283957704873754729191125675)
        ·
          refine ⟨425936557310632093786688513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 283957704873754729191125675 425936557310632093786688513)
          ·
            refine ⟨319452417982974070340016385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 425936557310632093786688513 319452417982974070340016385)
            ·
              refine ⟨239589313487230552755012289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 319452417982974070340016385 239589313487230552755012289)
              ·
                refine ⟨179691985115422914566259217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 239589313487230552755012289 179691985115422914566259217)
                ·
                  refine ⟨134768988836567185924694413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 179691985115422914566259217 134768988836567185924694413)
                  ·
                    refine ⟨50538370813712694721760405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 134768988836567185924694413 50538370813712694721760405)
                    ·
                      refine ⟨2368986131892782565082519, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 50538370813712694721760405 2368986131892782565082519)
                      ·
                        rfl

theorem cell23_4613584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 2, 2, 3, 6].length) (baseStart_4613584 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4613584 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4613584 prefixEnd_4613584 := by exact prefixLift 4613584
  have htrace : WordTrace (prefixWord ++ tailWord_4613584) baseStart_4613584 baseEnd_4613584 := by
    simpa [prefixWord, tailWord_4613584, baseEnd_4613584] using wordTrace_append hprefix tailTrace_4613584
  have hstable : (prefixWord ++ tailWord_4613584).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4613584).length < 2 ^ (prefixWord ++ tailWord_4613584).sum := by decide
  have hdescent : baseEnd_4613584 < baseStart_4613584 := by decide
  rcases family_descends (prefixWord ++ tailWord_4613584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4613605 : List Nat := [1, 3, 1, 5, 1, 1, 2, 2, 1, 4, 2]
def baseStart_4613605 : Nat := 118140960795 + 4613605 * 2 ^ 59
def prefixEnd_4613605 : Nat := 4983230072969 + 3 ^ 40 * 4613605 * 2
def baseEnd_4613605 : Nat := 2368996914986526982919923

theorem tailTrace_4613605 : CollatzResearch.WordTrace tailWord_4613605 prefixEnd_4613605 2368996914986526982919923 := by
  unfold tailWord_4613605
  simp only [CollatzResearch.WordTrace]
  refine ⟨168271998450704500847922269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112181332300469667231948179 168271998450704500847922269)
  ·
    refine ⟨63101999419014187817970851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 168271998450704500847922269 63101999419014187817970851)
    ·
      refine ⟨94652999128521281726956277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63101999419014187817970851 94652999128521281726956277)
      ·
        refine ⟨8873718668298870161902151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 94652999128521281726956277 8873718668298870161902151)
        ·
          refine ⟨13310578002448305242853227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8873718668298870161902151 13310578002448305242853227)
          ·
            refine ⟨19965867003672457864279841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13310578002448305242853227 19965867003672457864279841)
            ·
              refine ⟨14974400252754343398209881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19965867003672457864279841 14974400252754343398209881)
              ·
                refine ⟨11230800189565757548657411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14974400252754343398209881 11230800189565757548657411)
                ·
                  refine ⟨16846200284348636322986117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11230800189565757548657411 16846200284348636322986117)
                  ·
                    refine ⟨3158662553315369310559897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16846200284348636322986117 3158662553315369310559897)
                    ·
                      refine ⟨2368996914986526982919923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3158662553315369310559897 2368996914986526982919923)
                      ·
                        rfl

theorem cell23_4613605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 2, 2, 1, 4, 2].length) (baseStart_4613605 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4613605 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4613605 prefixEnd_4613605 := by exact prefixLift 4613605
  have htrace : WordTrace (prefixWord ++ tailWord_4613605) baseStart_4613605 baseEnd_4613605 := by
    simpa [prefixWord, tailWord_4613605, baseEnd_4613605] using wordTrace_append hprefix tailTrace_4613605
  have hstable : (prefixWord ++ tailWord_4613605).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4613605).length < 2 ^ (prefixWord ++ tailWord_4613605).sum := by decide
  have hdescent : baseEnd_4613605 < baseStart_4613605 := by decide
  rcases family_descends (prefixWord ++ tailWord_4613605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4613618 : List Nat := [3, 2, 1, 4, 1, 1, 1, 2, 2, 2, 4]
def baseStart_4613618 : Nat := 118140960795 + 4613618 * 2 ^ 59
def prefixEnd_4613618 : Nat := 4983230072969 + 3 ^ 40 * 4613618 * 2
def baseEnd_4613618 : Nat := 2369003590235035432057363

theorem tailTrace_4613618 : CollatzResearch.WordTrace tailWord_4613618 prefixEnd_4613618 2369003590235035432057363 := by
  unfold tailWord_4613618
  simp only [CollatzResearch.WordTrace]
  refine ⟨42068118149914351017036377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 112181648399771602712097005 42068118149914351017036377)
  ·
    refine ⟨31551088612435763262777283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42068118149914351017036377 31551088612435763262777283)
    ·
      refine ⟨47326632918653644894165925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31551088612435763262777283 47326632918653644894165925)
      ·
        refine ⟨8873743672247558417656111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 47326632918653644894165925 8873743672247558417656111)
        ·
          refine ⟨13310615508371337626484167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8873743672247558417656111 13310615508371337626484167)
          ·
            refine ⟨19965923262557006439726251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13310615508371337626484167 19965923262557006439726251)
            ·
              refine ⟨29948884893835509659589377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19965923262557006439726251 29948884893835509659589377)
              ·
                refine ⟨22461663670376632244692033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29948884893835509659589377 22461663670376632244692033)
                ·
                  refine ⟨16846247752782474183519025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22461663670376632244692033 16846247752782474183519025)
                  ·
                    refine ⟨12634685814586855637639269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16846247752782474183519025 12634685814586855637639269)
                    ·
                      refine ⟨2369003590235035432057363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12634685814586855637639269 2369003590235035432057363)
                      ·
                        rfl

theorem cell23_4613618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 1, 2, 2, 2, 4].length) (baseStart_4613618 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4613618 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4613618 prefixEnd_4613618 := by exact prefixLift 4613618
  have htrace : WordTrace (prefixWord ++ tailWord_4613618) baseStart_4613618 baseEnd_4613618 := by
    simpa [prefixWord, tailWord_4613618, baseEnd_4613618] using wordTrace_append hprefix tailTrace_4613618
  have hstable : (prefixWord ++ tailWord_4613618).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4613618).length < 2 ^ (prefixWord ++ tailWord_4613618).sum := by decide
  have hdescent : baseEnd_4613618 < baseStart_4613618 := by decide
  rcases family_descends (prefixWord ++ tailWord_4613618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4613622 : List Nat := [5, 1, 1, 1, 2, 3, 1, 1, 4, 2, 2]
def baseStart_4613622 : Nat := 118140960795 + 4613622 * 2 ^ 59
def prefixEnd_4613622 : Nat := 4983230072969 + 3 ^ 40 * 4613622 * 2
def baseEnd_4613622 : Nat := 2369005644157653416407345

theorem tailTrace_4613622 : CollatzResearch.WordTrace tailWord_4613622 prefixEnd_4613622 2369005644157653416407345 := by
  unfold tailWord_4613622
  simp only [CollatzResearch.WordTrace]
  refine ⟨10517038655727682046955695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 112181745661095275167527413 10517038655727682046955695)
  ·
    refine ⟨15775557983591523070433543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10517038655727682046955695 15775557983591523070433543)
    ·
      refine ⟨23663336975387284605650315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15775557983591523070433543 23663336975387284605650315)
      ·
        refine ⟨35495005463080926908475473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23663336975387284605650315 35495005463080926908475473)
        ·
          refine ⟨26621254097310695181356605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35495005463080926908475473 26621254097310695181356605)
          ·
            refine ⟨9982970286491510693008727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26621254097310695181356605 9982970286491510693008727)
            ·
              refine ⟨14974455429737266039513091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9982970286491510693008727 14974455429737266039513091)
              ·
                refine ⟨22461683144605899059269637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14974455429737266039513091 22461683144605899059269637)
                ·
                  refine ⟨4211565589613606073613057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 22461683144605899059269637 4211565589613606073613057)
                  ·
                    refine ⟨3158674192210204555209793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4211565589613606073613057 3158674192210204555209793)
                    ·
                      refine ⟨2369005644157653416407345, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3158674192210204555209793 2369005644157653416407345)
                      ·
                        rfl

theorem cell23_4613622_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 3, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 3, 1, 1, 4, 2, 2].length) (baseStart_4613622 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4613622 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4613622 prefixEnd_4613622 := by exact prefixLift 4613622
  have htrace : WordTrace (prefixWord ++ tailWord_4613622) baseStart_4613622 baseEnd_4613622 := by
    simpa [prefixWord, tailWord_4613622, baseEnd_4613622] using wordTrace_append hprefix tailTrace_4613622
  have hstable : (prefixWord ++ tailWord_4613622).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4613622).length < 2 ^ (prefixWord ++ tailWord_4613622).sum := by decide
  have hdescent : baseEnd_4613622 < baseStart_4613622 := by decide
  rcases family_descends (prefixWord ++ tailWord_4613622) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4613628 : List Nat := [2, 2, 2, 1, 2, 1, 4, 4, 5]
def baseStart_4613628 : Nat := 118140960795 + 4613628 * 2 ^ 59
def prefixEnd_4613628 : Nat := 4983230072969 + 3 ^ 40 * 4613628 * 2
def baseEnd_4613628 : Nat := 263223191671286710325813

theorem tailTrace_4613628 : CollatzResearch.WordTrace tailWord_4613628 prefixEnd_4613628 263223191671286710325813 := by
  unfold tailWord_4613628
  simp only [CollatzResearch.WordTrace]
  refine ⟨84136418664810587888004769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 112181891553080783850673025 84136418664810587888004769)
  ·
    refine ⟨63102313998607940916003577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 84136418664810587888004769 63102313998607940916003577)
    ·
      refine ⟨47326735498955955687002683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 63102313998607940916003577 47326735498955955687002683)
      ·
        refine ⟨70990103248433933530504025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47326735498955955687002683 70990103248433933530504025)
        ·
          refine ⟨53242577436325450147878019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 70990103248433933530504025 53242577436325450147878019)
          ·
            refine ⟨79863866154488175221817029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53242577436325450147878019 79863866154488175221817029)
            ·
              refine ⟨14974474903966532854090693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 79863866154488175221817029 14974474903966532854090693)
              ·
                refine ⟨2807714044493724910142005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14974474903966532854090693 2807714044493724910142005)
                ·
                  refine ⟨263223191671286710325813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2807714044493724910142005 263223191671286710325813)
                  ·
                    rfl

theorem cell23_4613628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 4, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 4, 4, 5].length) (baseStart_4613628 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4613628 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4613628 prefixEnd_4613628 := by exact prefixLift 4613628
  have htrace : WordTrace (prefixWord ++ tailWord_4613628) baseStart_4613628 baseEnd_4613628 := by
    simpa [prefixWord, tailWord_4613628, baseEnd_4613628] using wordTrace_append hprefix tailTrace_4613628
  have hstable : (prefixWord ++ tailWord_4613628).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4613628).length < 2 ^ (prefixWord ++ tailWord_4613628).sum := by decide
  have hdescent : baseEnd_4613628 < baseStart_4613628 := by decide
  rcases family_descends (prefixWord ++ tailWord_4613628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4613639 : List Nat := [1, 1, 4, 3, 2, 2, 3, 1, 2, 2, 2]
def baseStart_4613639 : Nat := 118140960795 + 4613639 * 2 ^ 59
def prefixEnd_4613639 : Nat := 4983230072969 + 3 ^ 40 * 4613639 * 2
def baseEnd_4613639 : Nat := 2369014373328779849894767

theorem tailTrace_4613639 : CollatzResearch.WordTrace tailWord_4613639 prefixEnd_4613639 2369014373328779849894767 := by
  unfold tailWord_4613639
  simp only [CollatzResearch.WordTrace]
  refine ⟨168273238532581324654659971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112182159021720883103106647 168273238532581324654659971)
  ·
    refine ⟨252409857798871986981989957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 168273238532581324654659971 252409857798871986981989957)
    ·
      refine ⟨47326848337288497559123117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 252409857798871986981989957 47326848337288497559123117)
      ·
        refine ⟨17747568126483186584671169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 47326848337288497559123117 17747568126483186584671169)
        ·
          refine ⟨13310676094862389938503377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17747568126483186584671169 13310676094862389938503377)
          ·
            refine ⟨9983007071146792453877533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13310676094862389938503377 9983007071146792453877533)
            ·
              refine ⟨3743627651680047170204075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9983007071146792453877533 3743627651680047170204075)
              ·
                refine ⟨5615441477520070755306113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3743627651680047170204075 5615441477520070755306113)
                ·
                  refine ⟨4211581108140053066479585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5615441477520070755306113 4211581108140053066479585)
                  ·
                    refine ⟨3158685831105039799859689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4211581108140053066479585 3158685831105039799859689)
                    ·
                      refine ⟨2369014373328779849894767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3158685831105039799859689 2369014373328779849894767)
                      ·
                        rfl

theorem cell23_4613639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 2, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 2, 3, 1, 2, 2, 2].length) (baseStart_4613639 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4613639 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4613639 prefixEnd_4613639 := by exact prefixLift 4613639
  have htrace : WordTrace (prefixWord ++ tailWord_4613639) baseStart_4613639 baseEnd_4613639 := by
    simpa [prefixWord, tailWord_4613639, baseEnd_4613639] using wordTrace_append hprefix tailTrace_4613639
  have hstable : (prefixWord ++ tailWord_4613639).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4613639).length < 2 ^ (prefixWord ++ tailWord_4613639).sum := by decide
  have hdescent : baseEnd_4613639 < baseStart_4613639 := by decide
  rcases family_descends (prefixWord ++ tailWord_4613639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4613805 : List Nat := [1, 5, 2, 1, 1, 1, 3, 2, 1, 1, 5]
def baseStart_4613805 : Nat := 118140960795 + 4613805 * 2 ^ 59
def prefixEnd_4613805 : Nat := 4983230072969 + 3 ^ 40 * 4613805 * 2
def baseEnd_4613805 : Nat := 2369099611117426200419003

theorem tailTrace_4613805 : CollatzResearch.WordTrace tailWord_4613805 prefixEnd_4613805 2369099611117426200419003 := by
  unfold tailWord_4613805
  simp only [CollatzResearch.WordTrace]
  refine ⟨168279293049979935005202869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112186195366653290003468579 168279293049979935005202869)
  ·
    refine ⟨15776183723435618906737769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 168279293049979935005202869 15776183723435618906737769)
    ·
      refine ⟨11832137792576714180053327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15776183723435618906737769 11832137792576714180053327)
      ·
        refine ⟨17748206688865071270079991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11832137792576714180053327 17748206688865071270079991)
        ·
          refine ⟨26622310033297606905119987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17748206688865071270079991 26622310033297606905119987)
          ·
            refine ⟨39933465049946410357679981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26622310033297606905119987 39933465049946410357679981)
            ·
              refine ⟨14975049393729903884129993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 39933465049946410357679981 14975049393729903884129993)
              ·
                refine ⟨11231287045297427913097495, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14975049393729903884129993 11231287045297427913097495)
                ·
                  refine ⟨16846930567946141869646243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11231287045297427913097495 16846930567946141869646243)
                  ·
                    refine ⟨25270395851919212804469365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16846930567946141869646243 25270395851919212804469365)
                    ·
                      refine ⟨2369099611117426200419003, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25270395851919212804469365 2369099611117426200419003)
                      ·
                        rfl

theorem cell23_4613805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 3, 2, 1, 1, 5].length) (baseStart_4613805 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4613805 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4613805 prefixEnd_4613805 := by exact prefixLift 4613805
  have htrace : WordTrace (prefixWord ++ tailWord_4613805) baseStart_4613805 baseEnd_4613805 := by
    simpa [prefixWord, tailWord_4613805, baseEnd_4613805] using wordTrace_append hprefix tailTrace_4613805
  have hstable : (prefixWord ++ tailWord_4613805).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4613805).length < 2 ^ (prefixWord ++ tailWord_4613805).sum := by decide
  have hdescent : baseEnd_4613805 < baseStart_4613805 := by decide
  rcases family_descends (prefixWord ++ tailWord_4613805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4613815 : List Nat := [1, 1, 3, 1, 5, 1, 3, 1, 1, 2, 4]
def baseStart_4613815 : Nat := 118140960795 + 4613815 * 2 ^ 59
def prefixEnd_4613815 : Nat := 4983230072969 + 3 ^ 40 * 4613815 * 2
def baseEnd_4613815 : Nat := 2369104745923971161293957

theorem tailTrace_4613815 : CollatzResearch.WordTrace tailWord_4613815 prefixEnd_4613815 2369104745923971161293957 := by
  unfold tailWord_4613815
  simp only [CollatzResearch.WordTrace]
  refine ⟨168279657779943706713066899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112186438519962471142044599 168279657779943706713066899)
  ·
    refine ⟨252419486669915560069600349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 168279657779943706713066899 252419486669915560069600349)
    ·
      refine ⟨94657307501218335026100131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 252419486669915560069600349 94657307501218335026100131)
      ·
        refine ⟨141985961251827502539150197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 94657307501218335026100131 141985961251827502539150197)
        ·
          refine ⟨13311183867358828363045331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 141985961251827502539150197 13311183867358828363045331)
          ·
            refine ⟨19966775801038242544567997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13311183867358828363045331 19966775801038242544567997)
            ·
              refine ⟨7487540925389340954212999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19966775801038242544567997 7487540925389340954212999)
              ·
                refine ⟨11231311388084011431319499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7487540925389340954212999 11231311388084011431319499)
                ·
                  refine ⟨16846967082126017146979249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11231311388084011431319499 16846967082126017146979249)
                  ·
                    refine ⟨12635225311594512860234437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16846967082126017146979249 12635225311594512860234437)
                    ·
                      refine ⟨2369104745923971161293957, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12635225311594512860234437 2369104745923971161293957)
                      ·
                        rfl

theorem cell23_4613815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 3, 1, 1, 2, 4].length) (baseStart_4613815 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4613815 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4613815 prefixEnd_4613815 := by exact prefixLift 4613815
  have htrace : WordTrace (prefixWord ++ tailWord_4613815) baseStart_4613815 baseEnd_4613815 := by
    simpa [prefixWord, tailWord_4613815, baseEnd_4613815] using wordTrace_append hprefix tailTrace_4613815
  have hstable : (prefixWord ++ tailWord_4613815).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4613815).length < 2 ^ (prefixWord ++ tailWord_4613815).sum := by decide
  have hdescent : baseEnd_4613815 < baseStart_4613815 := by decide
  rcases family_descends (prefixWord ++ tailWord_4613815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4613822 : List Nat := [4, 2, 1, 1, 2, 2, 1, 4, 1, 2, 3]
def baseStart_4613822 : Nat := 118140960795 + 4613822 * 2 ^ 59
def prefixEnd_4613822 : Nat := 4983230072969 + 3 ^ 40 * 4613822 * 2
def baseEnd_4613822 : Nat := 2369108340288552633906425

theorem tailTrace_4613822 : CollatzResearch.WordTrace tailWord_4613822 prefixEnd_4613822 2369108340288552633906425 := by
  unfold tailWord_4613822
  simp only [CollatzResearch.WordTrace]
  refine ⟨21034989136364793363571465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 112186608727278897939047813 21034989136364793363571465)
  ·
    refine ⟨15776241852273595022678599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21034989136364793363571465 15776241852273595022678599)
    ·
      refine ⟨23664362778410392534017899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15776241852273595022678599 23664362778410392534017899)
      ·
        refine ⟨35496544167615588801026849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23664362778410392534017899 35496544167615588801026849)
        ·
          refine ⟨26622408125711691600770137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35496544167615588801026849 26622408125711691600770137)
          ·
            refine ⟨19966806094283768700577603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26622408125711691600770137 19966806094283768700577603)
            ·
              refine ⟨29950209141425653050866405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19966806094283768700577603 29950209141425653050866405)
              ·
                refine ⟨5615664214017309947037451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 29950209141425653050866405 5615664214017309947037451)
                ·
                  refine ⟨8423496321025964920556177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5615664214017309947037451 8423496321025964920556177)
                  ·
                    refine ⟨6317622240769473690417133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8423496321025964920556177 6317622240769473690417133)
                    ·
                      refine ⟨2369108340288552633906425, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6317622240769473690417133 2369108340288552633906425)
                      ·
                        rfl

theorem cell23_4613822_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 1, 4, 1, 2, 3].length) (baseStart_4613822 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4613822 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4613822 prefixEnd_4613822 := by exact prefixLift 4613822
  have htrace : WordTrace (prefixWord ++ tailWord_4613822) baseStart_4613822 baseEnd_4613822 := by
    simpa [prefixWord, tailWord_4613822, baseEnd_4613822] using wordTrace_append hprefix tailTrace_4613822
  have hstable : (prefixWord ++ tailWord_4613822).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4613822).length < 2 ^ (prefixWord ++ tailWord_4613822).sum := by decide
  have hdescent : baseEnd_4613822 < baseStart_4613822 := by decide
  rcases family_descends (prefixWord ++ tailWord_4613822) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
