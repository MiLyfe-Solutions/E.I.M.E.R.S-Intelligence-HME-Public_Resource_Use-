import V185TrunkScan21Chunk020

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental

namespace V185TrunkScan21Incremental

def tailWord_254103 : List Nat := [1, 1, 3, 3, 5, 1, 1, 1, 5]
def baseStart_254103 : Nat := 118140960795 + 254103 * 2 ^ 59
def prefixEnd_254103 : Nat := 4983230072969 + 3 ^ 40 * 254103 * 2
def baseEnd_254103 : Nat := 57989766555344246463959

theorem tailTrace_254103 : CollatzResearch.WordTrace tailWord_254103 prefixEnd_254103 57989766555344246463959 := by
  unfold tailWord_254103
  simp only [CollatzResearch.WordTrace]
  refine ⟨9267897798435703182470963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6178598532290468788313975 9267897798435703182470963)
  ·
    refine ⟨13901846697653554773706445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9267897798435703182470963 13901846697653554773706445)
    ·
      refine ⟨5213192511620083040139917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13901846697653554773706445 5213192511620083040139917)
      ·
        refine ⟨1954947191857531140052469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5213192511620083040139917 1954947191857531140052469)
        ·
          refine ⟨183276299236643544379919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 1954947191857531140052469 183276299236643544379919)
          ·
            refine ⟨274914448854965316569879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 183276299236643544379919 274914448854965316569879)
            ·
              refine ⟨412371673282447974854819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 274914448854965316569879 412371673282447974854819)
              ·
                refine ⟨618557509923671962282229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 412371673282447974854819 618557509923671962282229)
                ·
                  refine ⟨57989766555344246463959, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 618557509923671962282229 57989766555344246463959)
                  ·
                    rfl

theorem cell21_254103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 5, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 5, 1, 1, 1, 5].length) (baseStart_254103 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_254103 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_254103 prefixEnd_254103 := by exact prefixLift 254103
  have htrace : WordTrace (prefixWord ++ tailWord_254103) baseStart_254103 baseEnd_254103 := by
    simpa [prefixWord, tailWord_254103, baseEnd_254103] using wordTrace_append hprefix tailTrace_254103
  have hstable : (prefixWord ++ tailWord_254103).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_254103).length < 2 ^ (prefixWord ++ tailWord_254103).sum := by decide
  have hdescent : baseEnd_254103 < baseStart_254103 := by decide
  rcases family_descends (prefixWord ++ tailWord_254103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_254210 : List Nat := [3, 4, 1, 1, 2, 3, 1, 2, 4]
def baseStart_254210 : Nat := 118140960795 + 254210 * 2 ^ 59
def prefixEnd_254210 : Nat := 4983230072969 + 3 ^ 40 * 254210 * 2
def baseEnd_254210 : Nat := 58014185413135838180407

theorem tailTrace_254210 : CollatzResearch.WordTrace tailWord_254210 prefixEnd_254210 58014185413135838180407 := by
  unfold tailWord_254210
  simp only [CollatzResearch.WordTrace]
  refine ⟨2317950102262015114154021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6181200272698706971077389 2317950102262015114154021)
  ·
    refine ⟨434615644174127833903879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2317950102262015114154021 434615644174127833903879)
    ·
      refine ⟨651923466261191750855819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 434615644174127833903879 651923466261191750855819)
      ·
        refine ⟨977885199391787626283729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 651923466261191750855819 977885199391787626283729)
        ·
          refine ⟨733413899543840719712797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 977885199391787626283729 733413899543840719712797)
          ·
            refine ⟨275030212328940269892299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 733413899543840719712797 275030212328940269892299)
            ·
              refine ⟨412545318493410404838449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 275030212328940269892299 412545318493410404838449)
              ·
                refine ⟨309408988870057803628837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 412545318493410404838449 309408988870057803628837)
                ·
                  refine ⟨58014185413135838180407, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 309408988870057803628837 58014185413135838180407)
                  ·
                    rfl

theorem cell21_254210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 3, 1, 2, 4].length) (baseStart_254210 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_254210 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_254210 prefixEnd_254210 := by exact prefixLift 254210
  have htrace : WordTrace (prefixWord ++ tailWord_254210) baseStart_254210 baseEnd_254210 := by
    simpa [prefixWord, tailWord_254210, baseEnd_254210] using wordTrace_append hprefix tailTrace_254210
  have hstable : (prefixWord ++ tailWord_254210).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_254210).length < 2 ^ (prefixWord ++ tailWord_254210).sum := by decide
  have hdescent : baseEnd_254210 < baseStart_254210 := by decide
  rcases family_descends (prefixWord ++ tailWord_254210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_254235 : List Nat := [1, 1, 1, 1, 1, 1, 6, 5, 4]
def baseStart_254235 : Nat := 118140960795 + 254235 * 2 ^ 59
def prefixEnd_254235 : Nat := 4983230072969 + 3 ^ 40 * 254235 * 2
def baseEnd_254235 : Nat := 58019890753741350263689

theorem tailTrace_254235 : CollatzResearch.WordTrace tailWord_254235 prefixEnd_254235 58019890753741350263689 := by
  unfold tailWord_254235
  simp only [CollatzResearch.WordTrace]
  refine ⟨9272712233957489726276159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6181808155971659817517439 9272712233957489726276159)
  ·
    refine ⟨13909068350936234589414239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9272712233957489726276159 13909068350936234589414239)
    ·
      refine ⟨20863602526404351884121359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13909068350936234589414239 20863602526404351884121359)
      ·
        refine ⟨31295403789606527826182039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20863602526404351884121359 31295403789606527826182039)
        ·
          refine ⟨46943105684409791739273059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31295403789606527826182039 46943105684409791739273059)
          ·
            refine ⟨70414658526614687608909589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46943105684409791739273059 70414658526614687608909589)
            ·
              refine ⟨3300687118435063481667637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 70414658526614687608909589 3300687118435063481667637)
              ·
                refine ⟨309439417353287201406341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3300687118435063481667637 309439417353287201406341)
                ·
                  refine ⟨58019890753741350263689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 309439417353287201406341 58019890753741350263689)
                  ·
                    rfl

theorem cell21_254235_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 6, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 6, 5, 4].length) (baseStart_254235 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_254235 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_254235 prefixEnd_254235 := by exact prefixLift 254235
  have htrace : WordTrace (prefixWord ++ tailWord_254235) baseStart_254235 baseEnd_254235 := by
    simpa [prefixWord, tailWord_254235, baseEnd_254235] using wordTrace_append hprefix tailTrace_254235
  have hstable : (prefixWord ++ tailWord_254235).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_254235).length < 2 ^ (prefixWord ++ tailWord_254235).sum := by decide
  have hdescent : baseEnd_254235 < baseStart_254235 := by decide
  rcases family_descends (prefixWord ++ tailWord_254235) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_254266 : List Nat := [3, 1, 1, 1, 4, 4, 7]
def baseStart_254266 : Nat := 118140960795 + 254266 * 2 ^ 59
def prefixEnd_254266 : Nat := 4983230072969 + 3 ^ 40 * 254266 * 2
def baseEnd_254266 : Nat := 6447440597343576138551

theorem tailTrace_254266 : CollatzResearch.WordTrace tailWord_254266 prefixEnd_254266 6447440597343576138551 := by
  unfold tailWord_254266
  simp only [CollatzResearch.WordTrace]
  refine ⟨2318460724211295505163663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6182561931230121347103101 2318460724211295505163663)
  ·
    refine ⟨3477691086316943257745495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2318460724211295505163663 3477691086316943257745495)
    ·
      refine ⟨5216536629475414886618243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3477691086316943257745495 5216536629475414886618243)
      ·
        refine ⟨7824804944213122329927365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5216536629475414886618243 7824804944213122329927365)
        ·
          refine ⟨1467150927039960436861381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7824804944213122329927365 1467150927039960436861381)
          ·
            refine ⟨275090798819992581911509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1467150927039960436861381 275090798819992581911509)
            ·
              refine ⟨6447440597343576138551, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 275090798819992581911509 6447440597343576138551)
              ·
                rfl

theorem cell21_254266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 4, 7].length) (baseStart_254266 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_254266 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_254266 prefixEnd_254266 := by exact prefixLift 254266
  have htrace : WordTrace (prefixWord ++ tailWord_254266) baseStart_254266 baseEnd_254266 := by
    simpa [prefixWord, tailWord_254266, baseEnd_254266] using wordTrace_append hprefix tailTrace_254266
  have hstable : (prefixWord ++ tailWord_254266).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_254266).length < 2 ^ (prefixWord ++ tailWord_254266).sum := by decide
  have hdescent : baseEnd_254266 < baseStart_254266 := by decide
  rcases family_descends (prefixWord ++ tailWord_254266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_254331 : List Nat := [1, 1, 1, 1, 1, 9, 2, 2, 3]
def baseStart_254331 : Nat := 118140960795 + 254331 * 2 ^ 59
def prefixEnd_254331 : Nat := 4983230072969 + 3 ^ 40 * 254331 * 2
def baseEnd_254331 : Nat := 58041799261666516663493

theorem tailTrace_254331 : CollatzResearch.WordTrace tailWord_254331 prefixEnd_254331 58041799261666516663493 := by
  unfold tailWord_254331
  simp only [CollatzResearch.WordTrace]
  refine ⟨9276213641609698121770847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6184142427739798747847231 9276213641609698121770847)
  ·
    refine ⟨13914320462414547182656271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9276213641609698121770847 13914320462414547182656271)
    ·
      refine ⟨20871480693621820773984407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13914320462414547182656271 20871480693621820773984407)
      ·
        refine ⟨31307221040432731160976611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20871480693621820773984407 31307221040432731160976611)
        ·
          refine ⟨46960831560649096741464917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31307221040432731160976611 46960831560649096741464917)
          ·
            refine ⟨275161122425678301219521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 46960831560649096741464917 275161122425678301219521)
            ·
              refine ⟨206370841819258725914641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 275161122425678301219521 206370841819258725914641)
              ·
                refine ⟨154778131364444044435981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 206370841819258725914641 154778131364444044435981)
                ·
                  refine ⟨58041799261666516663493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 154778131364444044435981 58041799261666516663493)
                  ·
                    rfl

theorem cell21_254331_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 9, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 9, 2, 2, 3].length) (baseStart_254331 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_254331 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_254331 prefixEnd_254331 := by exact prefixLift 254331
  have htrace : WordTrace (prefixWord ++ tailWord_254331) baseStart_254331 baseEnd_254331 := by
    simpa [prefixWord, tailWord_254331, baseEnd_254331] using wordTrace_append hprefix tailTrace_254331
  have hstable : (prefixWord ++ tailWord_254331).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_254331).length < 2 ^ (prefixWord ++ tailWord_254331).sum := by decide
  have hdescent : baseEnd_254331 < baseStart_254331 := by decide
  rcases family_descends (prefixWord ++ tailWord_254331) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_254435 : List Nat := [1, 1, 1, 6, 4, 1, 7]
def baseStart_254435 : Nat := 118140960795 + 254435 * 2 ^ 59
def prefixEnd_254435 : Nat := 4983230072969 + 3 ^ 40 * 254435 * 2
def baseEnd_254435 : Nat := 6451725942065049658883

theorem tailTrace_254435 : CollatzResearch.WordTrace tailWord_254435 prefixEnd_254435 6451725942065049658883 := by
  unfold tailWord_254435
  simp only [CollatzResearch.WordTrace]
  refine ⟨9280006833232923883556759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6186671222155282589037839 9280006833232923883556759)
  ·
    refine ⟨13920010249849385825335139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9280006833232923883556759 13920010249849385825335139)
    ·
      refine ⟨20880015374774078738002709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13920010249849385825335139 20880015374774078738002709)
      ·
        refine ⟨978750720692534940843877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 20880015374774078738002709 978750720692534940843877)
        ·
          refine ⟨183515760129850301408227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 978750720692534940843877 183515760129850301408227)
          ·
            refine ⟨275273640194775452112341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 183515760129850301408227 275273640194775452112341)
            ·
              refine ⟨6451725942065049658883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 275273640194775452112341 6451725942065049658883)
              ·
                rfl

theorem cell21_254435_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 4, 1, 7].length) (baseStart_254435 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_254435 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_254435 prefixEnd_254435 := by exact prefixLift 254435
  have htrace : WordTrace (prefixWord ++ tailWord_254435) baseStart_254435 baseEnd_254435 := by
    simpa [prefixWord, tailWord_254435, baseEnd_254435] using wordTrace_append hprefix tailTrace_254435
  have hstable : (prefixWord ++ tailWord_254435).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_254435).length < 2 ^ (prefixWord ++ tailWord_254435).sum := by decide
  have hdescent : baseEnd_254435 < baseStart_254435 := by decide
  rcases family_descends (prefixWord ++ tailWord_254435) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_254463 : List Nat := [1, 1, 2, 2, 1, 2, 5, 3, 4]
def baseStart_254463 : Nat := 118140960795 + 254463 * 2 ^ 59
def prefixEnd_254463 : Nat := 4983230072969 + 3 ^ 40 * 254463 * 2
def baseEnd_254463 : Nat := 58071923460063620463223

theorem tailTrace_254463 : CollatzResearch.WordTrace tailWord_254463 prefixEnd_254463 58071923460063620463223 := by
  unfold tailWord_254463
  simp only [CollatzResearch.WordTrace]
  refine ⟨9281028077131484665576043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6187352051420989777050695 9281028077131484665576043)
  ·
    refine ⟨13921542115697226998364065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9281028077131484665576043 13921542115697226998364065)
    ·
      refine ⟨10441156586772920248773049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13921542115697226998364065 10441156586772920248773049)
      ·
        refine ⟨7830867440079690186579787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10441156586772920248773049 7830867440079690186579787)
        ·
          refine ⟨11746301160119535279869681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7830867440079690186579787 11746301160119535279869681)
          ·
            refine ⟨8809725870089651459902261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11746301160119535279869681 8809725870089651459902261)
            ·
              refine ⟨825911800320904824365837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 8809725870089651459902261 825911800320904824365837)
              ·
                refine ⟨309716925120339309137189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 825911800320904824365837 309716925120339309137189)
                ·
                  refine ⟨58071923460063620463223, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 309716925120339309137189 58071923460063620463223)
                  ·
                    rfl

theorem cell21_254463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 5, 3, 4].length) (baseStart_254463 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_254463 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_254463 prefixEnd_254463 := by exact prefixLift 254463
  have htrace : WordTrace (prefixWord ++ tailWord_254463) baseStart_254463 baseEnd_254463 := by
    simpa [prefixWord, tailWord_254463, baseEnd_254463] using wordTrace_append hprefix tailTrace_254463
  have hstable : (prefixWord ++ tailWord_254463).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_254463).length < 2 ^ (prefixWord ++ tailWord_254463).sum := by decide
  have hdescent : baseEnd_254463 < baseStart_254463 := by decide
  rcases family_descends (prefixWord ++ tailWord_254463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_254525 : List Nat := [1, 4, 1, 3, 2, 2, 1, 2, 5]
def baseStart_254525 : Nat := 118140960795 + 254525 * 2 ^ 59
def prefixEnd_254525 : Nat := 4983230072969 + 3 ^ 40 * 254525 * 2
def baseEnd_254525 : Nat := 58086072704765290429763

theorem tailTrace_254525 : CollatzResearch.WordTrace tailWord_254525 prefixEnd_254525 58086072704765290429763 := by
  unfold tailWord_254525
  simp only [CollatzResearch.WordTrace]
  refine ⟨9283289402906869254333029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6188859601937912836222019 9283289402906869254333029)
  ·
    refine ⟨1740616763045037985187443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 9283289402906869254333029 1740616763045037985187443)
    ·
      refine ⟨2610925144567556977781165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1740616763045037985187443 2610925144567556977781165)
      ·
        refine ⟨979096929212833866667937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2610925144567556977781165 979096929212833866667937)
        ·
          refine ⟨734322696909625400000953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 979096929212833866667937 734322696909625400000953)
          ·
            refine ⟨550742022682219050000715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 734322696909625400000953 550742022682219050000715)
            ·
              refine ⟨826113034023328575001073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 550742022682219050000715 826113034023328575001073)
              ·
                refine ⟨619584775517496431250805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 826113034023328575001073 619584775517496431250805)
                ·
                  refine ⟨58086072704765290429763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 619584775517496431250805 58086072704765290429763)
                  ·
                    rfl

theorem cell21_254525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 2, 1, 2, 5].length) (baseStart_254525 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_254525 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_254525 prefixEnd_254525 := by exact prefixLift 254525
  have htrace : WordTrace (prefixWord ++ tailWord_254525) baseStart_254525 baseEnd_254525 := by
    simpa [prefixWord, tailWord_254525, baseEnd_254525] using wordTrace_append hprefix tailTrace_254525
  have hstable : (prefixWord ++ tailWord_254525).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_254525).length < 2 ^ (prefixWord ++ tailWord_254525).sum := by decide
  have hdescent : baseEnd_254525 < baseStart_254525 := by decide
  rcases family_descends (prefixWord ++ tailWord_254525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_254556 : List Nat := [2, 2, 4, 1, 3, 1, 1, 1, 6]
def baseStart_254556 : Nat := 118140960795 + 254556 * 2 ^ 59
def prefixEnd_254556 : Nat := 4983230072969 + 3 ^ 40 * 254556 * 2
def baseEnd_254556 : Nat := 58093147327116125413033

theorem tailTrace_254556 : CollatzResearch.WordTrace tailWord_254556 prefixEnd_254556 58093147327116125413033 := by
  unfold tailWord_254556
  simp only [CollatzResearch.WordTrace]
  refine ⟨4642210032897280774355761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6189613377196374365807681 4642210032897280774355761)
  ·
    refine ⟨3481657524672960580766821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4642210032897280774355761 3481657524672960580766821)
    ·
      refine ⟨652810785876180108893779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3481657524672960580766821 652810785876180108893779)
      ·
        refine ⟨979216178814270163340669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 652810785876180108893779 979216178814270163340669)
        ·
          refine ⟨367206067055351311252751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 979216178814270163340669 367206067055351311252751)
          ·
            refine ⟨550809100583026966879127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 367206067055351311252751 550809100583026966879127)
            ·
              refine ⟨826213650874540450318691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 550809100583026966879127 826213650874540450318691)
              ·
                refine ⟨1239320476311810675478037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 826213650874540450318691 1239320476311810675478037)
                ·
                  refine ⟨58093147327116125413033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1239320476311810675478037 58093147327116125413033)
                  ·
                    rfl

theorem cell21_254556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 3, 1, 1, 1, 6].length) (baseStart_254556 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_254556 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_254556 prefixEnd_254556 := by exact prefixLift 254556
  have htrace : WordTrace (prefixWord ++ tailWord_254556) baseStart_254556 baseEnd_254556 := by
    simpa [prefixWord, tailWord_254556, baseEnd_254556] using wordTrace_append hprefix tailTrace_254556
  have hstable : (prefixWord ++ tailWord_254556).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_254556).length < 2 ^ (prefixWord ++ tailWord_254556).sum := by decide
  have hdescent : baseEnd_254556 < baseStart_254556 := by decide
  rcases family_descends (prefixWord ++ tailWord_254556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_254573 : List Nat := [1, 5, 1, 1, 3, 2, 3, 1, 4]
def baseStart_254573 : Nat := 118140960795 + 254573 * 2 ^ 59
def prefixEnd_254573 : Nat := 4983230072969 + 3 ^ 40 * 254573 * 2
def baseEnd_254573 : Nat := 58097026958727873629665

theorem tailTrace_254573 : CollatzResearch.WordTrace tailWord_254573 prefixEnd_254573 58097026958727873629665 := by
  unfold tailWord_254573
  simp only [CollatzResearch.WordTrace]
  refine ⟨9285040106732973452080373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6190026737821982301386915 9285040106732973452080373)
  ·
    refine ⟨870472510006216261132535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 9285040106732973452080373 870472510006216261132535)
    ·
      refine ⟨1305708765009324391698803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 870472510006216261132535 1305708765009324391698803)
      ·
        refine ⟨1958563147513986587548205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1305708765009324391698803 1958563147513986587548205)
        ·
          refine ⟨734461180317744970330577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1958563147513986587548205 734461180317744970330577)
          ·
            refine ⟨550845885238308727747933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 734461180317744970330577 550845885238308727747933)
            ·
              refine ⟨206567206964365772905475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 550845885238308727747933 206567206964365772905475)
              ·
                refine ⟨309850810446548659358213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 206567206964365772905475 309850810446548659358213)
                ·
                  refine ⟨58097026958727873629665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 309850810446548659358213 58097026958727873629665)
                  ·
                    rfl

theorem cell21_254573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 2, 3, 1, 4].length) (baseStart_254573 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_254573 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_254573 prefixEnd_254573 := by exact prefixLift 254573
  have htrace : WordTrace (prefixWord ++ tailWord_254573) baseStart_254573 baseEnd_254573 := by
    simpa [prefixWord, tailWord_254573, baseEnd_254573] using wordTrace_append hprefix tailTrace_254573
  have hstable : (prefixWord ++ tailWord_254573).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_254573).length < 2 ^ (prefixWord ++ tailWord_254573).sum := by decide
  have hdescent : baseEnd_254573 < baseStart_254573 := by decide
  rcases family_descends (prefixWord ++ tailWord_254573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_254615 : List Nat := [1, 1, 3, 3, 2, 1, 2, 4, 4]
def baseStart_254615 : Nat := 118140960795 + 254615 * 2 ^ 59
def prefixEnd_254615 : Nat := 4983230072969 + 3 ^ 40 * 254615 * 2
def baseEnd_254615 : Nat := 58106611930945133929579

theorem tailTrace_254615 : CollatzResearch.WordTrace tailWord_254615 prefixEnd_254615 58106611930945133929579 := by
  unfold tailWord_254615
  simp only [CollatzResearch.WordTrace]
  refine ⟨9286571972580814625109299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6191047981720543083406199 9286571972580814625109299)
  ·
    refine ⟨13929857958871221937663949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9286571972580814625109299 13929857958871221937663949)
    ·
      refine ⟨5223696734576708226623981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13929857958871221937663949 5223696734576708226623981)
      ·
        refine ⟨1958886275466265584983993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5223696734576708226623981 1958886275466265584983993)
        ·
          refine ⟨1469164706599699188737995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1958886275466265584983993 1469164706599699188737995)
          ·
            refine ⟨2203747059899548783106993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1469164706599699188737995 2203747059899548783106993)
            ·
              refine ⟨1652810294924661587330245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2203747059899548783106993 1652810294924661587330245)
              ·
                refine ⟨309901930298374047624421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1652810294924661587330245 309901930298374047624421)
                ·
                  refine ⟨58106611930945133929579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 309901930298374047624421 58106611930945133929579)
                  ·
                    rfl

theorem cell21_254615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 2, 4, 4].length) (baseStart_254615 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_254615 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_254615 prefixEnd_254615 := by exact prefixLift 254615
  have htrace : WordTrace (prefixWord ++ tailWord_254615) baseStart_254615 baseEnd_254615 := by
    simpa [prefixWord, tailWord_254615, baseEnd_254615] using wordTrace_append hprefix tailTrace_254615
  have hstable : (prefixWord ++ tailWord_254615).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_254615).length < 2 ^ (prefixWord ++ tailWord_254615).sum := by decide
  have hdescent : baseEnd_254615 < baseStart_254615 := by decide
  rcases family_descends (prefixWord ++ tailWord_254615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_254669 : List Nat := [1, 6, 2, 1, 2, 2, 2, 2, 3]
def baseStart_254669 : Nat := 118140960795 + 254669 * 2 ^ 59
def prefixEnd_254669 : Nat := 4983230072969 + 3 ^ 40 * 254669 * 2
def baseEnd_254669 : Nat := 58118935466653040029469

theorem tailTrace_254669 : CollatzResearch.WordTrace tailWord_254669 prefixEnd_254669 58118935466653040029469 := by
  unfold tailWord_254669
  simp only [CollatzResearch.WordTrace]
  refine ⟨9288541514385181847575061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6192361009590121231716707 9288541514385181847575061)
  ·
    refine ⟨435400383486805399105081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 9288541514385181847575061 435400383486805399105081)
    ·
      refine ⟨326550287615104049328811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 435400383486805399105081 326550287615104049328811)
      ·
        refine ⟨489825431422656073993217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 326550287615104049328811 489825431422656073993217)
        ·
          refine ⟨367369073566992055494913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 489825431422656073993217 367369073566992055494913)
          ·
            refine ⟨275526805175244041621185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 367369073566992055494913 275526805175244041621185)
            ·
              refine ⟨206645103881433031215889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 275526805175244041621185 206645103881433031215889)
              ·
                refine ⟨154983827911074773411917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 206645103881433031215889 154983827911074773411917)
                ·
                  refine ⟨58118935466653040029469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 154983827911074773411917 58118935466653040029469)
                  ·
                    rfl

theorem cell21_254669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 2, 2, 2, 2, 3].length) (baseStart_254669 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_254669 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_254669 prefixEnd_254669 := by exact prefixLift 254669
  have htrace : WordTrace (prefixWord ++ tailWord_254669) baseStart_254669 baseEnd_254669 := by
    simpa [prefixWord, tailWord_254669, baseEnd_254669] using wordTrace_append hprefix tailTrace_254669
  have hstable : (prefixWord ++ tailWord_254669).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_254669).length < 2 ^ (prefixWord ++ tailWord_254669).sum := by decide
  have hdescent : baseEnd_254669 < baseStart_254669 := by decide
  rcases family_descends (prefixWord ++ tailWord_254669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_254719 : List Nat := [1, 1, 2, 2, 1, 3, 1, 1, 9]
def baseStart_254719 : Nat := 118140960795 + 254719 * 2 ^ 59
def prefixEnd_254719 : Nat := 4983230072969 + 3 ^ 40 * 254719 * 2
def baseEnd_254719 : Nat := 58130346147864064196033

theorem tailTrace_254719 : CollatzResearch.WordTrace tailWord_254719 prefixEnd_254719 58130346147864064196033 := by
  unfold tailWord_254719
  simp only [CollatzResearch.WordTrace]
  refine ⟨9290365164204040386895211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6193576776136026924596807 9290365164204040386895211)
  ·
    refine ⟨13935547746306060580342817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9290365164204040386895211 13935547746306060580342817)
    ·
      refine ⟨10451660809729545435257113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13935547746306060580342817 10451660809729545435257113)
      ·
        refine ⟨7838745607297159076442835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10451660809729545435257113 7838745607297159076442835)
        ·
          refine ⟨11758118410945738614664253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7838745607297159076442835 11758118410945738614664253)
          ·
            refine ⟨4409294404104651980499095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11758118410945738614664253 4409294404104651980499095)
            ·
              refine ⟨6613941606156977970748643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4409294404104651980499095 6613941606156977970748643)
              ·
                refine ⟨9920912409235466956122965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6613941606156977970748643 9920912409235466956122965)
                ·
                  refine ⟨58130346147864064196033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 9920912409235466956122965 58130346147864064196033)
                  ·
                    rfl

theorem cell21_254719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 1, 1, 9].length) (baseStart_254719 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_254719 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_254719 prefixEnd_254719 := by exact prefixLift 254719
  have htrace : WordTrace (prefixWord ++ tailWord_254719) baseStart_254719 baseEnd_254719 := by
    simpa [prefixWord, tailWord_254719, baseEnd_254719] using wordTrace_append hprefix tailTrace_254719
  have hstable : (prefixWord ++ tailWord_254719).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_254719).length < 2 ^ (prefixWord ++ tailWord_254719).sum := by decide
  have hdescent : baseEnd_254719 < baseStart_254719 := by decide
  rcases family_descends (prefixWord ++ tailWord_254719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_254722 : List Nat := [3, 4, 1, 1, 1, 3, 8]
def baseStart_254722 : Nat := 118140960795 + 254722 * 2 ^ 59
def prefixEnd_254722 : Nat := 4983230072969 + 3 ^ 40 * 254722 * 2
def baseEnd_254722 : Nat := 6459003420970747294003

theorem tailTrace_254722 : CollatzResearch.WordTrace tailWord_254722 prefixEnd_254722 6459003420970747294003 := by
  unfold tailWord_254722
  simp only [CollatzResearch.WordTrace]
  refine ⟨2322618645798292974813605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6193649722128781266169613 2322618645798292974813605)
  ·
    refine ⟨435490996087179932777551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2322618645798292974813605 435490996087179932777551)
    ·
      refine ⟨653236494130769899166327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 435490996087179932777551 653236494130769899166327)
      ·
        refine ⟨979854741196154848749491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 653236494130769899166327 979854741196154848749491)
        ·
          refine ⟨1469782111794232273124237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 979854741196154848749491 1469782111794232273124237)
          ·
            refine ⟨551168291922837102421589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1469782111794232273124237 551168291922837102421589)
            ·
              refine ⟨6459003420970747294003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 551168291922837102421589 6459003420970747294003)
              ·
                rfl

theorem cell21_254722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 3, 8].length) (baseStart_254722 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_254722 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_254722 prefixEnd_254722 := by exact prefixLift 254722
  have htrace : WordTrace (prefixWord ++ tailWord_254722) baseStart_254722 baseEnd_254722 := by
    simpa [prefixWord, tailWord_254722, baseEnd_254722] using wordTrace_append hprefix tailTrace_254722
  have hstable : (prefixWord ++ tailWord_254722).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_254722).length < 2 ^ (prefixWord ++ tailWord_254722).sum := by decide
  have hdescent : baseEnd_254722 < baseStart_254722 := by decide
  rcases family_descends (prefixWord ++ tailWord_254722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_254756 : List Nat := [2, 3, 1, 3, 4, 1, 2, 5]
def baseStart_254756 : Nat := 118140960795 + 254756 * 2 ^ 59
def prefixEnd_254756 : Nat := 4983230072969 + 3 ^ 40 * 254756 * 2
def baseEnd_254756 : Nat := 19379596683986740693097

theorem tailTrace_254756 : CollatzResearch.WordTrace tailWord_254756 prefixEnd_254756 19379596683986740693097 := by
  unfold tailWord_254756
  simp only [CollatzResearch.WordTrace]
  refine ⟨4645857332534997852996061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6194476443379997137328081 4645857332534997852996061)
  ·
    refine ⟨1742196499700624194873523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4645857332534997852996061 1742196499700624194873523)
    ·
      refine ⟨2613294749550936292310285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1742196499700624194873523 2613294749550936292310285)
      ·
        refine ⟨979985531081601109616357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2613294749550936292310285 979985531081601109616357)
        ·
          refine ⟨183747287077800208053067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 979985531081601109616357 183747287077800208053067)
          ·
            refine ⟨275620930616700312079601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 183747287077800208053067 275620930616700312079601)
            ·
              refine ⟨206715697962525234059701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 275620930616700312079601 206715697962525234059701)
              ·
                refine ⟨19379596683986740693097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 206715697962525234059701 19379596683986740693097)
                ·
                  rfl

theorem cell21_254756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 4, 1, 2, 5].length) (baseStart_254756 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_254756 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_254756 prefixEnd_254756 := by exact prefixLift 254756
  have htrace : WordTrace (prefixWord ++ tailWord_254756) baseStart_254756 baseEnd_254756 := by
    simpa [prefixWord, tailWord_254756, baseEnd_254756] using wordTrace_append hprefix tailTrace_254756
  have hstable : (prefixWord ++ tailWord_254756).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_254756).length < 2 ^ (prefixWord ++ tailWord_254756).sum := by decide
  have hdescent : baseEnd_254756 < baseStart_254756 := by decide
  rcases family_descends (prefixWord ++ tailWord_254756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_254801 : List Nat := [1, 2, 2, 1, 6, 2, 2, 1, 4]
def baseStart_254801 : Nat := 118140960795 + 254801 * 2 ^ 59
def prefixEnd_254801 : Nat := 4983230072969 + 3 ^ 40 * 254801 * 2
def baseEnd_254801 : Nat := 58149059665050143829199

theorem tailTrace_254801 : CollatzResearch.WordTrace tailWord_254801 prefixEnd_254801 58149059665050143829199 := by
  unfold tailWord_254801
  simp only [CollatzResearch.WordTrace]
  refine ⟨9293355949906968391380257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6195570633271312260920171 9293355949906968391380257)
  ·
    refine ⟨6970016962430226293535193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9293355949906968391380257 6970016962430226293535193)
    ·
      refine ⟨5227512721822669720151395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6970016962430226293535193 5227512721822669720151395)
      ·
        refine ⟨7841269082734004580227093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5227512721822669720151395 7841269082734004580227093)
        ·
          refine ⟨367559488253156464698145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 7841269082734004580227093 367559488253156464698145)
          ·
            refine ⟨275669616189867348523609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 367559488253156464698145 275669616189867348523609)
            ·
              refine ⟨206752212142400511392707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 275669616189867348523609 206752212142400511392707)
              ·
                refine ⟨310128318213600767089061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 206752212142400511392707 310128318213600767089061)
                ·
                  refine ⟨58149059665050143829199, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 310128318213600767089061 58149059665050143829199)
                  ·
                    rfl

theorem cell21_254801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 6, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 6, 2, 2, 1, 4].length) (baseStart_254801 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_254801 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_254801 prefixEnd_254801 := by exact prefixLift 254801
  have htrace : WordTrace (prefixWord ++ tailWord_254801) baseStart_254801 baseEnd_254801 := by
    simpa [prefixWord, tailWord_254801, baseEnd_254801] using wordTrace_append hprefix tailTrace_254801
  have hstable : (prefixWord ++ tailWord_254801).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_254801).length < 2 ^ (prefixWord ++ tailWord_254801).sum := by decide
  have hdescent : baseEnd_254801 < baseStart_254801 := by decide
  rcases family_descends (prefixWord ++ tailWord_254801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_254829 : List Nat := [1, 5, 1, 1, 1, 1, 1, 7, 3]
def baseStart_254829 : Nat := 118140960795 + 254829 * 2 ^ 59
def prefixEnd_254829 : Nat := 4983230072969 + 3 ^ 40 * 254829 * 2
def baseEnd_254829 : Nat := 58155449646528317362475

theorem tailTrace_254829 : CollatzResearch.WordTrace tailWord_254829 prefixEnd_254829 58155449646528317362475 := by
  unfold tailWord_254829
  simp only [CollatzResearch.WordTrace]
  refine ⟨9294377193805529173399541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6196251462537019448933027 9294377193805529173399541)
  ·
    refine ⟨871347861919268360006207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 9294377193805529173399541 871347861919268360006207)
    ·
      refine ⟨1307021792878902540009311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 871347861919268360006207 1307021792878902540009311)
      ·
        refine ⟨1960532689318353810013967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1307021792878902540009311 1960532689318353810013967)
        ·
          refine ⟨2940799033977530715020951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1960532689318353810013967 2940799033977530715020951)
          ·
            refine ⟨4411198550966296072531427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2940799033977530715020951 4411198550966296072531427)
            ·
              refine ⟨6616797826449444108797141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4411198550966296072531427 6616797826449444108797141)
              ·
                refine ⟨155081199057408846299933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6616797826449444108797141 155081199057408846299933)
                ·
                  refine ⟨58155449646528317362475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 155081199057408846299933 58155449646528317362475)
                  ·
                    rfl

theorem cell21_254829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 1, 7, 3].length) (baseStart_254829 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_254829 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_254829 prefixEnd_254829 := by exact prefixLift 254829
  have htrace : WordTrace (prefixWord ++ tailWord_254829) baseStart_254829 baseEnd_254829 := by
    simpa [prefixWord, tailWord_254829, baseEnd_254829] using wordTrace_append hprefix tailTrace_254829
  have hstable : (prefixWord ++ tailWord_254829).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_254829).length < 2 ^ (prefixWord ++ tailWord_254829).sum := by decide
  have hdescent : baseEnd_254829 < baseStart_254829 := by decide
  rcases family_descends (prefixWord ++ tailWord_254829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_254857 : List Nat := [1, 2, 1, 1, 5, 2, 3, 6]
def baseStart_254857 : Nat := 118140960795 + 254857 * 2 ^ 59
def prefixEnd_254857 : Nat := 4983230072969 + 3 ^ 40 * 254857 * 2
def baseEnd_254857 : Nat := 19387279876002163631917

theorem tailTrace_254857 : CollatzResearch.WordTrace tailWord_254857 prefixEnd_254857 19387279876002163631917 := by
  unfold tailWord_254857
  simp only [CollatzResearch.WordTrace]
  refine ⟨9295398437704089955418825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6196932291802726636945883 9295398437704089955418825)
  ·
    refine ⟨6971548828278067466564119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9295398437704089955418825 6971548828278067466564119)
    ·
      refine ⟨10457323242417101199846179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6971548828278067466564119 10457323242417101199846179)
      ·
        refine ⟨15685984863625651799769269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10457323242417101199846179 15685984863625651799769269)
        ·
          refine ⟨1470561080964904856228369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 15685984863625651799769269 1470561080964904856228369)
          ·
            refine ⟨1102920810723678642171277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1470561080964904856228369 1102920810723678642171277)
            ·
              refine ⟨413595304021379490814229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1102920810723678642171277 413595304021379490814229)
              ·
                refine ⟨19387279876002163631917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 413595304021379490814229 19387279876002163631917)
                ·
                  rfl

theorem cell21_254857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 3, 6].length) (baseStart_254857 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_254857 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_254857 prefixEnd_254857 := by exact prefixLift 254857
  have htrace : WordTrace (prefixWord ++ tailWord_254857) baseStart_254857 baseEnd_254857 := by
    simpa [prefixWord, tailWord_254857, baseEnd_254857] using wordTrace_append hprefix tailTrace_254857
  have hstable : (prefixWord ++ tailWord_254857).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_254857).length < 2 ^ (prefixWord ++ tailWord_254857).sum := by decide
  have hdescent : baseEnd_254857 < baseStart_254857 := by decide
  rcases family_descends (prefixWord ++ tailWord_254857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_254905 : List Nat := [1, 2, 1, 4, 2, 2, 2, 4, 3]
def baseStart_254905 : Nat := 118140960795 + 254905 * 2 ^ 59
def prefixEnd_254905 : Nat := 4983230072969 + 3 ^ 40 * 254905 * 2
def baseEnd_254905 : Nat := 58172793881969074095653

theorem tailTrace_254905 : CollatzResearch.WordTrace tailWord_254905 prefixEnd_254905 58172793881969074095653 := by
  unfold tailWord_254905
  simp only [CollatzResearch.WordTrace]
  refine ⟨9297149141530194153166169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6198099427686796102110779 9297149141530194153166169)
  ·
    refine ⟨6972861856147645614874627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9297149141530194153166169 6972861856147645614874627)
    ·
      refine ⟨10459292784221468422311941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6972861856147645614874627 10459292784221468422311941)
      ·
        refine ⟨1961117397041525329183489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10459292784221468422311941 1961117397041525329183489)
        ·
          refine ⟨1470838047781143996887617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1961117397041525329183489 1470838047781143996887617)
          ·
            refine ⟨1103128535835857997665713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1470838047781143996887617 1103128535835857997665713)
            ·
              refine ⟨827346401876893498249285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1103128535835857997665713 827346401876893498249285)
              ·
                refine ⟨155127450351917530921741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 827346401876893498249285 155127450351917530921741)
                ·
                  refine ⟨58172793881969074095653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 155127450351917530921741 58172793881969074095653)
                  ·
                    rfl

theorem cell21_254905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 2, 4, 3].length) (baseStart_254905 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_254905 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_254905 prefixEnd_254905 := by exact prefixLift 254905
  have htrace : WordTrace (prefixWord ++ tailWord_254905) baseStart_254905 baseEnd_254905 := by
    simpa [prefixWord, tailWord_254905, baseEnd_254905] using wordTrace_append hprefix tailTrace_254905
  have hstable : (prefixWord ++ tailWord_254905).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_254905).length < 2 ^ (prefixWord ++ tailWord_254905).sum := by decide
  have hdescent : baseEnd_254905 < baseStart_254905 := by decide
  rcases family_descends (prefixWord ++ tailWord_254905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_255012 : List Nat := [2, 3, 1, 4, 1, 2, 2, 2, 4]
def baseStart_255012 : Nat := 118140960795 + 255012 * 2 ^ 59
def prefixEnd_255012 : Nat := 4983230072969 + 3 ^ 40 * 255012 * 2
def baseEnd_255012 : Nat := 58197212739760665812101

theorem tailTrace_255012 : CollatzResearch.WordTrace tailWord_255012 prefixEnd_255012 58197212739760665812101 := by
  unfold tailWord_255012
  simp only [CollatzResearch.WordTrace]
  refine ⟨4650525876071275713655645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6200701168095034284874193 4650525876071275713655645)
  ·
    refine ⟨1743947203526728392620867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4650525876071275713655645 1743947203526728392620867)
    ·
      refine ⟨2615920805290092588931301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1743947203526728392620867 2615920805290092588931301)
      ·
        refine ⟨490485150991892360424619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2615920805290092588931301 490485150991892360424619)
        ·
          refine ⟨735727726487838540636929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 490485150991892360424619 735727726487838540636929)
          ·
            refine ⟨551795794865878905477697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 735727726487838540636929 551795794865878905477697)
            ·
              refine ⟨413846846149409179108273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 551795794865878905477697 413846846149409179108273)
              ·
                refine ⟨310385134612056884331205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 413846846149409179108273 310385134612056884331205)
                ·
                  refine ⟨58197212739760665812101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 310385134612056884331205 58197212739760665812101)
                  ·
                    rfl

theorem cell21_255012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 2, 2, 2, 4].length) (baseStart_255012 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_255012 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_255012 prefixEnd_255012 := by exact prefixLift 255012
  have htrace : WordTrace (prefixWord ++ tailWord_255012) baseStart_255012 baseEnd_255012 := by
    simpa [prefixWord, tailWord_255012, baseEnd_255012] using wordTrace_append hprefix tailTrace_255012
  have hstable : (prefixWord ++ tailWord_255012).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_255012).length < 2 ^ (prefixWord ++ tailWord_255012).sum := by decide
  have hdescent : baseEnd_255012 < baseStart_255012 := by decide
  rcases family_descends (prefixWord ++ tailWord_255012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_255015 : List Nat := [1, 1, 7, 1, 1, 1, 4, 2, 3]
def baseStart_255015 : Nat := 118140960795 + 255015 * 2 ^ 59
def prefixEnd_255015 : Nat := 4983230072969 + 3 ^ 40 * 255015 * 2
def baseEnd_255015 : Nat := 58197897380633327262095

theorem tailTrace_255015 : CollatzResearch.WordTrace tailWord_255015 prefixEnd_255015 58197897380633327262095 := by
  unfold tailWord_255015
  simp only [CollatzResearch.WordTrace]
  refine ⟨9301161171131682939670499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6200774114087788626446999 9301161171131682939670499)
  ·
    refine ⟨13951741756697524409505749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9301161171131682939670499 13951741756697524409505749)
    ·
      refine ⟨326993947422598228347791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 13951741756697524409505749 326993947422598228347791)
      ·
        refine ⟨490490921133897342521687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 326993947422598228347791 490490921133897342521687)
        ·
          refine ⟨735736381700846013782531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 490490921133897342521687 735736381700846013782531)
          ·
            refine ⟨1103604572551269020673797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 735736381700846013782531 1103604572551269020673797)
            ·
              refine ⟨206925857353362941376337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1103604572551269020673797 206925857353362941376337)
              ·
                refine ⟨155194393015022206032253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 206925857353362941376337 155194393015022206032253)
                ·
                  refine ⟨58197897380633327262095, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 155194393015022206032253 58197897380633327262095)
                  ·
                    rfl

theorem cell21_255015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 4, 2, 3].length) (baseStart_255015 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_255015 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_255015 prefixEnd_255015 := by exact prefixLift 255015
  have htrace : WordTrace (prefixWord ++ tailWord_255015) baseStart_255015 baseEnd_255015 := by
    simpa [prefixWord, tailWord_255015, baseEnd_255015] using wordTrace_append hprefix tailTrace_255015
  have hstable : (prefixWord ++ tailWord_255015).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_255015).length < 2 ^ (prefixWord ++ tailWord_255015).sum := by decide
  have hdescent : baseEnd_255015 < baseStart_255015 := by decide
  rcases family_descends (prefixWord ++ tailWord_255015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_255054 : List Nat := [4, 1, 1, 1, 1, 3, 2, 2, 6]
def baseStart_255054 : Nat := 118140960795 + 255054 * 2 ^ 59
def prefixEnd_255054 : Nat := 4983230072969 + 3 ^ 40 * 255054 * 2
def baseEnd_255054 : Nat := 58206797711977926112015

theorem tailTrace_255054 : CollatzResearch.WordTrace tailWord_255054 prefixEnd_255054 58206797711977926112015 := by
  unfold tailWord_255054
  simp only [CollatzResearch.WordTrace]
  refine ⟨1162822952248799075042527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 6201722411993595066893477 1162822952248799075042527)
  ·
    refine ⟨1744234428373198612563791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1162822952248799075042527 1744234428373198612563791)
    ·
      refine ⟨2616351642559797918845687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1744234428373198612563791 2616351642559797918845687)
      ·
        refine ⟨3924527463839696878268531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2616351642559797918845687 3924527463839696878268531)
        ·
          refine ⟨5886791195759545317402797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3924527463839696878268531 5886791195759545317402797)
          ·
            refine ⟨2207546698409829494026049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5886791195759545317402797 2207546698409829494026049)
            ·
              refine ⟨1655660023807372120519537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2207546698409829494026049 1655660023807372120519537)
              ·
                refine ⟨1241745017855529090389653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1655660023807372120519537 1241745017855529090389653)
                ·
                  refine ⟨58206797711977926112015, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1241745017855529090389653 58206797711977926112015)
                  ·
                    rfl

theorem cell21_255054_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 2, 2, 6].length) (baseStart_255054 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_255054 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_255054 prefixEnd_255054 := by exact prefixLift 255054
  have htrace : WordTrace (prefixWord ++ tailWord_255054) baseStart_255054 baseEnd_255054 := by
    simpa [prefixWord, tailWord_255054, baseEnd_255054] using wordTrace_append hprefix tailTrace_255054
  have hstable : (prefixWord ++ tailWord_255054).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_255054).length < 2 ^ (prefixWord ++ tailWord_255054).sum := by decide
  have hdescent : baseEnd_255054 < baseStart_255054 := by decide
  rcases family_descends (prefixWord ++ tailWord_255054) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_255074 : List Nat := [3, 3, 2, 2, 1, 1, 2, 4, 3]
def baseStart_255074 : Nat := 118140960795 + 255074 * 2 ^ 59
def prefixEnd_255074 : Nat := 4983230072969 + 3 ^ 40 * 255074 * 2
def baseEnd_255074 : Nat := 58211361984462335778641

theorem tailTrace_255074 : CollatzResearch.WordTrace tailWord_255074 prefixEnd_255074 58211361984462335778641 := by
  unfold tailWord_255074
  simp only [CollatzResearch.WordTrace]
  refine ⟨2325828269479484004017069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6202208718611957344045517 2325828269479484004017069)
  ·
    refine ⟨872185601054806501506401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2325828269479484004017069 872185601054806501506401)
    ·
      refine ⟨654139200791104876129801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 872185601054806501506401 654139200791104876129801)
      ·
        refine ⟨490604400593328657097351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 654139200791104876129801 490604400593328657097351)
        ·
          refine ⟨735906600889992985646027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 490604400593328657097351 735906600889992985646027)
          ·
            refine ⟨1103859901334989478469041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 735906600889992985646027 1103859901334989478469041)
            ·
              refine ⟨827894926001242108851781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1103859901334989478469041 827894926001242108851781)
              ·
                refine ⟨155230298625232895409709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 827894926001242108851781 155230298625232895409709)
                ·
                  refine ⟨58211361984462335778641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 155230298625232895409709 58211361984462335778641)
                  ·
                    rfl

theorem cell21_255074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 2, 4, 3].length) (baseStart_255074 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_255074 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_255074 prefixEnd_255074 := by exact prefixLift 255074
  have htrace : WordTrace (prefixWord ++ tailWord_255074) baseStart_255074 baseEnd_255074 := by
    simpa [prefixWord, tailWord_255074, baseEnd_255074] using wordTrace_append hprefix tailTrace_255074
  have hstable : (prefixWord ++ tailWord_255074).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_255074).length < 2 ^ (prefixWord ++ tailWord_255074).sum := by decide
  have hdescent : baseEnd_255074 < baseStart_255074 := by decide
  rcases family_descends (prefixWord ++ tailWord_255074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_255240 : List Nat := [2, 1, 3, 2, 4, 2, 1, 2, 4]
def baseStart_255240 : Nat := 118140960795 + 255240 * 2 ^ 59
def prefixEnd_255240 : Nat := 4983230072969 + 3 ^ 40 * 255240 * 2
def baseEnd_255240 : Nat := 58249245446082936011635

theorem tailTrace_255240 : CollatzResearch.WordTrace tailWord_255240 prefixEnd_255240 58249245446082936011635 := by
  unfold tailWord_255240
  simp only [CollatzResearch.WordTrace]
  refine ⟨4654683797658273183305587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6206245063544364244407449 4654683797658273183305587)
  ·
    refine ⟨6982025696487409774958381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4654683797658273183305587 6982025696487409774958381)
    ·
      refine ⟨2618259636182778665609393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6982025696487409774958381 2618259636182778665609393)
      ·
        refine ⟨1963694727137083999207045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2618259636182778665609393 1963694727137083999207045)
        ·
          refine ⟨368192761338203249851321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1963694727137083999207045 368192761338203249851321)
          ·
            refine ⟨276144571003652437388491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 368192761338203249851321 276144571003652437388491)
            ·
              refine ⟨414216856505478656082737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 276144571003652437388491 414216856505478656082737)
              ·
                refine ⟨310662642379108992062053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 414216856505478656082737 310662642379108992062053)
                ·
                  refine ⟨58249245446082936011635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 310662642379108992062053 58249245446082936011635)
                  ·
                    rfl

theorem cell21_255240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 4, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 4, 2, 1, 2, 4].length) (baseStart_255240 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_255240 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_255240 prefixEnd_255240 := by exact prefixLift 255240
  have htrace : WordTrace (prefixWord ++ tailWord_255240) baseStart_255240 baseEnd_255240 := by
    simpa [prefixWord, tailWord_255240, baseEnd_255240] using wordTrace_append hprefix tailTrace_255240
  have hstable : (prefixWord ++ tailWord_255240).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_255240).length < 2 ^ (prefixWord ++ tailWord_255240).sum := by decide
  have hdescent : baseEnd_255240 < baseStart_255240 := by decide
  rcases family_descends (prefixWord ++ tailWord_255240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_255282 : List Nat := [3, 2, 1, 1, 4, 1, 1, 2, 6]
def baseStart_255282 : Nat := 118140960795 + 255282 * 2 ^ 59
def prefixEnd_255282 : Nat := 4983230072969 + 3 ^ 40 * 255282 * 2
def baseEnd_255282 : Nat := 58258830418300196311549

theorem tailTrace_255282 : CollatzResearch.WordTrace tailWord_255282 prefixEnd_255282 58258830418300196311549 := by
  unfold tailWord_255282
  simp only [CollatzResearch.WordTrace]
  refine ⟨2327724865291096884910025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6207266307442925026426733 2327724865291096884910025)
  ·
    refine ⟨1745793648968322663682519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2327724865291096884910025 1745793648968322663682519)
    ·
      refine ⟨2618690473452483995523779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1745793648968322663682519 2618690473452483995523779)
      ·
        refine ⟨3928035710178725993285669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2618690473452483995523779 3928035710178725993285669)
        ·
          refine ⟨736506695658511123741063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3928035710178725993285669 736506695658511123741063)
          ·
            refine ⟨1104760043487766685611595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 736506695658511123741063 1104760043487766685611595)
            ·
              refine ⟨1657140065231650028417393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1104760043487766685611595 1657140065231650028417393)
              ·
                refine ⟨1242855048923737521313045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1657140065231650028417393 1242855048923737521313045)
                ·
                  refine ⟨58258830418300196311549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1242855048923737521313045 58258830418300196311549)
                  ·
                    rfl

theorem cell21_255282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 1, 2, 6].length) (baseStart_255282 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_255282 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_255282 prefixEnd_255282 := by exact prefixLift 255282
  have htrace : WordTrace (prefixWord ++ tailWord_255282) baseStart_255282 baseEnd_255282 := by
    simpa [prefixWord, tailWord_255282, baseEnd_255282] using wordTrace_append hprefix tailTrace_255282
  have hstable : (prefixWord ++ tailWord_255282).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_255282).length < 2 ^ (prefixWord ++ tailWord_255282).sum := by decide
  have hdescent : baseEnd_255282 < baseStart_255282 := by decide
  rcases family_descends (prefixWord ++ tailWord_255282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_255285 : List Nat := [1, 3, 3, 1, 2, 2, 3, 3, 3]
def baseStart_255285 : Nat := 118140960795 + 255285 * 2 ^ 59
def prefixEnd_255285 : Nat := 4983230072969 + 3 ^ 40 * 255285 * 2
def baseEnd_255285 : Nat := 58259515059172857761543

theorem tailTrace_255285 : CollatzResearch.WordTrace tailWord_255285 prefixEnd_255285 58259515059172857761543 := by
  unfold tailWord_255285
  simp only [CollatzResearch.WordTrace]
  refine ⟨9311008880153519051999309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6207339253435679367999539 9311008880153519051999309)
  ·
    refine ⟨3491628330057569644499741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9311008880153519051999309 3491628330057569644499741)
    ·
      refine ⟨1309360623771588616687403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3491628330057569644499741 1309360623771588616687403)
      ·
        refine ⟨1964040935657382925031105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1309360623771588616687403 1964040935657382925031105)
        ·
          refine ⟨1473030701743037193773329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1964040935657382925031105 1473030701743037193773329)
          ·
            refine ⟨1104773026307277895329997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1473030701743037193773329 1104773026307277895329997)
            ·
              refine ⟨414289884865229210748749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1104773026307277895329997 414289884865229210748749)
              ·
                refine ⟨155358706824460954030781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 414289884865229210748749 155358706824460954030781)
                ·
                  refine ⟨58259515059172857761543, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 155358706824460954030781 58259515059172857761543)
                  ·
                    rfl

theorem cell21_255285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 3, 3, 3].length) (baseStart_255285 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_255285 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_255285 prefixEnd_255285 := by exact prefixLift 255285
  have htrace : WordTrace (prefixWord ++ tailWord_255285) baseStart_255285 baseEnd_255285 := by
    simpa [prefixWord, tailWord_255285, baseEnd_255285] using wordTrace_append hprefix tailTrace_255285
  have hstable : (prefixWord ++ tailWord_255285).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_255285).length < 2 ^ (prefixWord ++ tailWord_255285).sum := by decide
  have hdescent : baseEnd_255285 < baseStart_255285 := by decide
  rcases family_descends (prefixWord ++ tailWord_255285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_255344 : List Nat := [2, 1, 1, 1, 4, 2, 2, 5, 3]
def baseStart_255344 : Nat := 118140960795 + 255344 * 2 ^ 59
def prefixEnd_255344 : Nat := 4983230072969 + 3 ^ 40 * 255344 * 2
def baseEnd_255344 : Nat := 58272979663001866278089

theorem tailTrace_255344 : CollatzResearch.WordTrace tailWord_255344 prefixEnd_255344 58272979663001866278089 := by
  unfold tailWord_255344
  simp only [CollatzResearch.WordTrace]
  refine ⟨4656580393469886064198543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6208773857959848085598057 4656580393469886064198543)
  ·
    refine ⟨6984870590204829096297815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4656580393469886064198543 6984870590204829096297815)
    ·
      refine ⟨10477305885307243644446723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6984870590204829096297815 10477305885307243644446723)
      ·
        refine ⟨15715958827960865466670085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10477305885307243644446723 15715958827960865466670085)
        ·
          refine ⟨2946742280242662275000641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15715958827960865466670085 2946742280242662275000641)
          ·
            refine ⟨2210056710181996706250481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2946742280242662275000641 2210056710181996706250481)
            ·
              refine ⟨1657542532636497529687861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2210056710181996706250481 1657542532636497529687861)
              ·
                refine ⟨155394612434671643408237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1657542532636497529687861 155394612434671643408237)
                ·
                  refine ⟨58272979663001866278089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 155394612434671643408237 58272979663001866278089)
                  ·
                    rfl

theorem cell21_255344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 2, 5, 3].length) (baseStart_255344 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_255344 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_255344 prefixEnd_255344 := by exact prefixLift 255344
  have htrace : WordTrace (prefixWord ++ tailWord_255344) baseStart_255344 baseEnd_255344 := by
    simpa [prefixWord, tailWord_255344, baseEnd_255344] using wordTrace_append hprefix tailTrace_255344
  have hstable : (prefixWord ++ tailWord_255344).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_255344).length < 2 ^ (prefixWord ++ tailWord_255344).sum := by decide
  have hdescent : baseEnd_255344 < baseStart_255344 := by decide
  rcases family_descends (prefixWord ++ tailWord_255344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_255541 : List Nat := [1, 3, 3, 1, 1, 5, 1, 6]
def baseStart_255541 : Nat := 118140960795 + 255541 * 2 ^ 59
def prefixEnd_255541 : Nat := 4983230072969 + 3 ^ 40 * 255541 * 2
def baseEnd_255541 : Nat := 19439312582324433831451

theorem tailTrace_255541 : CollatzResearch.WordTrace tailWord_255541 prefixEnd_255541 19439312582324433831451 := by
  unfold tailWord_255541
  simp only [CollatzResearch.WordTrace]
  refine ⟨9320345967226074773318477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6213563978150716515545651 9320345967226074773318477)
  ·
    refine ⟨3495129737709778039994429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9320345967226074773318477 3495129737709778039994429)
    ·
      refine ⟨1310673651641166764997911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3495129737709778039994429 1310673651641166764997911)
      ·
        refine ⟨1966010477461750147496867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1310673651641166764997911 1966010477461750147496867)
        ·
          refine ⟨2949015716192625221245301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1966010477461750147496867 2949015716192625221245301)
          ·
            refine ⟨276470223393058614491747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 2949015716192625221245301 276470223393058614491747)
            ·
              refine ⟨414705335089587921737621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 276470223393058614491747 414705335089587921737621)
              ·
                refine ⟨19439312582324433831451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 414705335089587921737621 19439312582324433831451)
                ·
                  rfl

theorem cell21_255541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 5, 1, 6].length) (baseStart_255541 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_255541 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_255541 prefixEnd_255541 := by exact prefixLift 255541
  have htrace : WordTrace (prefixWord ++ tailWord_255541) baseStart_255541 baseEnd_255541 := by
    simpa [prefixWord, tailWord_255541, baseEnd_255541] using wordTrace_append hprefix tailTrace_255541
  have hstable : (prefixWord ++ tailWord_255541).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_255541).length < 2 ^ (prefixWord ++ tailWord_255541).sum := by decide
  have hdescent : baseEnd_255541 < baseStart_255541 := by decide
  rcases family_descends (prefixWord ++ tailWord_255541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_255569 : List Nat := [1, 2, 2, 1, 3, 2, 2, 2, 6]
def baseStart_255569 : Nat := 118140960795 + 255569 * 2 ^ 59
def prefixEnd_255569 : Nat := 4983230072969 + 3 ^ 40 * 255569 * 2
def baseEnd_255569 : Nat := 58324327728451475027629

theorem tailTrace_255569 : CollatzResearch.WordTrace tailWord_255569 prefixEnd_255569 58324327728451475027629 := by
  unfold tailWord_255569
  simp only [CollatzResearch.WordTrace]
  refine ⟨9321367211124635555337761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6214244807416423703558507 9321367211124635555337761)
  ·
    refine ⟨6991025408343476666503321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9321367211124635555337761 6991025408343476666503321)
    ·
      refine ⟨5243269056257607499877491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6991025408343476666503321 5243269056257607499877491)
      ·
        refine ⟨7864903584386411249816237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5243269056257607499877491 7864903584386411249816237)
        ·
          refine ⟨2949338844144904218681089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7864903584386411249816237 2949338844144904218681089)
          ·
            refine ⟨2212004133108678164010817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2949338844144904218681089 2212004133108678164010817)
            ·
              refine ⟨1659003099831508623008113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2212004133108678164010817 1659003099831508623008113)
              ·
                refine ⟨1244252324873631467256085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1659003099831508623008113 1244252324873631467256085)
                ·
                  refine ⟨58324327728451475027629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1244252324873631467256085 58324327728451475027629)
                  ·
                    rfl

theorem cell21_255569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 2, 2, 6].length) (baseStart_255569 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_255569 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_255569 prefixEnd_255569 := by exact prefixLift 255569
  have htrace : WordTrace (prefixWord ++ tailWord_255569) baseStart_255569 baseEnd_255569 := by
    simpa [prefixWord, tailWord_255569, baseEnd_255569] using wordTrace_append hprefix tailTrace_255569
  have hstable : (prefixWord ++ tailWord_255569).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_255569).length < 2 ^ (prefixWord ++ tailWord_255569).sum := by decide
  have hdescent : baseEnd_255569 < baseStart_255569 := by decide
  rcases family_descends (prefixWord ++ tailWord_255569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_255617 : List Nat := [1, 2, 4, 2, 1, 2, 4, 5]
def baseStart_255617 : Nat := 118140960795 + 255617 * 2 ^ 59
def prefixEnd_255617 : Nat := 4983230072969 + 3 ^ 40 * 255617 * 2
def baseEnd_255617 : Nat := 19445093994138019409177

theorem tailTrace_255617 : CollatzResearch.WordTrace tailWord_255617 prefixEnd_255617 19445093994138019409177 := by
  unfold tailWord_255617
  simp only [CollatzResearch.WordTrace]
  refine ⟨9323117914950739753085105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6215411943300493168723403 9323117914950739753085105)
  ·
    refine ⟨6992338436213054814813829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9323117914950739753085105 6992338436213054814813829)
    ·
      refine ⟨1311063456789947777777593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6992338436213054814813829 1311063456789947777777593)
      ·
        refine ⟨983297592592460833333195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1311063456789947777777593 983297592592460833333195)
        ·
          refine ⟨1474946388888691249999793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 983297592592460833333195 1474946388888691249999793)
          ·
            refine ⟨1106209791666518437499845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1474946388888691249999793 1106209791666518437499845)
            ·
              refine ⟨207414335937472207031221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1106209791666518437499845 207414335937472207031221)
              ·
                refine ⟨19445093994138019409177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 207414335937472207031221 19445093994138019409177)
                ·
                  rfl

theorem cell21_255617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 4, 5].length) (baseStart_255617 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_255617 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_255617 prefixEnd_255617 := by exact prefixLift 255617
  have htrace : WordTrace (prefixWord ++ tailWord_255617) baseStart_255617 baseEnd_255617 := by
    simpa [prefixWord, tailWord_255617, baseEnd_255617] using wordTrace_append hprefix tailTrace_255617
  have hstable : (prefixWord ++ tailWord_255617).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_255617).length < 2 ^ (prefixWord ++ tailWord_255617).sum := by decide
  have hdescent : baseEnd_255617 < baseStart_255617 := by decide
  rcases family_descends (prefixWord ++ tailWord_255617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_255634 : List Nat := [3, 2, 3, 1, 4, 1, 7]
def baseStart_255634 : Nat := 118140960795 + 255634 * 2 ^ 59
def prefixEnd_255634 : Nat := 4983230072969 + 3 ^ 40 * 255634 * 2
def baseEnd_255634 : Nat := 6482129068225089604907

theorem tailTrace_255634 : CollatzResearch.WordTrace tailWord_255634 prefixEnd_255634 6482129068225089604907 := by
  unfold tailWord_255634
  simp only [CollatzResearch.WordTrace]
  refine ⟨2330934488972287914113489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6215825303926101104302637 2330934488972287914113489)
  ·
    refine ⟨1748200866729215935585117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2330934488972287914113489 1748200866729215935585117)
    ·
      refine ⟨655575325023455975844419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1748200866729215935585117 655575325023455975844419)
      ·
        refine ⟨983362987535183963766629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 655575325023455975844419 983362987535183963766629)
        ·
          refine ⟨184380560162846993206243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 983362987535183963766629 184380560162846993206243)
          ·
            refine ⟨276570840244270489809365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 184380560162846993206243 276570840244270489809365)
            ·
              refine ⟨6482129068225089604907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 276570840244270489809365 6482129068225089604907)
              ·
                rfl

theorem cell21_255634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 4, 1, 7].length) (baseStart_255634 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_255634 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_255634 prefixEnd_255634 := by exact prefixLift 255634
  have htrace : WordTrace (prefixWord ++ tailWord_255634) baseStart_255634 baseEnd_255634 := by
    simpa [prefixWord, tailWord_255634, baseEnd_255634] using wordTrace_append hprefix tailTrace_255634
  have hstable : (prefixWord ++ tailWord_255634).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_255634).length < 2 ^ (prefixWord ++ tailWord_255634).sum := by decide
  have hdescent : baseEnd_255634 < baseStart_255634 := by decide
  rcases family_descends (prefixWord ++ tailWord_255634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_255648 : List Nat := [2, 1, 1, 4, 3, 3, 1, 1, 5]
def baseStart_255648 : Nat := 118140960795 + 255648 * 2 ^ 59
def prefixEnd_255648 : Nat := 4983230072969 + 3 ^ 40 * 255648 * 2
def baseEnd_255648 : Nat := 58342356604764893210801

theorem tailTrace_255648 : CollatzResearch.WordTrace tailWord_255648 prefixEnd_255648 58342356604764893210801 := by
  unfold tailWord_255648
  simp only [CollatzResearch.WordTrace]
  refine ⟨4662124288919216023731799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6216165718558954698309065 4662124288919216023731799)
  ·
    refine ⟨6993186433378824035597699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4662124288919216023731799 6993186433378824035597699)
    ·
      refine ⟨10489779650068236053396549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6993186433378824035597699 10489779650068236053396549)
      ·
        refine ⟨1966833684387794260011853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10489779650068236053396549 1966833684387794260011853)
        ·
          refine ⟨737562631645422847504445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1966833684387794260011853 737562631645422847504445)
          ·
            refine ⟨276585986867033567814167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 737562631645422847504445 276585986867033567814167)
            ·
              refine ⟨414878980300550351721251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 276585986867033567814167 414878980300550351721251)
              ·
                refine ⟨622318470450825527581877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 414878980300550351721251 622318470450825527581877)
                ·
                  refine ⟨58342356604764893210801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 622318470450825527581877 58342356604764893210801)
                  ·
                    rfl

theorem cell21_255648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 3, 1, 1, 5].length) (baseStart_255648 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_255648 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_255648 prefixEnd_255648 := by exact prefixLift 255648
  have htrace : WordTrace (prefixWord ++ tailWord_255648) baseStart_255648 baseEnd_255648 := by
    simpa [prefixWord, tailWord_255648, baseEnd_255648] using wordTrace_append hprefix tailTrace_255648
  have hstable : (prefixWord ++ tailWord_255648).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_255648).length < 2 ^ (prefixWord ++ tailWord_255648).sum := by decide
  have hdescent : baseEnd_255648 < baseStart_255648 := by decide
  rcases family_descends (prefixWord ++ tailWord_255648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_255676 : List Nat := [2, 2, 2, 3, 1, 2, 2, 7]
def baseStart_255676 : Nat := 118140960795 + 255676 * 2 ^ 59
def prefixEnd_255676 : Nat := 4983230072969 + 3 ^ 40 * 255676 * 2
def baseEnd_255676 : Nat := 19449582195414355581359

theorem tailTrace_255676 : CollatzResearch.WordTrace tailWord_255676 prefixEnd_255676 19449582195414355581359 := by
  unfold tailWord_255676
  simp only [CollatzResearch.WordTrace]
  refine ⟨4662634910868496414741441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6216846547824661886321921 4662634910868496414741441)
  ·
    refine ⟨3496976183151372311056081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4662634910868496414741441 3496976183151372311056081)
    ·
      refine ⟨2622732137363529233292061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3496976183151372311056081 2622732137363529233292061)
      ·
        refine ⟨983524551511323462484523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2622732137363529233292061 983524551511323462484523)
        ·
          refine ⟨1475286827266985193726785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 983524551511323462484523 1475286827266985193726785)
          ·
            refine ⟨1106465120450238895295089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1475286827266985193726785 1106465120450238895295089)
            ·
              refine ⟨829848840337679171471317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1106465120450238895295089 829848840337679171471317)
              ·
                refine ⟨19449582195414355581359, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 829848840337679171471317 19449582195414355581359)
                ·
                  rfl

theorem cell21_255676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 2, 7].length) (baseStart_255676 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_255676 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_255676 prefixEnd_255676 := by exact prefixLift 255676
  have htrace : WordTrace (prefixWord ++ tailWord_255676) baseStart_255676 baseEnd_255676 := by
    simpa [prefixWord, tailWord_255676, baseEnd_255676] using wordTrace_append hprefix tailTrace_255676
  have hstable : (prefixWord ++ tailWord_255676).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_255676).length < 2 ^ (prefixWord ++ tailWord_255676).sum := by decide
  have hdescent : baseEnd_255676 < baseStart_255676 := by decide
  rcases family_descends (prefixWord ++ tailWord_255676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_255693 : List Nat := [1, 6, 2, 1, 1, 10]
def baseStart_255693 : Nat := 118140960795 + 255693 * 2 ^ 59
def prefixEnd_255693 : Nat := 4983230072969 + 3 ^ 40 * 255693 * 2
def baseEnd_255693 : Nat := 2161208378439067220767

theorem tailTrace_255693 : CollatzResearch.WordTrace tailWord_255693 prefixEnd_255693 2161208378439067220767 := by
  unfold tailWord_255693
  simp only [CollatzResearch.WordTrace]
  refine ⟨9325889862675404732851733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6217259908450269821901155 9325889862675404732851733)
  ·
    refine ⟨437151087312909596852425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 9325889862675404732851733 437151087312909596852425)
    ·
      refine ⟨327863315484682197639319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 437151087312909596852425 327863315484682197639319)
      ·
        refine ⟨491794973227023296458979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 327863315484682197639319 491794973227023296458979)
        ·
          refine ⟨737692459840534944688469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 491794973227023296458979 737692459840534944688469)
          ·
            refine ⟨2161208378439067220767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 737692459840534944688469 2161208378439067220767)
            ·
              rfl

theorem cell21_255693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 10].length) (baseStart_255693 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_255693 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_255693 prefixEnd_255693 := by exact prefixLift 255693
  have htrace : WordTrace (prefixWord ++ tailWord_255693) baseStart_255693 baseEnd_255693 := by
    simpa [prefixWord, tailWord_255693, baseEnd_255693] using wordTrace_append hprefix tailTrace_255693
  have hstable : (prefixWord ++ tailWord_255693).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_255693).length < 2 ^ (prefixWord ++ tailWord_255693).sum := by decide
  have hdescent : baseEnd_255693 < baseStart_255693 := by decide
  rcases family_descends (prefixWord ++ tailWord_255693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_255735 : List Nat := [1, 1, 3, 1, 1, 1, 4, 9]
def baseStart_255735 : Nat := 118140960795 + 255735 * 2 ^ 59
def prefixEnd_255735 : Nat := 4983230072969 + 3 ^ 40 * 255735 * 2
def baseEnd_255735 : Nat := 19454070396690691753541

theorem tailTrace_255735 : CollatzResearch.WordTrace tailWord_255735 prefixEnd_255735 19454070396690691753541 := by
  unfold tailWord_255735
  simp only [CollatzResearch.WordTrace]
  refine ⟨9327421728523245905880659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6218281152348830603920439 9327421728523245905880659)
  ·
    refine ⟨13991132592784868858820989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9327421728523245905880659 13991132592784868858820989)
    ·
      refine ⟨5246674722294325822057871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13991132592784868858820989 5246674722294325822057871)
      ·
        refine ⟨7870012083441488733086807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5246674722294325822057871 7870012083441488733086807)
        ·
          refine ⟨11805018125162233099630211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7870012083441488733086807 11805018125162233099630211)
          ·
            refine ⟨17707527187743349649445317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11805018125162233099630211 17707527187743349649445317)
            ·
              refine ⟨3320161347701878059270997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17707527187743349649445317 3320161347701878059270997)
              ·
                refine ⟨19454070396690691753541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 3320161347701878059270997 19454070396690691753541)
                ·
                  rfl

theorem cell21_255735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 4, 9].length) (baseStart_255735 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_255735 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_255735 prefixEnd_255735 := by exact prefixLift 255735
  have htrace : WordTrace (prefixWord ++ tailWord_255735) baseStart_255735 baseEnd_255735 := by
    simpa [prefixWord, tailWord_255735, baseEnd_255735] using wordTrace_append hprefix tailTrace_255735
  have hstable : (prefixWord ++ tailWord_255735).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_255735).length < 2 ^ (prefixWord ++ tailWord_255735).sum := by decide
  have hdescent : baseEnd_255735 < baseStart_255735 := by decide
  rcases family_descends (prefixWord ++ tailWord_255735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_255800 : List Nat := [2, 1, 2, 1, 3, 3, 3, 3, 3]
def baseStart_255800 : Nat := 118140960795 + 255800 * 2 ^ 59
def prefixEnd_255800 : Nat := 4983230072969 + 3 ^ 40 * 255800 * 2
def baseEnd_255800 : Nat := 58377045075646406677157

theorem tailTrace_255800 : CollatzResearch.WordTrace tailWord_255800 prefixEnd_255800 58377045075646406677157 := by
  unfold tailWord_255800
  simp only [CollatzResearch.WordTrace]
  refine ⟨4664896236643881003498427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6219861648858508004664569 4664896236643881003498427)
  ·
    refine ⟨6997344354965821505247641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4664896236643881003498427 6997344354965821505247641)
    ·
      refine ⟨5248008266224366128935731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6997344354965821505247641 5248008266224366128935731)
      ·
        refine ⟨7872012399336549193403597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5248008266224366128935731 7872012399336549193403597)
        ·
          refine ⟨2952004649751205947526349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7872012399336549193403597 2952004649751205947526349)
          ·
            refine ⟨1107001743656702230322381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2952004649751205947526349 1107001743656702230322381)
            ·
              refine ⟨415125653871263336370893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1107001743656702230322381 415125653871263336370893)
              ·
                refine ⟨155672120201723751139085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 415125653871263336370893 155672120201723751139085)
                ·
                  refine ⟨58377045075646406677157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 155672120201723751139085 58377045075646406677157)
                  ·
                    rfl

theorem cell21_255800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 3, 3, 3].length) (baseStart_255800 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_255800 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_255800 prefixEnd_255800 := by exact prefixLift 255800
  have htrace : WordTrace (prefixWord ++ tailWord_255800) baseStart_255800 baseEnd_255800 := by
    simpa [prefixWord, tailWord_255800, baseEnd_255800] using wordTrace_append hprefix tailTrace_255800
  have hstable : (prefixWord ++ tailWord_255800).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_255800).length < 2 ^ (prefixWord ++ tailWord_255800).sum := by decide
  have hdescent : baseEnd_255800 < baseStart_255800 := by decide
  rcases family_descends (prefixWord ++ tailWord_255800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_255811 : List Nat := [1, 1, 1, 3, 1, 5, 9]
def baseStart_255811 : Nat := 118140960795 + 255811 * 2 ^ 59
def prefixEnd_255811 : Nat := 4983230072969 + 3 ^ 40 * 255811 * 2
def baseEnd_255811 : Nat := 6486617269501425777089

theorem tailTrace_255811 : CollatzResearch.WordTrace tailWord_255811 prefixEnd_255811 6486617269501425777089 := by
  unfold tailWord_255811
  simp only [CollatzResearch.WordTrace]
  refine ⟨9330193676247910885647287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6220129117498607257098191 9330193676247910885647287)
  ·
    refine ⟨13995290514371866328470931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9330193676247910885647287 13995290514371866328470931)
    ·
      refine ⟨20992935771557799492706397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13995290514371866328470931 20992935771557799492706397)
      ·
        refine ⟨7872350914334174809764899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20992935771557799492706397 7872350914334174809764899)
        ·
          refine ⟨11808526371501262214647349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7872350914334174809764899 11808526371501262214647349)
          ·
            refine ⟨1107049347328243332623189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 11808526371501262214647349 1107049347328243332623189)
            ·
              refine ⟨6486617269501425777089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 1107049347328243332623189 6486617269501425777089)
              ·
                rfl

theorem cell21_255811_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 9].length) (baseStart_255811 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_255811 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_255811 prefixEnd_255811 := by exact prefixLift 255811
  have htrace : WordTrace (prefixWord ++ tailWord_255811) baseStart_255811 baseEnd_255811 := by
    simpa [prefixWord, tailWord_255811, baseEnd_255811] using wordTrace_append hprefix tailTrace_255811
  have hstable : (prefixWord ++ tailWord_255811).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_255811).length < 2 ^ (prefixWord ++ tailWord_255811).sum := by decide
  have hdescent : baseEnd_255811 < baseStart_255811 := by decide
  rcases family_descends (prefixWord ++ tailWord_255811) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_255828 : List Nat := [2, 4, 1, 1, 3, 1, 1, 8]
def baseStart_255828 : Nat := 118140960795 + 255828 * 2 ^ 59
def prefixEnd_255828 : Nat := 4983230072969 + 3 ^ 40 * 255828 * 2
def baseEnd_255828 : Nat := 19461145019041526736811

theorem tailTrace_255828 : CollatzResearch.WordTrace tailWord_255828 prefixEnd_255828 19461145019041526736811 := by
  unfold tailWord_255828
  simp only [CollatzResearch.WordTrace]
  refine ⟨4665406858593161394508069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6220542478124215192677425 4665406858593161394508069)
  ·
    refine ⟨874763785986217761470263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4665406858593161394508069 874763785986217761470263)
    ·
      refine ⟨1312145678979326642205395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 874763785986217761470263 1312145678979326642205395)
      ·
        refine ⟨1968218518468989963308093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1312145678979326642205395 1968218518468989963308093)
        ·
          refine ⟨738081944425871236240535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1968218518468989963308093 738081944425871236240535)
          ·
            refine ⟨1107122916638806854360803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 738081944425871236240535 1107122916638806854360803)
            ·
              refine ⟨1660684374958210281541205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1107122916638806854360803 1660684374958210281541205)
              ·
                refine ⟨19461145019041526736811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1660684374958210281541205 19461145019041526736811)
                ·
                  rfl

theorem cell21_255828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 1, 8].length) (baseStart_255828 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_255828 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_255828 prefixEnd_255828 := by exact prefixLift 255828
  have htrace : WordTrace (prefixWord ++ tailWord_255828) baseStart_255828 baseEnd_255828 := by
    simpa [prefixWord, tailWord_255828, baseEnd_255828] using wordTrace_append hprefix tailTrace_255828
  have hstable : (prefixWord ++ tailWord_255828).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_255828).length < 2 ^ (prefixWord ++ tailWord_255828).sum := by decide
  have hdescent : baseEnd_255828 < baseStart_255828 := by decide
  rcases family_descends (prefixWord ++ tailWord_255828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_255859 : List Nat := [1, 1, 1, 2, 2, 1, 3, 7, 3]
def baseStart_255859 : Nat := 118140960795 + 255859 * 2 ^ 59
def prefixEnd_255859 : Nat := 4983230072969 + 3 ^ 40 * 255859 * 2
def baseEnd_255859 : Nat := 58390509679475415193703

theorem tailTrace_255859 : CollatzResearch.WordTrace tailWord_255859 prefixEnd_255859 58390509679475415193703 := by
  unfold tailWord_255859
  simp only [CollatzResearch.WordTrace]
  refine ⟨9331944380074015083394631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6221296253382676722263087 9331944380074015083394631)
  ·
    refine ⟨13997916570111022625091947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9331944380074015083394631 13997916570111022625091947)
    ·
      refine ⟨20996874855166533937637921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13997916570111022625091947 20996874855166533937637921)
      ·
        refine ⟨15747656141374900453228441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20996874855166533937637921 15747656141374900453228441)
        ·
          refine ⟨11810742106031175339921331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15747656141374900453228441 11810742106031175339921331)
          ·
            refine ⟨17716113159046763009881997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11810742106031175339921331 17716113159046763009881997)
            ·
              refine ⟨6643542434642536128705749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17716113159046763009881997 6643542434642536128705749)
              ·
                refine ⟨155708025811934440516541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6643542434642536128705749 155708025811934440516541)
                ·
                  refine ⟨58390509679475415193703, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 155708025811934440516541 58390509679475415193703)
                  ·
                    rfl

theorem cell21_255859_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 3, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 3, 7, 3].length) (baseStart_255859 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_255859 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_255859 prefixEnd_255859 := by exact prefixLift 255859
  have htrace : WordTrace (prefixWord ++ tailWord_255859) baseStart_255859 baseEnd_255859 := by
    simpa [prefixWord, tailWord_255859, baseEnd_255859] using wordTrace_append hprefix tailTrace_255859
  have hstable : (prefixWord ++ tailWord_255859).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_255859).length < 2 ^ (prefixWord ++ tailWord_255859).sum := by decide
  have hdescent : baseEnd_255859 < baseStart_255859 := by decide
  rcases family_descends (prefixWord ++ tailWord_255859) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_255935 : List Nat := [1, 1, 2, 2, 2, 1, 3, 6, 3]
def baseStart_255935 : Nat := 118140960795 + 255935 * 2 ^ 59
def prefixEnd_255935 : Nat := 4983230072969 + 3 ^ 40 * 255935 * 2
def baseEnd_255935 : Nat := 58407853914916171926881

theorem tailTrace_255935 : CollatzResearch.WordTrace tailWord_255935 prefixEnd_255935 58407853914916171926881 := by
  unfold tailWord_255935
  simp only [CollatzResearch.WordTrace]
  refine ⟨9334716327798680063161259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6223144218532453375440839 9334716327798680063161259)
  ·
    refine ⟨14002074491698020094741889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9334716327798680063161259 14002074491698020094741889)
    ·
      refine ⟨10501555868773515071056417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14002074491698020094741889 10501555868773515071056417)
      ·
        refine ⟨7876166901580136303292313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10501555868773515071056417 7876166901580136303292313)
        ·
          refine ⟨5907125176185102227469235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7876166901580136303292313 5907125176185102227469235)
          ·
            refine ⟨8860687764277653341203853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5907125176185102227469235 8860687764277653341203853)
            ·
              refine ⟨3322757911604120002951445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8860687764277653341203853 3322757911604120002951445)
              ·
                refine ⟨155754277106443125138349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3322757911604120002951445 155754277106443125138349)
                ·
                  refine ⟨58407853914916171926881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 155754277106443125138349 58407853914916171926881)
                  ·
                    rfl

theorem cell21_255935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 3, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 3, 6, 3].length) (baseStart_255935 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_255935 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_255935 prefixEnd_255935 := by exact prefixLift 255935
  have htrace : WordTrace (prefixWord ++ tailWord_255935) baseStart_255935 baseEnd_255935 := by
    simpa [prefixWord, tailWord_255935, baseEnd_255935] using wordTrace_append hprefix tailTrace_255935
  have hstable : (prefixWord ++ tailWord_255935).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_255935).length < 2 ^ (prefixWord ++ tailWord_255935).sum := by decide
  have hdescent : baseEnd_255935 < baseStart_255935 := by decide
  rcases family_descends (prefixWord ++ tailWord_255935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_256042 : List Nat := [3, 1, 4, 1, 2, 1, 1, 4, 4]
def baseStart_256042 : Nat := 118140960795 + 256042 * 2 ^ 59
def prefixEnd_256042 : Nat := 4983230072969 + 3 ^ 40 * 256042 * 2
def baseEnd_256042 : Nat := 58432272772707763643329

theorem tailTrace_256042 : CollatzResearch.WordTrace tailWord_256042 prefixEnd_256042 58432272772707763643329 := by
  unfold tailWord_256042
  simp only [CollatzResearch.WordTrace]
  refine ⟨2334654734602759334326595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6225745958940691558204253 2334654734602759334326595)
  ·
    refine ⟨3501982101904139001489893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2334654734602759334326595 3501982101904139001489893)
    ·
      refine ⟨656621644107026062779355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3501982101904139001489893 656621644107026062779355)
      ·
        refine ⟨984932466160539094169033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 656621644107026062779355 984932466160539094169033)
        ·
          refine ⟨738699349620404320626775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 984932466160539094169033 738699349620404320626775)
          ·
            refine ⟨1108049024430606480940163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 738699349620404320626775 1108049024430606480940163)
            ·
              refine ⟨1662073536645909721410245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1108049024430606480940163 1662073536645909721410245)
              ·
                refine ⟨311638788121108072764421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1662073536645909721410245 311638788121108072764421)
                ·
                  refine ⟨58432272772707763643329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 311638788121108072764421 58432272772707763643329)
                  ·
                    rfl

theorem cell21_256042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 1, 4, 4].length) (baseStart_256042 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_256042 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_256042 prefixEnd_256042 := by exact prefixLift 256042
  have htrace : WordTrace (prefixWord ++ tailWord_256042) baseStart_256042 baseEnd_256042 := by
    simpa [prefixWord, tailWord_256042, baseEnd_256042] using wordTrace_append hprefix tailTrace_256042
  have hstable : (prefixWord ++ tailWord_256042).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_256042).length < 2 ^ (prefixWord ++ tailWord_256042).sum := by decide
  have hdescent : baseEnd_256042 < baseStart_256042 := by decide
  rcases family_descends (prefixWord ++ tailWord_256042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_256087 : List Nat := [1, 1, 3, 2, 2, 1, 3, 5, 3]
def baseStart_256087 : Nat := 118140960795 + 256087 * 2 ^ 59
def prefixEnd_256087 : Nat := 4983230072969 + 3 ^ 40 * 256087 * 2
def baseEnd_256087 : Nat := 58442542385797685393237

theorem tailTrace_256087 : CollatzResearch.WordTrace tailWord_256087 prefixEnd_256087 58442542385797685393237 := by
  unfold tailWord_256087
  simp only [CollatzResearch.WordTrace]
  refine ⟨9340260223248010022694515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6226840148832006681796343 9340260223248010022694515)
  ·
    refine ⟨14010390334872015034041773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9340260223248010022694515 14010390334872015034041773)
    ·
      refine ⟨5253896375577005637765665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14010390334872015034041773 5253896375577005637765665)
      ·
        refine ⟨3940422281682754228324249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5253896375577005637765665 3940422281682754228324249)
        ·
          refine ⟨2955316711262065671243187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3940422281682754228324249 2955316711262065671243187)
          ·
            refine ⟨4432975066893098506864781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2955316711262065671243187 4432975066893098506864781)
            ·
              refine ⟨1662365650084911940074293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4432975066893098506864781 1662365650084911940074293)
              ·
                refine ⟨155846779695460494381965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1662365650084911940074293 155846779695460494381965)
                ·
                  refine ⟨58442542385797685393237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 155846779695460494381965 58442542385797685393237)
                  ·
                    rfl

theorem cell21_256087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 3, 5, 3].length) (baseStart_256087 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_256087 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_256087 prefixEnd_256087 := by exact prefixLift 256087
  have htrace : WordTrace (prefixWord ++ tailWord_256087) baseStart_256087 baseEnd_256087 := by
    simpa [prefixWord, tailWord_256087, baseEnd_256087] using wordTrace_append hprefix tailTrace_256087
  have hstable : (prefixWord ++ tailWord_256087).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_256087).length < 2 ^ (prefixWord ++ tailWord_256087).sum := by decide
  have hdescent : baseEnd_256087 < baseStart_256087 := by decide
  rcases family_descends (prefixWord ++ tailWord_256087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_256101 : List Nat := [1, 3, 1, 3, 2, 3, 1, 1, 6]
def baseStart_256101 : Nat := 118140960795 + 256101 * 2 ^ 59
def prefixEnd_256101 : Nat := 4983230072969 + 3 ^ 40 * 256101 * 2
def baseEnd_256101 : Nat := 58445737376536772159875

theorem tailTrace_256101 : CollatzResearch.WordTrace tailWord_256101 prefixEnd_256101 58445737376536772159875 := by
  unfold tailWord_256101
  simp only [CollatzResearch.WordTrace]
  refine ⟨9340770845197290413704157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6227180563464860275802771 9340770845197290413704157)
  ·
    refine ⟨3502789066948983905139059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9340770845197290413704157 3502789066948983905139059)
    ·
      refine ⟨5254183600423475857708589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3502789066948983905139059 5254183600423475857708589)
      ·
        refine ⟨1970318850158803446640721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5254183600423475857708589 1970318850158803446640721)
        ·
          refine ⟨1477739137619102584980541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1970318850158803446640721 1477739137619102584980541)
          ·
            refine ⟨554152176607163469367703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1477739137619102584980541 554152176607163469367703)
            ·
              refine ⟨831228264910745204051555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 554152176607163469367703 831228264910745204051555)
              ·
                refine ⟨1246842397366117806077333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 831228264910745204051555 1246842397366117806077333)
                ·
                  refine ⟨58445737376536772159875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1246842397366117806077333 58445737376536772159875)
                  ·
                    rfl

theorem cell21_256101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 3, 1, 1, 6].length) (baseStart_256101 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_256101 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_256101 prefixEnd_256101 := by exact prefixLift 256101
  have htrace : WordTrace (prefixWord ++ tailWord_256101) baseStart_256101 baseEnd_256101 := by
    simpa [prefixWord, tailWord_256101, baseEnd_256101] using wordTrace_append hprefix tailTrace_256101
  have hstable : (prefixWord ++ tailWord_256101).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_256101).length < 2 ^ (prefixWord ++ tailWord_256101).sum := by decide
  have hdescent : baseEnd_256101 < baseStart_256101 := by decide
  rcases family_descends (prefixWord ++ tailWord_256101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_256214 : List Nat := [5, 2, 1, 2, 1, 1, 4, 2, 3]
def baseStart_256214 : Nat := 118140960795 + 256214 * 2 ^ 59
def prefixEnd_256214 : Nat := 4983230072969 + 3 ^ 40 * 256214 * 2
def baseEnd_256214 : Nat := 58471525516073686776311

theorem tailTrace_256214 : CollatzResearch.WordTrace tailWord_256214 prefixEnd_256214 58471525516073686776311 := by
  unfold tailWord_256214
  simp only [CollatzResearch.WordTrace]
  refine ⟨584055768361744419535481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 6229928195858607141711797 584055768361744419535481)
  ·
    refine ⟨438041826271308314651611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 584055768361744419535481 438041826271308314651611)
    ·
      refine ⟨657062739406962471977417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 438041826271308314651611 657062739406962471977417)
      ·
        refine ⟨492797054555221853983063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 657062739406962471977417 492797054555221853983063)
        ·
          refine ⟨739195581832832780974595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 492797054555221853983063 739195581832832780974595)
          ·
            refine ⟨1108793372749249171461893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 739195581832832780974595 1108793372749249171461893)
            ·
              refine ⟨207898757390484219649105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1108793372749249171461893 207898757390484219649105)
              ·
                refine ⟨155924068042863164736829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 207898757390484219649105 155924068042863164736829)
                ·
                  refine ⟨58471525516073686776311, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 155924068042863164736829 58471525516073686776311)
                  ·
                    rfl

theorem cell21_256214_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 4, 2, 3].length) (baseStart_256214 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_256214 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_256214 prefixEnd_256214 := by exact prefixLift 256214
  have htrace : WordTrace (prefixWord ++ tailWord_256214) baseStart_256214 baseEnd_256214 := by
    simpa [prefixWord, tailWord_256214, baseEnd_256214] using wordTrace_append hprefix tailTrace_256214
  have hstable : (prefixWord ++ tailWord_256214).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_256214).length < 2 ^ (prefixWord ++ tailWord_256214).sum := by decide
  have hdescent : baseEnd_256214 < baseStart_256214 := by decide
  rcases family_descends (prefixWord ++ tailWord_256214) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_256301 : List Nat := [1, 5, 3, 1, 2, 1, 1, 7]
def baseStart_256301 : Nat := 118140960795 + 256301 * 2 ^ 59
def prefixEnd_256301 : Nat := 4983230072969 + 3 ^ 40 * 256301 * 2
def baseEnd_256301 : Nat := 19497126700460289608711

theorem tailTrace_256301 : CollatzResearch.WordTrace tailWord_256301 prefixEnd_256301 19497126700460289608711 := by
  unfold tailWord_256301
  simp only [CollatzResearch.WordTrace]
  refine ⟨9348065444472724570984757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6232043629648483047323171 9348065444472724570984757)
  ·
    refine ⟨876381135419317928529821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 9348065444472724570984757 876381135419317928529821)
    ·
      refine ⟨328642925782244223198683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 876381135419317928529821 328642925782244223198683)
      ·
        refine ⟨492964388673366334798025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 328642925782244223198683 492964388673366334798025)
        ·
          refine ⟨369723291505024751098519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 492964388673366334798025 369723291505024751098519)
          ·
            refine ⟨554584937257537126647779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 369723291505024751098519 554584937257537126647779)
            ·
              refine ⟨831877405886305689971669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 554584937257537126647779 831877405886305689971669)
              ·
                refine ⟨19497126700460289608711, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 831877405886305689971669 19497126700460289608711)
                ·
                  rfl

theorem cell21_256301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 2, 1, 1, 7].length) (baseStart_256301 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_256301 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_256301 prefixEnd_256301 := by exact prefixLift 256301
  have htrace : WordTrace (prefixWord ++ tailWord_256301) baseStart_256301 baseEnd_256301 := by
    simpa [prefixWord, tailWord_256301, baseEnd_256301] using wordTrace_append hprefix tailTrace_256301
  have hstable : (prefixWord ++ tailWord_256301).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_256301).length < 2 ^ (prefixWord ++ tailWord_256301).sum := by decide
  have hdescent : baseEnd_256301 < baseStart_256301 := by decide
  rcases family_descends (prefixWord ++ tailWord_256301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_256312 : List Nat := [2, 1, 2, 1, 3, 1, 3, 2, 6]
def baseStart_256312 : Nat := 118140960795 + 256312 * 2 ^ 59
def prefixEnd_256312 : Nat := 4983230072969 + 3 ^ 40 * 256312 * 2
def baseEnd_256312 : Nat := 58493890451247294142777

theorem tailTrace_256312 : CollatzResearch.WordTrace tailWord_256312 prefixEnd_256312 58493890451247294142777 := by
  unfold tailWord_256312
  simp only [CollatzResearch.WordTrace]
  refine ⟨4674233323716436724817595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6232311098288582299756793 4674233323716436724817595)
  ·
    refine ⟨7011349985574655087226393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4674233323716436724817595 7011349985574655087226393)
    ·
      refine ⟨5258512489180991315419795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7011349985574655087226393 5258512489180991315419795)
      ·
        refine ⟨7887768733771486973129693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5258512489180991315419795 7887768733771486973129693)
        ·
          refine ⟨2957913275164307614923635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7887768733771486973129693 2957913275164307614923635)
          ·
            refine ⟨4436869912746461422385453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2957913275164307614923635 4436869912746461422385453)
            ·
              refine ⟨1663826217279923033394545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4436869912746461422385453 1663826217279923033394545)
              ·
                refine ⟨1247869662959942275045909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1663826217279923033394545 1247869662959942275045909)
                ·
                  refine ⟨58493890451247294142777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1247869662959942275045909 58493890451247294142777)
                  ·
                    rfl

theorem cell21_256312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 3, 2, 6].length) (baseStart_256312 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_256312 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_256312 prefixEnd_256312 := by exact prefixLift 256312
  have htrace : WordTrace (prefixWord ++ tailWord_256312) baseStart_256312 baseEnd_256312 := by
    simpa [prefixWord, tailWord_256312, baseEnd_256312] using wordTrace_append hprefix tailTrace_256312
  have hstable : (prefixWord ++ tailWord_256312).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_256312).length < 2 ^ (prefixWord ++ tailWord_256312).sum := by decide
  have hdescent : baseEnd_256312 < baseStart_256312 := by decide
  rcases family_descends (prefixWord ++ tailWord_256312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_256332 : List Nat := [2, 2, 1, 3, 2, 1, 5, 2, 3]
def baseStart_256332 : Nat := 118140960795 + 256332 * 2 ^ 59
def prefixEnd_256332 : Nat := 4983230072969 + 3 ^ 40 * 256332 * 2
def baseEnd_256332 : Nat := 58498454723731703809403

theorem tailTrace_256332 : CollatzResearch.WordTrace tailWord_256332 prefixEnd_256332 58498454723731703809403 := by
  unfold tailWord_256332
  simp only [CollatzResearch.WordTrace]
  refine ⟨4674598053680208432681625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6232797404906944576908833 4674598053680208432681625)
  ·
    refine ⟨3505948540260156324511219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4674598053680208432681625 3505948540260156324511219)
    ·
      refine ⟨5258922810390234486766829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3505948540260156324511219 5258922810390234486766829)
      ·
        refine ⟨1972096053896337932537561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5258922810390234486766829 1972096053896337932537561)
        ·
          refine ⟨1479072040422253449403171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1972096053896337932537561 1479072040422253449403171)
          ·
            refine ⟨2218608060633380174104757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1479072040422253449403171 2218608060633380174104757)
            ·
              refine ⟨207994505684379391322321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 2218608060633380174104757 207994505684379391322321)
              ·
                refine ⟨155995879263284543491741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 207994505684379391322321 155995879263284543491741)
                ·
                  refine ⟨58498454723731703809403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 155995879263284543491741 58498454723731703809403)
                  ·
                    rfl

theorem cell21_256332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 5, 2, 3].length) (baseStart_256332 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_256332 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_256332 prefixEnd_256332 := by exact prefixLift 256332
  have htrace : WordTrace (prefixWord ++ tailWord_256332) baseStart_256332 baseEnd_256332 := by
    simpa [prefixWord, tailWord_256332, baseEnd_256332] using wordTrace_append hprefix tailTrace_256332
  have hstable : (prefixWord ++ tailWord_256332).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_256332).length < 2 ^ (prefixWord ++ tailWord_256332).sum := by decide
  have hdescent : baseEnd_256332 < baseStart_256332 := by decide
  rcases family_descends (prefixWord ++ tailWord_256332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_256343 : List Nat := [1, 1, 3, 2, 3, 1, 4, 6]
def baseStart_256343 : Nat := 118140960795 + 256343 * 2 ^ 59
def prefixEnd_256343 : Nat := 4983230072969 + 3 ^ 40 * 256343 * 2
def baseEnd_256343 : Nat := 19500321691199376375349

theorem tailTrace_256343 : CollatzResearch.WordTrace tailWord_256343 prefixEnd_256343 19500321691199376375349 := by
  unfold tailWord_256343
  simp only [CollatzResearch.WordTrace]
  refine ⟨9349597310320565744013683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6233064873547043829342455 9349597310320565744013683)
  ·
    refine ⟨14024395965480848616020525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9349597310320565744013683 14024395965480848616020525)
    ·
      refine ⟨5259148487055318231007697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14024395965480848616020525 5259148487055318231007697)
      ·
        refine ⟨3944361365291488673255773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5259148487055318231007697 3944361365291488673255773)
        ·
          refine ⟨1479135511984308252470915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3944361365291488673255773 1479135511984308252470915)
          ·
            refine ⟨2218703267976462378706373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1479135511984308252470915 2218703267976462378706373)
            ·
              refine ⟨416006862745586696007445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2218703267976462378706373 416006862745586696007445)
              ·
                refine ⟨19500321691199376375349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 416006862745586696007445 19500321691199376375349)
                ·
                  rfl

theorem cell21_256343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 4, 6].length) (baseStart_256343 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_256343 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_256343 prefixEnd_256343 := by exact prefixLift 256343
  have htrace : WordTrace (prefixWord ++ tailWord_256343) baseStart_256343 baseEnd_256343 := by
    simpa [prefixWord, tailWord_256343, baseEnd_256343] using wordTrace_append hprefix tailTrace_256343
  have hstable : (prefixWord ++ tailWord_256343).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_256343).length < 2 ^ (prefixWord ++ tailWord_256343).sum := by decide
  have hdescent : baseEnd_256343 < baseStart_256343 := by decide
  rcases family_descends (prefixWord ++ tailWord_256343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_256391 : List Nat := [1, 1, 4, 2, 2, 1, 3, 4, 3]
def baseStart_256391 : Nat := 118140960795 + 256391 * 2 ^ 59
def prefixEnd_256391 : Nat := 4983230072969 + 3 ^ 40 * 256391 * 2
def baseEnd_256391 : Nat := 58511919327560712325949

theorem tailTrace_256391 : CollatzResearch.WordTrace tailWord_256391 prefixEnd_256391 58511919327560712325949 := by
  unfold tailWord_256391
  simp only [CollatzResearch.WordTrace]
  refine ⟨9351348014146669941761027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6234232009431113294507351 9351348014146669941761027)
  ·
    refine ⟨14027022021220004912641541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9351348014146669941761027 14027022021220004912641541)
    ·
      refine ⟨2630066628978750921120289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 14027022021220004912641541 2630066628978750921120289)
      ·
        refine ⟨1972549971734063190840217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2630066628978750921120289 1972549971734063190840217)
        ·
          refine ⟨1479412478800547393130163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1972549971734063190840217 1479412478800547393130163)
          ·
            refine ⟨2219118718200821089695245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1479412478800547393130163 2219118718200821089695245)
            ·
              refine ⟨832169519325307908635717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2219118718200821089695245 832169519325307908635717)
              ·
                refine ⟨156031784873495232869197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 832169519325307908635717 156031784873495232869197)
                ·
                  refine ⟨58511919327560712325949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 156031784873495232869197 58511919327560712325949)
                  ·
                    rfl

theorem cell21_256391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 3, 4, 3].length) (baseStart_256391 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_256391 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_256391 prefixEnd_256391 := by exact prefixLift 256391
  have htrace : WordTrace (prefixWord ++ tailWord_256391) baseStart_256391 baseEnd_256391 := by
    simpa [prefixWord, tailWord_256391, baseEnd_256391] using wordTrace_append hprefix tailTrace_256391
  have hstable : (prefixWord ++ tailWord_256391).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_256391).length < 2 ^ (prefixWord ++ tailWord_256391).sum := by decide
  have hdescent : baseEnd_256391 < baseStart_256391 := by decide
  rcases family_descends (prefixWord ++ tailWord_256391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_256394 : List Nat := [3, 1, 2, 5, 2, 1, 1, 6]
def baseStart_256394 : Nat := 118140960795 + 256394 * 2 ^ 59
def prefixEnd_256394 : Nat := 4983230072969 + 3 ^ 40 * 256394 * 2
def baseEnd_256394 : Nat := 19504201322811124591981

theorem tailTrace_256394 : CollatzResearch.WordTrace tailWord_256394 prefixEnd_256394 19504201322811124591981 := by
  unfold tailWord_256394
  simp only [CollatzResearch.WordTrace]
  refine ⟨2337864358283950363530059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6234304955423867636080157 2337864358283950363530059)
  ·
    refine ⟨3506796537425925545295089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2337864358283950363530059 3506796537425925545295089)
    ·
      refine ⟨2630097403069444158971317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3506796537425925545295089 2630097403069444158971317)
      ·
        refine ⟨246571631537760389903561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 2630097403069444158971317 246571631537760389903561)
        ·
          refine ⟨184928723653320292427671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 246571631537760389903561 184928723653320292427671)
          ·
            refine ⟨277393085479980438641507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 184928723653320292427671 277393085479980438641507)
            ·
              refine ⟨416089628219970657962261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 277393085479980438641507 416089628219970657962261)
              ·
                refine ⟨19504201322811124591981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 416089628219970657962261 19504201322811124591981)
                ·
                  rfl

theorem cell21_256394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 2, 1, 1, 6].length) (baseStart_256394 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_256394 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_256394 prefixEnd_256394 := by exact prefixLift 256394
  have htrace : WordTrace (prefixWord ++ tailWord_256394) baseStart_256394 baseEnd_256394 := by
    simpa [prefixWord, tailWord_256394, baseEnd_256394] using wordTrace_append hprefix tailTrace_256394
  have hstable : (prefixWord ++ tailWord_256394).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_256394).length < 2 ^ (prefixWord ++ tailWord_256394).sum := by decide
  have hdescent : baseEnd_256394 < baseStart_256394 := by decide
  rcases family_descends (prefixWord ++ tailWord_256394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_256501 : List Nat := [1, 3, 5, 1, 3, 1, 1, 1, 5]
def baseStart_256501 : Nat := 118140960795 + 256501 * 2 ^ 59
def prefixEnd_256501 : Nat := 4983230072969 + 3 ^ 40 * 256501 * 2
def baseEnd_256501 : Nat := 58537022826224965492391

theorem tailTrace_256501 : CollatzResearch.WordTrace tailWord_256501 prefixEnd_256501 58537022826224965492391 := by
  unfold tailWord_256501
  simp only [CollatzResearch.WordTrace]
  refine ⟨9355360043748158728265357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6236906695832105818843571 9355360043748158728265357)
  ·
    refine ⟨3508260016405559523099509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9355360043748158728265357 3508260016405559523099509)
    ·
      refine ⟨328899376538021205290579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 3508260016405559523099509 328899376538021205290579)
      ·
        refine ⟨493349064807031807935869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 328899376538021205290579 493349064807031807935869)
        ·
          refine ⟨185005899302636927975951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 493349064807031807935869 185005899302636927975951)
          ·
            refine ⟨277508848953955391963927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 185005899302636927975951 277508848953955391963927)
            ·
              refine ⟨416263273430933087945891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 277508848953955391963927 416263273430933087945891)
              ·
                refine ⟨624394910146399631918837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 416263273430933087945891 624394910146399631918837)
                ·
                  refine ⟨58537022826224965492391, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 624394910146399631918837 58537022826224965492391)
                  ·
                    rfl

theorem cell21_256501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 3, 1, 1, 1, 5].length) (baseStart_256501 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_256501 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_256501 prefixEnd_256501 := by exact prefixLift 256501
  have htrace : WordTrace (prefixWord ++ tailWord_256501) baseStart_256501 baseEnd_256501 := by
    simpa [prefixWord, tailWord_256501, baseEnd_256501] using wordTrace_append hprefix tailTrace_256501
  have hstable : (prefixWord ++ tailWord_256501).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_256501).length < 2 ^ (prefixWord ++ tailWord_256501).sum := by decide
  have hdescent : baseEnd_256501 < baseStart_256501 := by decide
  rcases family_descends (prefixWord ++ tailWord_256501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_256754 : List Nat := [3, 2, 1, 3, 1, 3, 1, 2, 5]
def baseStart_256754 : Nat := 118140960795 + 256754 * 2 ^ 59
def prefixEnd_256754 : Nat := 4983230072969 + 3 ^ 40 * 256754 * 2
def baseEnd_256754 : Nat := 58594760873152747775207

theorem tailTrace_256754 : CollatzResearch.WordTrace tailWord_256754 prefixEnd_256754 58594760873152747775207 := by
  unfold tailWord_256754
  simp only [CollatzResearch.WordTrace]
  refine ⟨2341146927957895734306329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6243058474554388624816877 2341146927957895734306329)
  ·
    refine ⟨1755860195968421800729747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2341146927957895734306329 1755860195968421800729747)
    ·
      refine ⟨2633790293952632701094621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1755860195968421800729747 2633790293952632701094621)
      ·
        refine ⟨987671360232237262910483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2633790293952632701094621 987671360232237262910483)
        ·
          refine ⟨1481507040348355894365725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 987671360232237262910483 1481507040348355894365725)
          ·
            refine ⟨555565140130633460387147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1481507040348355894365725 555565140130633460387147)
            ·
              refine ⟨833347710195950190580721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 555565140130633460387147 833347710195950190580721)
              ·
                refine ⟨625010782646962642935541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 833347710195950190580721 625010782646962642935541)
                ·
                  refine ⟨58594760873152747775207, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 625010782646962642935541 58594760873152747775207)
                  ·
                    rfl

theorem cell21_256754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 3, 1, 2, 5].length) (baseStart_256754 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_256754 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_256754 prefixEnd_256754 := by exact prefixLift 256754
  have htrace : WordTrace (prefixWord ++ tailWord_256754) baseStart_256754 baseEnd_256754 := by
    simpa [prefixWord, tailWord_256754, baseEnd_256754] using wordTrace_append hprefix tailTrace_256754
  have hstable : (prefixWord ++ tailWord_256754).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_256754).length < 2 ^ (prefixWord ++ tailWord_256754).sum := by decide
  have hdescent : baseEnd_256754 < baseStart_256754 := by decide
  rcases family_descends (prefixWord ++ tailWord_256754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_256802 : List Nat := [3, 3, 1, 1, 2, 3, 3, 1, 4]
def baseStart_256802 : Nat := 118140960795 + 256802 * 2 ^ 59
def prefixEnd_256802 : Nat := 4983230072969 + 3 ^ 40 * 256802 * 2
def baseEnd_256802 : Nat := 58605715127115330975109

theorem tailTrace_256802 : CollatzResearch.WordTrace tailWord_256802 prefixEnd_256802 58605715127115330975109 := by
  unfold tailWord_256802
  simp only [CollatzResearch.WordTrace]
  refine ⟨2341584603914421783743165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6244225610438458089981773 2341584603914421783743165)
  ·
    refine ⟨878094226467908168903687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2341584603914421783743165 878094226467908168903687)
    ·
      refine ⟨1317141339701862253355531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 878094226467908168903687 1317141339701862253355531)
      ·
        refine ⟨1975712009552793380033297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1317141339701862253355531 1975712009552793380033297)
        ·
          refine ⟨1481784007164595035024973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1975712009552793380033297 1481784007164595035024973)
          ·
            refine ⟨555669002686723138134365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1481784007164595035024973 555669002686723138134365)
            ·
              refine ⟨208375876007521176800387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 555669002686723138134365 208375876007521176800387)
              ·
                refine ⟨312563814011281765200581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 208375876007521176800387 312563814011281765200581)
                ·
                  refine ⟨58605715127115330975109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 312563814011281765200581 58605715127115330975109)
                  ·
                    rfl

theorem cell21_256802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 3, 3, 1, 4].length) (baseStart_256802 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_256802 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_256802 prefixEnd_256802 := by exact prefixLift 256802
  have htrace : WordTrace (prefixWord ++ tailWord_256802) baseStart_256802 baseEnd_256802 := by
    simpa [prefixWord, tailWord_256802, baseEnd_256802] using wordTrace_append hprefix tailTrace_256802
  have hstable : (prefixWord ++ tailWord_256802).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_256802).length < 2 ^ (prefixWord ++ tailWord_256802).sum := by decide
  have hdescent : baseEnd_256802 < baseStart_256802 := by decide
  rcases family_descends (prefixWord ++ tailWord_256802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_256822 : List Nat := [5, 1, 2, 2, 3, 1, 1, 3, 3]
def baseStart_256822 : Nat := 118140960795 + 256822 * 2 ^ 59
def prefixEnd_256822 : Nat := 4983230072969 + 3 ^ 40 * 256822 * 2
def baseEnd_256822 : Nat := 58610279399599740641735

theorem tailTrace_256822 : CollatzResearch.WordTrace tailWord_256822 prefixEnd_256822 58610279399599740641735 := by
  unfold tailWord_256822
  simp only [CollatzResearch.WordTrace]
  refine ⟨585441742224076909418795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 6244711917056820367133813 585441742224076909418795)
  ·
    refine ⟨878162613336115364128193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 585441742224076909418795 878162613336115364128193)
    ·
      refine ⟨658621960002086523096145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 878162613336115364128193 658621960002086523096145)
      ·
        refine ⟨493966470001564892322109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 658621960002086523096145 493966470001564892322109)
        ·
          refine ⟨185237426250586834620791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 493966470001564892322109 185237426250586834620791)
          ·
            refine ⟨277856139375880251931187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 185237426250586834620791 277856139375880251931187)
            ·
              refine ⟨416784209063820377896781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 277856139375880251931187 416784209063820377896781)
              ·
                refine ⟨156294078398932641711293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 416784209063820377896781 156294078398932641711293)
                ·
                  refine ⟨58610279399599740641735, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 156294078398932641711293 58610279399599740641735)
                  ·
                    rfl

theorem cell21_256822_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 3, 1, 1, 3, 3].length) (baseStart_256822 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_256822 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_256822 prefixEnd_256822 := by exact prefixLift 256822
  have htrace : WordTrace (prefixWord ++ tailWord_256822) baseStart_256822 baseEnd_256822 := by
    simpa [prefixWord, tailWord_256822, baseEnd_256822] using wordTrace_append hprefix tailTrace_256822
  have hstable : (prefixWord ++ tailWord_256822).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_256822).length < 2 ^ (prefixWord ++ tailWord_256822).sum := by decide
  have hdescent : baseEnd_256822 < baseStart_256822 := by decide
  rcases family_descends (prefixWord ++ tailWord_256822) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_256833 : List Nat := [1, 2, 5, 3, 2, 1, 7]
def baseStart_256833 : Nat := 118140960795 + 256833 * 2 ^ 59
def prefixEnd_256833 : Nat := 4983230072969 + 3 ^ 40 * 256833 * 2
def baseEnd_256833 : Nat := 6512532194385129550931

theorem tailTrace_256833 : CollatzResearch.WordTrace tailWord_256833 prefixEnd_256833 6512532194385129550931 := by
  unfold tailWord_256833
  simp only [CollatzResearch.WordTrace]
  refine ⟨9367469078545379429351153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6244979385696919619567435 9367469078545379429351153)
  ·
    refine ⟨7025601808909034572013365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9367469078545379429351153 7025601808909034572013365)
    ·
      refine ⟨658650169585221991126253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 7025601808909034572013365 658650169585221991126253)
      ·
        refine ⟨246993813594458246672345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 658650169585221991126253 246993813594458246672345)
        ·
          refine ⟨185245360195843685004259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 246993813594458246672345 185245360195843685004259)
          ·
            refine ⟨277868040293765527506389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 185245360195843685004259 277868040293765527506389)
            ·
              refine ⟨6512532194385129550931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 277868040293765527506389 6512532194385129550931)
              ·
                rfl

theorem cell21_256833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 2, 1, 7].length) (baseStart_256833 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_256833 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_256833 prefixEnd_256833 := by exact prefixLift 256833
  have htrace : WordTrace (prefixWord ++ tailWord_256833) baseStart_256833 baseEnd_256833 := by
    simpa [prefixWord, tailWord_256833, baseEnd_256833] using wordTrace_append hprefix tailTrace_256833
  have hstable : (prefixWord ++ tailWord_256833).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_256833).length < 2 ^ (prefixWord ++ tailWord_256833).sum := by decide
  have hdescent : baseEnd_256833 < baseStart_256833 := by decide
  rcases family_descends (prefixWord ++ tailWord_256833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_256844 : List Nat := [2, 2, 1, 3, 3, 1, 2, 1, 6]
def baseStart_256844 : Nat := 118140960795 + 256844 * 2 ^ 59
def prefixEnd_256844 : Nat := 4983230072969 + 3 ^ 40 * 256844 * 2
def baseEnd_256844 : Nat := 58615300099332591275023

theorem tailTrace_256844 : CollatzResearch.WordTrace tailWord_256844 prefixEnd_256844 58615300099332591275023 := by
  unfold tailWord_256844
  simp only [CollatzResearch.WordTrace]
  refine ⟨4683935140752764154000793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6245246854337018872001057 4683935140752764154000793)
  ·
    refine ⟨3512951355564573115500595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4683935140752764154000793 3512951355564573115500595)
    ·
      refine ⟨5269427033346859673250893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3512951355564573115500595 5269427033346859673250893)
      ·
        refine ⟨1976035137505072377469085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5269427033346859673250893 1976035137505072377469085)
        ·
          refine ⟨741013176564402141550907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1976035137505072377469085 741013176564402141550907)
          ·
            refine ⟨1111519764846603212326361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 741013176564402141550907 1111519764846603212326361)
            ·
              refine ⟨833639823634952409244771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1111519764846603212326361 833639823634952409244771)
              ·
                refine ⟨1250459735452428613867157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 833639823634952409244771 1250459735452428613867157)
                ·
                  refine ⟨58615300099332591275023, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1250459735452428613867157 58615300099332591275023)
                  ·
                    rfl

theorem cell21_256844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 2, 1, 6].length) (baseStart_256844 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_256844 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_256844 prefixEnd_256844 := by exact prefixLift 256844
  have htrace : WordTrace (prefixWord ++ tailWord_256844) baseStart_256844 baseEnd_256844 := by
    simpa [prefixWord, tailWord_256844, baseEnd_256844] using wordTrace_append hprefix tailTrace_256844
  have hstable : (prefixWord ++ tailWord_256844).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_256844).length < 2 ^ (prefixWord ++ tailWord_256844).sum := by decide
  have hdescent : baseEnd_256844 < baseStart_256844 := by decide
  rcases family_descends (prefixWord ++ tailWord_256844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_256858 : List Nat := [3, 1, 1, 2, 1, 4, 1, 8]
def baseStart_256858 : Nat := 118140960795 + 256858 * 2 ^ 59
def prefixEnd_256858 : Nat := 4983230072969 + 3 ^ 40 * 256858 * 2
def baseEnd_256858 : Nat := 19539498363357226013887

theorem tailTrace_256858 : CollatzResearch.WordTrace tailWord_256858 prefixEnd_256858 19539498363357226013887 := by
  unfold tailWord_256858
  simp only [CollatzResearch.WordTrace]
  refine ⟨2342095225863702174752807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6245587268969872466007485 2342095225863702174752807)
  ·
    refine ⟨3513142838795553262129211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2342095225863702174752807 3513142838795553262129211)
    ·
      refine ⟨5269714258193329893193817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3513142838795553262129211 5269714258193329893193817)
      ·
        refine ⟨3952285693644997419895363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5269714258193329893193817 3952285693644997419895363)
        ·
          refine ⟨5928428540467496129843045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3952285693644997419895363 5928428540467496129843045)
          ·
            refine ⟨1111580351337655524345571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5928428540467496129843045 1111580351337655524345571)
            ·
              refine ⟨1667370527006483286518357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1111580351337655524345571 1667370527006483286518357)
              ·
                refine ⟨19539498363357226013887, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1667370527006483286518357 19539498363357226013887)
                ·
                  rfl

theorem cell21_256858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 1, 8].length) (baseStart_256858 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_256858 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_256858 prefixEnd_256858 := by exact prefixLift 256858
  have htrace : WordTrace (prefixWord ++ tailWord_256858) baseStart_256858 baseEnd_256858 := by
    simpa [prefixWord, tailWord_256858, baseEnd_256858] using wordTrace_append hprefix tailTrace_256858
  have hstable : (prefixWord ++ tailWord_256858).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_256858).length < 2 ^ (prefixWord ++ tailWord_256858).sum := by decide
  have hdescent : baseEnd_256858 < baseStart_256858 := by decide
  rcases family_descends (prefixWord ++ tailWord_256858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_256999 : List Nat := [1, 1, 5, 2, 2, 1, 3, 3, 3]
def baseStart_256999 : Nat := 118140960795 + 256999 * 2 ^ 59
def prefixEnd_256999 : Nat := 4983230072969 + 3 ^ 40 * 256999 * 2
def baseEnd_256999 : Nat := 58650673211086766191373

theorem tailTrace_256999 : CollatzResearch.WordTrace tailWord_256999 prefixEnd_256999 58650673211086766191373 := by
  unfold tailWord_256999
  simp only [CollatzResearch.WordTrace]
  refine ⟨9373523595943989779894051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6249015730629326519929367 9373523595943989779894051)
  ·
    refine ⟨14060285393915984669841077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9373523595943989779894051 14060285393915984669841077)
    ·
      refine ⟨1318151755679623562797601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 14060285393915984669841077 1318151755679623562797601)
      ·
        refine ⟨988613816759717672098201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1318151755679623562797601 988613816759717672098201)
        ·
          refine ⟨741460362569788254073651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 988613816759717672098201 741460362569788254073651)
          ·
            refine ⟨1112190543854682381110477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 741460362569788254073651 1112190543854682381110477)
            ·
              refine ⟨417071453945505892916429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1112190543854682381110477 417071453945505892916429)
              ·
                refine ⟨156401795229564709843661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 417071453945505892916429 156401795229564709843661)
                ·
                  refine ⟨58650673211086766191373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 156401795229564709843661 58650673211086766191373)
                  ·
                    rfl

theorem cell21_256999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 3, 3, 3].length) (baseStart_256999 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_256999 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_256999 prefixEnd_256999 := by exact prefixLift 256999
  have htrace : WordTrace (prefixWord ++ tailWord_256999) baseStart_256999 baseEnd_256999 := by
    simpa [prefixWord, tailWord_256999, baseEnd_256999] using wordTrace_append hprefix tailTrace_256999
  have hstable : (prefixWord ++ tailWord_256999).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_256999).length < 2 ^ (prefixWord ++ tailWord_256999).sum := by decide
  have hdescent : baseEnd_256999 < baseStart_256999 := by decide
  rcases family_descends (prefixWord ++ tailWord_256999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_257072 : List Nat := [2, 1, 1, 1, 2, 4, 4, 2, 4]
def baseStart_257072 : Nat := 118140960795 + 257072 * 2 ^ 59
def prefixEnd_257072 : Nat := 4983230072969 + 3 ^ 40 * 257072 * 2
def baseEnd_257072 : Nat := 58667332805654861474557

theorem tailTrace_257072 : CollatzResearch.WordTrace tailWord_257072 prefixEnd_257072 58667332805654861474557 := by
  unfold tailWord_257072
  simp only [CollatzResearch.WordTrace]
  refine ⟨4688093062339761623650735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6250790749786348831534313 4688093062339761623650735)
  ·
    refine ⟨7032139593509642435476103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4688093062339761623650735 7032139593509642435476103)
    ·
      refine ⟨10548209390264463653214155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7032139593509642435476103 10548209390264463653214155)
      ·
        refine ⟨15822314085396695479821233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10548209390264463653214155 15822314085396695479821233)
        ·
          refine ⟨11866735564047521609865925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15822314085396695479821233 11866735564047521609865925)
          ·
            refine ⟨2225012918258910301849861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11866735564047521609865925 2225012918258910301849861)
            ·
              refine ⟨417189922173545681596849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2225012918258910301849861 417189922173545681596849)
              ·
                refine ⟨312892441630159261197637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 417189922173545681596849 312892441630159261197637)
                ·
                  refine ⟨58667332805654861474557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 312892441630159261197637 58667332805654861474557)
                  ·
                    rfl

theorem cell21_257072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 4, 2, 4].length) (baseStart_257072 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_257072 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_257072 prefixEnd_257072 := by exact prefixLift 257072
  have htrace : WordTrace (prefixWord ++ tailWord_257072) baseStart_257072 baseEnd_257072 := by
    simpa [prefixWord, tailWord_257072, baseEnd_257072] using wordTrace_append hprefix tailTrace_257072
  have hstable : (prefixWord ++ tailWord_257072).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_257072).length < 2 ^ (prefixWord ++ tailWord_257072).sum := by decide
  have hdescent : baseEnd_257072 < baseStart_257072 := by decide
  rcases family_descends (prefixWord ++ tailWord_257072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_257134 : List Nat := [4, 1, 2, 2, 1, 3, 2, 1, 5]
def baseStart_257134 : Nat := 118140960795 + 257134 * 2 ^ 59
def prefixEnd_257134 : Nat := 4983230072969 + 3 ^ 40 * 257134 * 2
def baseEnd_257134 : Nat := 58681482050356531441097

theorem tailTrace_257134 : CollatzResearch.WordTrace tailWord_257134 prefixEnd_257134 58681482050356531441097 := by
  unfold tailWord_257134
  simp only [CollatzResearch.WordTrace]
  refine ⟨1172305931306863479507307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 6252298300303271890705637 1172305931306863479507307)
  ·
    refine ⟨1758458896960295219260961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1172305931306863479507307 1758458896960295219260961)
    ·
      refine ⟨1318844172720221414445721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1758458896960295219260961 1318844172720221414445721)
      ·
        refine ⟨989133129540166060834291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1318844172720221414445721 989133129540166060834291)
        ·
          refine ⟨1483699694310249091251437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 989133129540166060834291 1483699694310249091251437)
          ·
            refine ⟨556387385366343409219289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1483699694310249091251437 556387385366343409219289)
            ·
              refine ⟨417290539024757556914467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 556387385366343409219289 417290539024757556914467)
              ·
                refine ⟨625935808537136335371701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 417290539024757556914467 625935808537136335371701)
                ·
                  refine ⟨58681482050356531441097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 625935808537136335371701 58681482050356531441097)
                  ·
                    rfl

theorem cell21_257134_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 3, 2, 1, 5].length) (baseStart_257134 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_257134 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_257134 prefixEnd_257134 := by exact prefixLift 257134
  have htrace : WordTrace (prefixWord ++ tailWord_257134) baseStart_257134 baseEnd_257134 := by
    simpa [prefixWord, tailWord_257134, baseEnd_257134] using wordTrace_append hprefix tailTrace_257134
  have hstable : (prefixWord ++ tailWord_257134).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_257134).length < 2 ^ (prefixWord ++ tailWord_257134).sum := by decide
  have hdescent : baseEnd_257134 < baseStart_257134 := by decide
  rcases family_descends (prefixWord ++ tailWord_257134) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_257162 : List Nat := [3, 1, 2, 3, 1, 1, 3, 7]
def baseStart_257162 : Nat := 118140960795 + 257162 * 2 ^ 59
def prefixEnd_257162 : Nat := 4983230072969 + 3 ^ 40 * 257162 * 2
def baseEnd_257162 : Nat := 19562624010611568324791

theorem tailTrace_257162 : CollatzResearch.WordTrace tailWord_257162 prefixEnd_257162 19562624010611568324791 := by
  unfold tailWord_257162
  simp only [CollatzResearch.WordTrace]
  refine ⟨2344867173588367154519435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6252979129568979078718493 2344867173588367154519435)
  ·
    refine ⟨3517300760382550731779153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2344867173588367154519435 3517300760382550731779153)
    ·
      refine ⟨2637975570286913048834365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3517300760382550731779153 2637975570286913048834365)
      ·
        refine ⟨989240838857592393312887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2637975570286913048834365 989240838857592393312887)
        ·
          refine ⟨1483861258286388589969331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 989240838857592393312887 1483861258286388589969331)
          ·
            refine ⟨2225791887429582884953997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1483861258286388589969331 2225791887429582884953997)
            ·
              refine ⟨834671957786093581857749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2225791887429582884953997 834671957786093581857749)
              ·
                refine ⟨19562624010611568324791, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 834671957786093581857749 19562624010611568324791)
                ·
                  rfl

theorem cell21_257162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 3, 7].length) (baseStart_257162 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_257162 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_257162 prefixEnd_257162 := by exact prefixLift 257162
  have htrace : WordTrace (prefixWord ++ tailWord_257162) baseStart_257162 baseEnd_257162 := by
    simpa [prefixWord, tailWord_257162, baseEnd_257162] using wordTrace_append hprefix tailTrace_257162
  have hstable : (prefixWord ++ tailWord_257162).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_257162).length < 2 ^ (prefixWord ++ tailWord_257162).sum := by decide
  have hdescent : baseEnd_257162 < baseStart_257162 := by decide
  rcases family_descends (prefixWord ++ tailWord_257162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_257297 : List Nat := [1, 2, 2, 1, 1, 4, 10]
def baseStart_257297 : Nat := 118140960795 + 257297 * 2 ^ 59
def prefixEnd_257297 : Nat := 4983230072969 + 3 ^ 40 * 257297 * 2
def baseEnd_257297 : Nat := 6524297874567163358233

theorem tailTrace_257297 : CollatzResearch.WordTrace tailWord_257297 prefixEnd_257297 6524297874567163358233 := by
  unfold tailWord_257297
  simp only [CollatzResearch.WordTrace]
  refine ⟨9384392548864386674242145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6256261699242924449494763 9384392548864386674242145)
  ·
    refine ⟨7038294411648290005681609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9384392548864386674242145 7038294411648290005681609)
    ·
      refine ⟨5278720808736217504261207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7038294411648290005681609 5278720808736217504261207)
      ·
        refine ⟨7918081213104326256391811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5278720808736217504261207 7918081213104326256391811)
        ·
          refine ⟨11877121819656489384587717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7918081213104326256391811 11877121819656489384587717)
          ·
            refine ⟨2226960341185591759610197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11877121819656489384587717 2226960341185591759610197)
            ·
              refine ⟨6524297874567163358233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 2226960341185591759610197 6524297874567163358233)
              ·
                rfl

theorem cell21_257297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 10].length) (baseStart_257297 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_257297 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_257297 prefixEnd_257297 := by exact prefixLift 257297
  have htrace : WordTrace (prefixWord ++ tailWord_257297) baseStart_257297 baseEnd_257297 := by
    simpa [prefixWord, tailWord_257297, baseEnd_257297] using wordTrace_append hprefix tailTrace_257297
  have hstable : (prefixWord ++ tailWord_257297).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_257297).length < 2 ^ (prefixWord ++ tailWord_257297).sum := by decide
  have hdescent : baseEnd_257297 < baseStart_257297 := by decide
  rcases family_descends (prefixWord ++ tailWord_257297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_257317 : List Nat := [1, 3, 1, 2, 4, 2, 3, 1, 4]
def baseStart_257317 : Nat := 118140960795 + 257317 * 2 ^ 59
def prefixEnd_257317 : Nat := 4983230072969 + 3 ^ 40 * 257317 * 2
def baseEnd_257317 : Nat := 58723245143588879890723

theorem tailTrace_257317 : CollatzResearch.WordTrace tailWord_257317 prefixEnd_257317 58723245143588879890723 := by
  unfold tailWord_257317
  simp only [CollatzResearch.WordTrace]
  refine ⟨9385122008791930089970205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6256748005861286726646803 9385122008791930089970205)
  ·
    refine ⟨3519420753296973783738827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9385122008791930089970205 3519420753296973783738827)
    ·
      refine ⟨5279131129945460675608241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3519420753296973783738827 5279131129945460675608241)
      ·
        refine ⟨3959348347459095506706181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5279131129945460675608241 3959348347459095506706181)
        ·
          refine ⟨742377815148580407507409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3959348347459095506706181 742377815148580407507409)
          ·
            refine ⟨556783361361435305630557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 742377815148580407507409 556783361361435305630557)
            ·
              refine ⟨208793760510538239611459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 556783361361435305630557 208793760510538239611459)
              ·
                refine ⟨313190640765807359417189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 208793760510538239611459 313190640765807359417189)
                ·
                  refine ⟨58723245143588879890723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 313190640765807359417189 58723245143588879890723)
                  ·
                    rfl

theorem cell21_257317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 2, 3, 1, 4].length) (baseStart_257317 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_257317 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_257317 prefixEnd_257317 := by exact prefixLift 257317
  have htrace : WordTrace (prefixWord ++ tailWord_257317) baseStart_257317 baseEnd_257317 := by
    simpa [prefixWord, tailWord_257317, baseEnd_257317] using wordTrace_append hprefix tailTrace_257317
  have hstable : (prefixWord ++ tailWord_257317).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_257317).length < 2 ^ (prefixWord ++ tailWord_257317).sum := by decide
  have hdescent : baseEnd_257317 < baseStart_257317 := by decide
  rcases family_descends (prefixWord ++ tailWord_257317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_257328 : List Nat := [2, 1, 1, 1, 2, 2, 3, 4, 5]
def baseStart_257328 : Nat := 118140960795 + 257328 * 2 ^ 59
def prefixEnd_257328 : Nat := 4983230072969 + 3 ^ 40 * 257328 * 2
def baseEnd_257328 : Nat := 58725755493455305207367

theorem tailTrace_257328 : CollatzResearch.WordTrace tailWord_257328 prefixEnd_257328 58725755493455305207367 := by
  unfold tailWord_257328
  simp only [CollatzResearch.WordTrace]
  refine ⟨4692761605876039484310319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6257015474501385979080425 4692761605876039484310319)
  ·
    refine ⟨7039142408814059226465479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4692761605876039484310319 7039142408814059226465479)
    ·
      refine ⟨10558713613221088839698219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7039142408814059226465479 10558713613221088839698219)
      ·
        refine ⟨15838070419831633259547329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10558713613221088839698219 15838070419831633259547329)
        ·
          refine ⟨11878552814873724944660497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15838070419831633259547329 11878552814873724944660497)
          ·
            refine ⟨8908914611155293708495373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11878552814873724944660497 8908914611155293708495373)
            ·
              refine ⟨3340842979183235140685765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8908914611155293708495373 3340842979183235140685765)
              ·
                refine ⟨626408058596856588878581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3340842979183235140685765 626408058596856588878581)
                ·
                  refine ⟨58725755493455305207367, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 626408058596856588878581 58725755493455305207367)
                  ·
                    rfl

theorem cell21_257328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 3, 4, 5].length) (baseStart_257328 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_257328 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_257328 prefixEnd_257328 := by exact prefixLift 257328
  have htrace : WordTrace (prefixWord ++ tailWord_257328) baseStart_257328 baseEnd_257328 := by
    simpa [prefixWord, tailWord_257328, baseEnd_257328] using wordTrace_append hprefix tailTrace_257328
  have hstable : (prefixWord ++ tailWord_257328).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_257328).length < 2 ^ (prefixWord ++ tailWord_257328).sum := by decide
  have hdescent : baseEnd_257328 < baseStart_257328 := by decide
  rcases family_descends (prefixWord ++ tailWord_257328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_257331 : List Nat := [1, 1, 1, 2, 5, 4, 2, 5]
def baseStart_257331 : Nat := 118140960795 + 257331 * 2 ^ 59
def prefixEnd_257331 : Nat := 4983230072969 + 3 ^ 40 * 257331 * 2
def baseEnd_257331 : Nat := 19575480044775988885787

theorem tailTrace_257331 : CollatzResearch.WordTrace tailWord_257331 prefixEnd_257331 19575480044775988885787 := by
  unfold tailWord_257331
  simp only [CollatzResearch.WordTrace]
  refine ⟨9385632630741210480979847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6257088420494140320653231 9385632630741210480979847)
  ·
    refine ⟨14078448946111815721469771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9385632630741210480979847 14078448946111815721469771)
    ·
      refine ⟨21117673419167723582204657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14078448946111815721469771 21117673419167723582204657)
      ·
        refine ⟨15838255064375792686653493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21117673419167723582204657 15838255064375792686653493)
        ·
          refine ⟨1484836412285230564373765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 15838255064375792686653493 1484836412285230564373765)
          ·
            refine ⟨278406827303480730820081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1484836412285230564373765 278406827303480730820081)
            ·
              refine ⟨208805120477610548115061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 278406827303480730820081 208805120477610548115061)
              ·
                refine ⟨19575480044775988885787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 208805120477610548115061 19575480044775988885787)
                ·
                  rfl

theorem cell21_257331_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 4, 2, 5].length) (baseStart_257331 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_257331 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_257331 prefixEnd_257331 := by exact prefixLift 257331
  have htrace : WordTrace (prefixWord ++ tailWord_257331) baseStart_257331 baseEnd_257331 := by
    simpa [prefixWord, tailWord_257331, baseEnd_257331] using wordTrace_append hprefix tailTrace_257331
  have hstable : (prefixWord ++ tailWord_257331).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_257331).length < 2 ^ (prefixWord ++ tailWord_257331).sum := by decide
  have hdescent : baseEnd_257331 < baseStart_257331 := by decide
  rcases family_descends (prefixWord ++ tailWord_257331) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_257376 : List Nat := [2, 1, 1, 3, 4, 2, 1, 3, 4]
def baseStart_257376 : Nat := 118140960795 + 257376 * 2 ^ 59
def prefixEnd_257376 : Nat := 4983230072969 + 3 ^ 40 * 257376 * 2
def baseEnd_257376 : Nat := 58736709747417888407269

theorem tailTrace_257376 : CollatzResearch.WordTrace tailWord_257376 prefixEnd_257376 58736709747417888407269 := by
  unfold tailWord_257376
  simp only [CollatzResearch.WordTrace]
  refine ⟨4693636957789091583183991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6258182610385455444245321 4693636957789091583183991)
  ·
    refine ⟨7040455436683637374775987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4693636957789091583183991 7040455436683637374775987)
    ·
      refine ⟨10560683155025456062163981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7040455436683637374775987 10560683155025456062163981)
      ·
        refine ⟨3960256183134546023311493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10560683155025456062163981 3960256183134546023311493)
        ·
          refine ⟨742548034337727379370905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3960256183134546023311493 742548034337727379370905)
          ·
            refine ⟨556911025753295534528179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 742548034337727379370905 556911025753295534528179)
            ·
              refine ⟨835366538629943301792269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 556911025753295534528179 835366538629943301792269)
              ·
                refine ⟨313262451986228738172101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 835366538629943301792269 313262451986228738172101)
                ·
                  refine ⟨58736709747417888407269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 313262451986228738172101 58736709747417888407269)
                  ·
                    rfl

theorem cell21_257376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 2, 1, 3, 4].length) (baseStart_257376 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_257376 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_257376 prefixEnd_257376 := by exact prefixLift 257376
  have htrace : WordTrace (prefixWord ++ tailWord_257376) baseStart_257376 baseEnd_257376 := by
    simpa [prefixWord, tailWord_257376, baseEnd_257376] using wordTrace_append hprefix tailTrace_257376
  have hstable : (prefixWord ++ tailWord_257376).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_257376).length < 2 ^ (prefixWord ++ tailWord_257376).sum := by decide
  have hdescent : baseEnd_257376 < baseStart_257376 := by decide
  rcases family_descends (prefixWord ++ tailWord_257376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_257410 : List Nat := [3, 4, 2, 1, 1, 2, 2, 2, 4]
def baseStart_257410 : Nat := 118140960795 + 257410 * 2 ^ 59
def prefixEnd_257410 : Nat := 4983230072969 + 3 ^ 40 * 257410 * 2
def baseEnd_257410 : Nat := 58744469010641384840533

theorem tailTrace_257410 : CollatzResearch.WordTrace tailWord_257410 prefixEnd_257410 58744469010641384840533 := by
  unfold tailWord_257410
  simp only [CollatzResearch.WordTrace]
  refine ⟨2347128499363751743276421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6259009331636671315403789 2347128499363751743276421)
  ·
    refine ⟨440086593630703451864329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2347128499363751743276421 440086593630703451864329)
    ·
      refine ⟨330064945223027588898247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 440086593630703451864329 330064945223027588898247)
      ·
        refine ⟨495097417834541383347371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 330064945223027588898247 495097417834541383347371)
        ·
          refine ⟨742646126751812075021057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 495097417834541383347371 742646126751812075021057)
          ·
            refine ⟨556984595063859056265793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 742646126751812075021057 556984595063859056265793)
            ·
              refine ⟨417738446297894292199345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 556984595063859056265793 417738446297894292199345)
              ·
                refine ⟨313303834723420719149509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 417738446297894292199345 313303834723420719149509)
                ·
                  refine ⟨58744469010641384840533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 313303834723420719149509 58744469010641384840533)
                  ·
                    rfl

theorem cell21_257410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 2, 2, 2, 4].length) (baseStart_257410 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_257410 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_257410 prefixEnd_257410 := by exact prefixLift 257410
  have htrace : WordTrace (prefixWord ++ tailWord_257410) baseStart_257410 baseEnd_257410 := by
    simpa [prefixWord, tailWord_257410, baseEnd_257410] using wordTrace_append hprefix tailTrace_257410
  have hstable : (prefixWord ++ tailWord_257410).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_257410).length < 2 ^ (prefixWord ++ tailWord_257410).sum := by decide
  have hdescent : baseEnd_257410 < baseStart_257410 := by decide
  rcases family_descends (prefixWord ++ tailWord_257410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_257511 : List Nat := [1, 1, 5, 2, 1, 2, 1, 2, 6]
def baseStart_257511 : Nat := 118140960795 + 257511 * 2 ^ 59
def prefixEnd_257511 : Nat := 4983230072969 + 3 ^ 40 * 257511 * 2
def baseEnd_257511 : Nat := 58767518586687653656993

theorem tailTrace_257511 : CollatzResearch.WordTrace tailWord_257511 prefixEnd_257511 58767518586687653656993 := by
  unfold tailWord_257511
  simp only [CollatzResearch.WordTrace]
  refine ⟨9392197770089101222532387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6261465180059400815021591 9392197770089101222532387)
  ·
    refine ⟨14088296655133651833798581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9392197770089101222532387 14088296655133651833798581)
    ·
      refine ⟨1320777811418779859418617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 14088296655133651833798581 1320777811418779859418617)
      ·
        refine ⟨990583358564084894563963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1320777811418779859418617 990583358564084894563963)
        ·
          refine ⟨1485875037846127341845945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 990583358564084894563963 1485875037846127341845945)
          ·
            refine ⟨1114406278384595506384459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1485875037846127341845945 1114406278384595506384459)
            ·
              refine ⟨1671609417576893259576689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1114406278384595506384459 1671609417576893259576689)
              ·
                refine ⟨1253707063182669944682517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1671609417576893259576689 1253707063182669944682517)
                ·
                  refine ⟨58767518586687653656993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1253707063182669944682517 58767518586687653656993)
                  ·
                    rfl

theorem cell21_257511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 1, 2, 6].length) (baseStart_257511 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_257511 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_257511 prefixEnd_257511 := by exact prefixLift 257511
  have htrace : WordTrace (prefixWord ++ tailWord_257511) baseStart_257511 baseEnd_257511 := by
    simpa [prefixWord, tailWord_257511, baseEnd_257511] using wordTrace_append hprefix tailTrace_257511
  have hstable : (prefixWord ++ tailWord_257511).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_257511).length < 2 ^ (prefixWord ++ tailWord_257511).sum := by decide
  have hdescent : baseEnd_257511 < baseStart_257511 := by decide
  rcases family_descends (prefixWord ++ tailWord_257511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_257573 : List Nat := [1, 3, 1, 2, 2, 1, 1, 7, 3]
def baseStart_257573 : Nat := 118140960795 + 257573 * 2 ^ 59
def prefixEnd_257573 : Nat := 4983230072969 + 3 ^ 40 * 257573 * 2
def baseEnd_257573 : Nat := 58781667831389323623533

theorem tailTrace_257573 : CollatzResearch.WordTrace tailWord_257573 prefixEnd_257573 58781667831389323623533 := by
  unfold tailWord_257573
  simp only [CollatzResearch.WordTrace]
  refine ⟨9394459095864485811289373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6262972730576323874192915 9394459095864485811289373)
  ·
    refine ⟨3522922160949182179233515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9394459095864485811289373 3522922160949182179233515)
    ·
      refine ⟨5284383241423773268850273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3522922160949182179233515 5284383241423773268850273)
      ·
        refine ⟨3963287431067829951637705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5284383241423773268850273 3963287431067829951637705)
        ·
          refine ⟨2972465573300872463728279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3963287431067829951637705 2972465573300872463728279)
          ·
            refine ⟨4458698359951308695592419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2972465573300872463728279 4458698359951308695592419)
            ·
              refine ⟨6688047539926963043388629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4458698359951308695592419 6688047539926963043388629)
              ·
                refine ⟨156751114217038196329421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6688047539926963043388629 156751114217038196329421)
                ·
                  refine ⟨58781667831389323623533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 156751114217038196329421 58781667831389323623533)
                  ·
                    rfl

theorem cell21_257573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 1, 7, 3].length) (baseStart_257573 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_257573 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_257573 prefixEnd_257573 := by exact prefixLift 257573
  have htrace : WordTrace (prefixWord ++ tailWord_257573) baseStart_257573 baseEnd_257573 := by
    simpa [prefixWord, tailWord_257573, baseEnd_257573] using wordTrace_append hprefix tailTrace_257573
  have hstable : (prefixWord ++ tailWord_257573).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_257573).length < 2 ^ (prefixWord ++ tailWord_257573).sum := by decide
  have hdescent : baseEnd_257573 < baseStart_257573 := by decide
  rcases family_descends (prefixWord ++ tailWord_257573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_257587 : List Nat := [1, 1, 1, 2, 4, 3, 1, 4, 4]
def baseStart_257587 : Nat := 118140960795 + 257587 * 2 ^ 59
def prefixEnd_257587 : Nat := 4983230072969 + 3 ^ 40 * 257587 * 2
def baseEnd_257587 : Nat := 58784862822128410390171

theorem tailTrace_257587 : CollatzResearch.WordTrace tailWord_257587 prefixEnd_257587 58784862822128410390171 := by
  unfold tailWord_257587
  simp only [CollatzResearch.WordTrace]
  refine ⟨9394969717813766202299015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6263313145209177468199343 9394969717813766202299015)
  ·
    refine ⟨14092454576720649303448523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9394969717813766202299015 14092454576720649303448523)
    ·
      refine ⟨21138681865080973955172785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14092454576720649303448523 21138681865080973955172785)
      ·
        refine ⟨15854011398810730466379589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21138681865080973955172785 15854011398810730466379589)
        ·
          refine ⟨2972627137277011962446173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15854011398810730466379589 2972627137277011962446173)
          ·
            refine ⟨1114735176478879485917315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2972627137277011962446173 1114735176478879485917315)
            ·
              refine ⟨1672102764718319228875973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1114735176478879485917315 1672102764718319228875973)
              ·
                refine ⟨313519268384684855414245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1672102764718319228875973 313519268384684855414245)
                ·
                  refine ⟨58784862822128410390171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 313519268384684855414245 58784862822128410390171)
                  ·
                    rfl

theorem cell21_257587_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 1, 4, 4].length) (baseStart_257587 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_257587 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_257587 prefixEnd_257587 := by exact prefixLift 257587
  have htrace : WordTrace (prefixWord ++ tailWord_257587) baseStart_257587 baseEnd_257587 := by
    simpa [prefixWord, tailWord_257587, baseEnd_257587] using wordTrace_append hprefix tailTrace_257587
  have hstable : (prefixWord ++ tailWord_257587).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_257587).length < 2 ^ (prefixWord ++ tailWord_257587).sum := by decide
  have hdescent : baseEnd_257587 < baseStart_257587 := by decide
  rcases family_descends (prefixWord ++ tailWord_257587) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_257694 : List Nat := [4, 3, 1, 1, 1, 2, 9]
def baseStart_257694 : Nat := 118140960795 + 257694 * 2 ^ 59
def prefixEnd_257694 : Nat := 4983230072969 + 3 ^ 40 * 257694 * 2
def baseEnd_257694 : Nat := 6534364631102222456291

theorem tailTrace_257694 : CollatzResearch.WordTrace tailWord_257694 prefixEnd_257694 6534364631102222456291 := by
  unfold tailWord_257694
  simp only [CollatzResearch.WordTrace]
  refine ⟨1174859041053265434555517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 6265914885617415650962757 1174859041053265434555517)
  ·
    refine ⟨440572140394974537958319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1174859041053265434555517 440572140394974537958319)
    ·
      refine ⟨660858210592461806937479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 440572140394974537958319 660858210592461806937479)
      ·
        refine ⟨991287315888692710406219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 660858210592461806937479 991287315888692710406219)
        ·
          refine ⟨1486930973833039065609329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 991287315888692710406219 1486930973833039065609329)
          ·
            refine ⟨1115198230374779299206997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1486930973833039065609329 1115198230374779299206997)
            ·
              refine ⟨6534364631102222456291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 1115198230374779299206997 6534364631102222456291)
              ·
                rfl

theorem cell21_257694_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 9].length) (baseStart_257694 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_257694 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_257694 prefixEnd_257694 := by exact prefixLift 257694
  have htrace : WordTrace (prefixWord ++ tailWord_257694) baseStart_257694 baseEnd_257694 := by
    simpa [prefixWord, tailWord_257694, baseEnd_257694] using wordTrace_append hprefix tailTrace_257694
  have hstable : (prefixWord ++ tailWord_257694).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_257694).length < 2 ^ (prefixWord ++ tailWord_257694).sum := by decide
  have hdescent : baseEnd_257694 < baseStart_257694 := by decide
  rcases family_descends (prefixWord ++ tailWord_257694) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_257815 : List Nat := [1, 1, 3, 4, 2, 2, 1, 1, 6]
def baseStart_257815 : Nat := 118140960795 + 257815 * 2 ^ 59
def prefixEnd_257815 : Nat := 4983230072969 + 3 ^ 40 * 257815 * 2
def baseEnd_257815 : Nat := 58836895528450680589705

theorem tailTrace_257815 : CollatzResearch.WordTrace tailWord_257815 prefixEnd_257815 58836895528450680589705 := by
  unfold tailWord_257815
  simp only [CollatzResearch.WordTrace]
  refine ⟨9403285560987761141598899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6268857040658507427732599 9403285560987761141598899)
  ·
    refine ⟨14104928341481641712398349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9403285560987761141598899 14104928341481641712398349)
    ·
      refine ⟨5289348128055615642149381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14104928341481641712398349 5289348128055615642149381)
      ·
        refine ⟨991752774010427932903009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5289348128055615642149381 991752774010427932903009)
        ·
          refine ⟨743814580507820949677257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 991752774010427932903009 743814580507820949677257)
          ·
            refine ⟨557860935380865712257943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 743814580507820949677257 557860935380865712257943)
            ·
              refine ⟨836791403071298568386915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 557860935380865712257943 836791403071298568386915)
              ·
                refine ⟨1255187104606947852580373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 836791403071298568386915 1255187104606947852580373)
                ·
                  refine ⟨58836895528450680589705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1255187104606947852580373 58836895528450680589705)
                  ·
                    rfl

theorem cell21_257815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 2, 1, 1, 6].length) (baseStart_257815 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_257815 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_257815 prefixEnd_257815 := by exact prefixLift 257815
  have htrace : WordTrace (prefixWord ++ tailWord_257815) baseStart_257815 baseEnd_257815 := by
    simpa [prefixWord, tailWord_257815, baseEnd_257815] using wordTrace_append hprefix tailTrace_257815
  have hstable : (prefixWord ++ tailWord_257815).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_257815).length < 2 ^ (prefixWord ++ tailWord_257815).sum := by decide
  have hdescent : baseEnd_257815 < baseStart_257815 := by decide
  rcases family_descends (prefixWord ++ tailWord_257815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_257877 : List Nat := [1, 3, 2, 2, 2, 4, 1, 1, 5]
def baseStart_257877 : Nat := 118140960795 + 257877 * 2 ^ 59
def prefixEnd_257877 : Nat := 4983230072969 + 3 ^ 40 * 257877 * 2
def baseEnd_257877 : Nat := 58851044773152350556245

theorem tailTrace_257877 : CollatzResearch.WordTrace tailWord_257877 prefixEnd_257877 58851044773152350556245 := by
  unfold tailWord_257877
  simp only [CollatzResearch.WordTrace]
  refine ⟨9405546886763145730355885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6270364591175430486903923 9405546886763145730355885)
  ·
    refine ⟨3527080082536179648883457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9405546886763145730355885 3527080082536179648883457)
    ·
      refine ⟨2645310061902134736662593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3527080082536179648883457 2645310061902134736662593)
      ·
        refine ⟨1983982546426601052496945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2645310061902134736662593 1983982546426601052496945)
        ·
          refine ⟨1487986909819950789372709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1983982546426601052496945 1487986909819950789372709)
          ·
            refine ⟨278997545591240773007383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1487986909819950789372709 278997545591240773007383)
            ·
              refine ⟨418496318386861159511075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 278997545591240773007383 418496318386861159511075)
              ·
                refine ⟨627744477580291739266613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 418496318386861159511075 627744477580291739266613)
                ·
                  refine ⟨58851044773152350556245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 627744477580291739266613 58851044773152350556245)
                  ·
                    rfl

theorem cell21_257877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 4, 1, 1, 5].length) (baseStart_257877 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_257877 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_257877 prefixEnd_257877 := by exact prefixLift 257877
  have htrace : WordTrace (prefixWord ++ tailWord_257877) baseStart_257877 baseEnd_257877 := by
    simpa [prefixWord, tailWord_257877, baseEnd_257877] using wordTrace_append hprefix tailTrace_257877
  have hstable : (prefixWord ++ tailWord_257877).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_257877).length < 2 ^ (prefixWord ++ tailWord_257877).sum := by decide
  have hdescent : baseEnd_257877 < baseStart_257877 := by decide
  rcases family_descends (prefixWord ++ tailWord_257877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_257928 : List Nat := [2, 1, 3, 3, 4, 1, 2, 2, 3]
def baseStart_257928 : Nat := 118140960795 + 257928 * 2 ^ 59
def prefixEnd_257928 : Nat := 4983230072969 + 3 ^ 40 * 257928 * 2
def baseEnd_257928 : Nat := 58862683667987595206141

theorem tailTrace_257928 : CollatzResearch.WordTrace tailWord_257928 prefixEnd_257928 58862683667987595206141 := by
  unfold tailWord_257928
  simp only [CollatzResearch.WordTrace]
  refine ⟨4703703504789190720231219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6271604673052254293641625 4703703504789190720231219)
  ·
    refine ⟨7055555257183786080346829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4703703504789190720231219 7055555257183786080346829)
    ·
      refine ⟨2645833221443919780130061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7055555257183786080346829 2645833221443919780130061)
      ·
        refine ⟨992187458041469917548773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2645833221443919780130061 992187458041469917548773)
        ·
          refine ⟨186035148382775609540395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 992187458041469917548773 186035148382775609540395)
          ·
            refine ⟨279052722574163414310593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 186035148382775609540395 279052722574163414310593)
            ·
              refine ⟨209289541930622560732945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 279052722574163414310593 209289541930622560732945)
              ·
                refine ⟨156967156447966920549709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 209289541930622560732945 156967156447966920549709)
                ·
                  refine ⟨58862683667987595206141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 156967156447966920549709 58862683667987595206141)
                  ·
                    rfl

theorem cell21_257928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 4, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 4, 1, 2, 2, 3].length) (baseStart_257928 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_257928 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_257928 prefixEnd_257928 := by exact prefixLift 257928
  have htrace : WordTrace (prefixWord ++ tailWord_257928) baseStart_257928 baseEnd_257928 := by
    simpa [prefixWord, tailWord_257928, baseEnd_257928] using wordTrace_append hprefix tailTrace_257928
  have hstable : (prefixWord ++ tailWord_257928).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_257928).length < 2 ^ (prefixWord ++ tailWord_257928).sum := by decide
  have hdescent : baseEnd_257928 < baseStart_257928 := by decide
  rcases family_descends (prefixWord ++ tailWord_257928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_257953 : List Nat := [1, 2, 3, 4, 2, 1, 1, 2, 5]
def baseStart_257953 : Nat := 118140960795 + 257953 * 2 ^ 59
def prefixEnd_257953 : Nat := 4983230072969 + 3 ^ 40 * 257953 * 2
def baseEnd_257953 : Nat := 58868389008593107289423

theorem tailTrace_257953 : CollatzResearch.WordTrace tailWord_257953 prefixEnd_257953 58868389008593107289423 := by
  unfold tailWord_257953
  simp only [CollatzResearch.WordTrace]
  refine ⟨9408318834487810710122513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6272212556325207140081675 9408318834487810710122513)
  ·
    refine ⟨7056239125865858032591885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9408318834487810710122513 7056239125865858032591885)
    ·
      refine ⟨2646089672199696762221957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7056239125865858032591885 2646089672199696762221957)
      ·
        refine ⟨496141813537443142916617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2646089672199696762221957 496141813537443142916617)
        ·
          refine ⟨372106360153082357187463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 496141813537443142916617 372106360153082357187463)
          ·
            refine ⟨558159540229623535781195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 372106360153082357187463 558159540229623535781195)
            ·
              refine ⟨837239310344435303671793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 558159540229623535781195 837239310344435303671793)
              ·
                refine ⟨627929482758326477753845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 837239310344435303671793 627929482758326477753845)
                ·
                  refine ⟨58868389008593107289423, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 627929482758326477753845 58868389008593107289423)
                  ·
                    rfl

theorem cell21_257953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 2, 1, 1, 2, 5].length) (baseStart_257953 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_257953 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_257953 prefixEnd_257953 := by exact prefixLift 257953
  have htrace : WordTrace (prefixWord ++ tailWord_257953) baseStart_257953 baseEnd_257953 := by
    simpa [prefixWord, tailWord_257953, baseEnd_257953] using wordTrace_append hprefix tailTrace_257953
  have hstable : (prefixWord ++ tailWord_257953).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_257953).length < 2 ^ (prefixWord ++ tailWord_257953).sum := by decide
  have hdescent : baseEnd_257953 < baseStart_257953 := by decide
  rcases family_descends (prefixWord ++ tailWord_257953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_257981 : List Nat := [1, 4, 1, 2, 3, 2, 8]
def baseStart_257981 : Nat := 118140960795 + 257981 * 2 ^ 59
def prefixEnd_257981 : Nat := 4983230072969 + 3 ^ 40 * 257981 * 2
def baseEnd_257981 : Nat := 6541642110007920091411

theorem tailTrace_257981 : CollatzResearch.WordTrace tailWord_257981 prefixEnd_257981 6541642110007920091411 := by
  unfold tailWord_257981
  simp only [CollatzResearch.WordTrace]
  refine ⟨9409340078386371492141797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6272893385590914328094531 9409340078386371492141797)
  ·
    refine ⟨1764251264697444654776587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 9409340078386371492141797 1764251264697444654776587)
    ·
      refine ⟨2646376897046166982164881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1764251264697444654776587 2646376897046166982164881)
      ·
        refine ⟨1984782672784625236623661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2646376897046166982164881 1984782672784625236623661)
        ·
          refine ⟨744293502294234463733873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1984782672784625236623661 744293502294234463733873)
          ·
            refine ⟨558220126720675847800405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 744293502294234463733873 558220126720675847800405)
            ·
              refine ⟨6541642110007920091411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 558220126720675847800405 6541642110007920091411)
              ·
                rfl

theorem cell21_257981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 2, 8].length) (baseStart_257981 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_257981 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_257981 prefixEnd_257981 := by exact prefixLift 257981
  have htrace : WordTrace (prefixWord ++ tailWord_257981) baseStart_257981 baseEnd_257981 := by
    simpa [prefixWord, tailWord_257981, baseEnd_257981] using wordTrace_append hprefix tailTrace_257981
  have hstable : (prefixWord ++ tailWord_257981).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_257981).length < 2 ^ (prefixWord ++ tailWord_257981).sum := by decide
  have hdescent : baseEnd_257981 < baseStart_257981 := by decide
  rcases family_descends (prefixWord ++ tailWord_257981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_258026 : List Nat := [3, 1, 3, 1, 2, 1, 1, 1, 8]
def baseStart_258026 : Nat := 118140960795 + 258026 * 2 ^ 59
def prefixEnd_258026 : Nat := 4983230072969 + 3 ^ 40 * 258026 * 2
def baseEnd_258026 : Nat := 58885048603161202572607

theorem tailTrace_258026 : CollatzResearch.WordTrace tailWord_258026 prefixEnd_258026 58885048603161202572607 := by
  unfold tailWord_258026
  simp only [CollatzResearch.WordTrace]
  refine ⟨2352745340805836044382483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6273987575482229451686621 2352745340805836044382483)
  ·
    refine ⟨3529118011208754066573725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2352745340805836044382483 3529118011208754066573725)
    ·
      refine ⟨1323419254203282774965147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3529118011208754066573725 1323419254203282774965147)
      ·
        refine ⟨1985128881304924162447721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1323419254203282774965147 1985128881304924162447721)
        ·
          refine ⟨1488846660978693121835791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1985128881304924162447721 1488846660978693121835791)
          ·
            refine ⟨2233269991468039682753687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1488846660978693121835791 2233269991468039682753687)
            ·
              refine ⟨3349904987202059524130531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2233269991468039682753687 3349904987202059524130531)
              ·
                refine ⟨5024857480803089286195797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3349904987202059524130531 5024857480803089286195797)
                ·
                  refine ⟨58885048603161202572607, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 5024857480803089286195797 58885048603161202572607)
                  ·
                    rfl

theorem cell21_258026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 1, 1, 8].length) (baseStart_258026 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_258026 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_258026 prefixEnd_258026 := by exact prefixLift 258026
  have htrace : WordTrace (prefixWord ++ tailWord_258026) baseStart_258026 baseEnd_258026 := by
    simpa [prefixWord, tailWord_258026, baseEnd_258026] using wordTrace_append hprefix tailTrace_258026
  have hstable : (prefixWord ++ tailWord_258026).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_258026).length < 2 ^ (prefixWord ++ tailWord_258026).sum := by decide
  have hdescent : baseEnd_258026 < baseStart_258026 := by decide
  rcases family_descends (prefixWord ++ tailWord_258026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_258040 : List Nat := [2, 1, 2, 1, 1, 3, 11]
def baseStart_258040 : Nat := 118140960795 + 258040 * 2 ^ 59
def prefixEnd_258040 : Nat := 4983230072969 + 3 ^ 40 * 258040 * 2
def baseEnd_258040 : Nat := 6543138177100032148805

theorem tailTrace_258040 : CollatzResearch.WordTrace tailWord_258040 prefixEnd_258040 6543138177100032148805 := by
  unfold tailWord_258040
  simp only [CollatzResearch.WordTrace]
  refine ⟨4705745992586312284269787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6274327990115083045693049 4705745992586312284269787)
  ·
    refine ⟨7058618988879468426404681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4705745992586312284269787 7058618988879468426404681)
    ·
      refine ⟨5293964241659601319803511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7058618988879468426404681 5293964241659601319803511)
      ·
        refine ⟨7940946362489401979705267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5293964241659601319803511 7940946362489401979705267)
        ·
          refine ⟨11911419543734102969557901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7940946362489401979705267 11911419543734102969557901)
          ·
            refine ⟨4466782328900288613584213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11911419543734102969557901 4466782328900288613584213)
            ·
              refine ⟨6543138177100032148805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 4466782328900288613584213 6543138177100032148805)
              ·
                rfl

theorem cell21_258040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 11].length) (baseStart_258040 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_258040 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_258040 prefixEnd_258040 := by exact prefixLift 258040
  have htrace : WordTrace (prefixWord ++ tailWord_258040) baseStart_258040 baseEnd_258040 := by
    simpa [prefixWord, tailWord_258040, baseEnd_258040] using wordTrace_append hprefix tailTrace_258040
  have hstable : (prefixWord ++ tailWord_258040).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_258040).length < 2 ^ (prefixWord ++ tailWord_258040).sum := by decide
  have hdescent : baseEnd_258040 < baseStart_258040 := by decide
  rcases family_descends (prefixWord ++ tailWord_258040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_258046 : List Nat := [4, 2, 2, 2, 1, 3, 1, 1, 5]
def baseStart_258046 : Nat := 118140960795 + 258046 * 2 ^ 59
def prefixEnd_258046 : Nat := 4983230072969 + 3 ^ 40 * 258046 * 2
def baseEnd_258046 : Nat := 58889612875645612239233

theorem tailTrace_258046 : CollatzResearch.WordTrace tailWord_258046 prefixEnd_258046 58889612875645612239233 := by
  unfold tailWord_258046
  simp only [CollatzResearch.WordTrace]
  refine ⟨1176463852893860949157249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 6274473882100591728838661 1176463852893860949157249)
  ·
    refine ⟨882347889670395711867937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1176463852893860949157249 882347889670395711867937)
    ·
      refine ⟨661760917252796783900953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 882347889670395711867937 661760917252796783900953)
      ·
        refine ⟨496320687939597587925715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 661760917252796783900953 496320687939597587925715)
        ·
          refine ⟨744481031909396381888573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 496320687939597587925715 744481031909396381888573)
          ·
            refine ⟨279180386966023643208215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 744481031909396381888573 279180386966023643208215)
            ·
              refine ⟨418770580449035464812323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 279180386966023643208215 418770580449035464812323)
              ·
                refine ⟨628155870673553197218485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 418770580449035464812323 628155870673553197218485)
                ·
                  refine ⟨58889612875645612239233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 628155870673553197218485 58889612875645612239233)
                  ·
                    rfl

theorem cell21_258046_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 3, 1, 1, 5].length) (baseStart_258046 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_258046 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_258046 prefixEnd_258046 := by exact prefixLift 258046
  have htrace : WordTrace (prefixWord ++ tailWord_258046) baseStart_258046 baseEnd_258046 := by
    simpa [prefixWord, tailWord_258046, baseEnd_258046] using wordTrace_append hprefix tailTrace_258046
  have hstable : (prefixWord ++ tailWord_258046).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_258046).length < 2 ^ (prefixWord ++ tailWord_258046).sum := by decide
  have hdescent : baseEnd_258046 < baseStart_258046 := by decide
  rcases family_descends (prefixWord ++ tailWord_258046) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_258192 : List Nat := [2, 1, 1, 1, 1, 1, 7, 7]
def baseStart_258192 : Nat := 118140960795 + 258192 * 2 ^ 59
def prefixEnd_258192 : Nat := 4983230072969 + 3 ^ 40 * 258192 * 2
def baseEnd_258192 : Nat := 19640977354927267601867

theorem tailTrace_258192 : CollatzResearch.WordTrace tailWord_258192 prefixEnd_258192 19640977354927267601867 := by
  unfold tailWord_258192
  simp only [CollatzResearch.WordTrace]
  refine ⟨4708517940310977264036415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6278023920414636352048553 4708517940310977264036415)
  ·
    refine ⟨7062776910466465896054623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4708517940310977264036415 7062776910466465896054623)
    ·
      refine ⟨10594165365699698844081935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7062776910466465896054623 10594165365699698844081935)
      ·
        refine ⟨15891248048549548266122903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10594165365699698844081935 15891248048549548266122903)
        ·
          refine ⟨23836872072824322399184355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15891248048549548266122903 23836872072824322399184355)
          ·
            refine ⟨35755308109236483598776533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23836872072824322399184355 35755308109236483598776533)
            ·
              refine ⟨838015033810230084346325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 35755308109236483598776533 838015033810230084346325)
              ·
                refine ⟨19640977354927267601867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 838015033810230084346325 19640977354927267601867)
                ·
                  rfl

theorem cell21_258192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 7, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 7, 7].length) (baseStart_258192 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_258192 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_258192 prefixEnd_258192 := by exact prefixLift 258192
  have htrace : WordTrace (prefixWord ++ tailWord_258192) baseStart_258192 baseEnd_258192 := by
    simpa [prefixWord, tailWord_258192, baseEnd_258192] using wordTrace_append hprefix tailTrace_258192
  have hstable : (prefixWord ++ tailWord_258192).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_258192).length < 2 ^ (prefixWord ++ tailWord_258192).sum := by decide
  have hdescent : baseEnd_258192 < baseStart_258192 := by decide
  rcases family_descends (prefixWord ++ tailWord_258192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_258209 : List Nat := [1, 2, 3, 3, 1, 4, 7]
def baseStart_258209 : Nat := 118140960795 + 258209 * 2 ^ 59
def prefixEnd_258209 : Nat := 4983230072969 + 3 ^ 40 * 258209 * 2
def baseEnd_258209 : Nat := 6547423521821505669137

theorem tailTrace_258209 : CollatzResearch.WordTrace tailWord_258209 prefixEnd_258209 6547423521821505669137 := by
  unfold tailWord_258209
  simp only [CollatzResearch.WordTrace]
  refine ⟨9417655921560366431441681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6278437281040244287627787 9417655921560366431441681)
  ·
    refine ⟨7063241941170274823581261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9417655921560366431441681 7063241941170274823581261)
    ·
      refine ⟨2648715727938853058842973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7063241941170274823581261 2648715727938853058842973)
      ·
        refine ⟨993268397977069897066115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2648715727938853058842973 993268397977069897066115)
        ·
          refine ⟨1489902596965604845599173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 993268397977069897066115 1489902596965604845599173)
          ·
            refine ⟨279356736931050908549845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1489902596965604845599173 279356736931050908549845)
            ·
              refine ⟨6547423521821505669137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 279356736931050908549845 6547423521821505669137)
              ·
                rfl

theorem cell21_258209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 4, 7].length) (baseStart_258209 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_258209 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_258209 prefixEnd_258209 := by exact prefixLift 258209
  have htrace : WordTrace (prefixWord ++ tailWord_258209) baseStart_258209 baseEnd_258209 := by
    simpa [prefixWord, tailWord_258209, baseEnd_258209] using wordTrace_append hprefix tailTrace_258209
  have hstable : (prefixWord ++ tailWord_258209).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_258209).length < 2 ^ (prefixWord ++ tailWord_258209).sum := by decide
  have hdescent : baseEnd_258209 < baseStart_258209 := by decide
  rcases family_descends (prefixWord ++ tailWord_258209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_258215 : List Nat := [1, 1, 6, 2, 2, 1, 3, 2, 3]
def baseStart_258215 : Nat := 118140960795 + 258215 * 2 ^ 59
def prefixEnd_258215 : Nat := 4983230072969 + 3 ^ 40 * 258215 * 2
def baseEnd_258215 : Nat := 58928180978138873922221

theorem tailTrace_258215 : CollatzResearch.WordTrace tailWord_258215 prefixEnd_258215 58928180978138873922221 := by
  unfold tailWord_258215
  simp only [CollatzResearch.WordTrace]
  refine ⟨9417874759538629456160099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6278583173025752970773399 9417874759538629456160099)
  ·
    refine ⟨14126812139307944184240149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9417874759538629456160099 14126812139307944184240149)
    ·
      refine ⟨662194319030059883636257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 14126812139307944184240149 662194319030059883636257)
      ·
        refine ⟨496645739272544912727193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 662194319030059883636257 496645739272544912727193)
        ·
          refine ⟨372484304454408684545395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 496645739272544912727193 372484304454408684545395)
          ·
            refine ⟨558726456681613026818093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 372484304454408684545395 558726456681613026818093)
            ·
              refine ⟨209522421255604885056785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 558726456681613026818093 209522421255604885056785)
              ·
                refine ⟨157141815941703663792589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 209522421255604885056785 157141815941703663792589)
                ·
                  refine ⟨58928180978138873922221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 157141815941703663792589 58928180978138873922221)
                  ·
                    rfl

theorem cell21_258215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 2, 1, 3, 2, 3].length) (baseStart_258215 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_258215 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_258215 prefixEnd_258215 := by exact prefixLift 258215
  have htrace : WordTrace (prefixWord ++ tailWord_258215) baseStart_258215 baseEnd_258215 := by
    simpa [prefixWord, tailWord_258215, baseEnd_258215] using wordTrace_append hprefix tailTrace_258215
  have hstable : (prefixWord ++ tailWord_258215).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_258215).length < 2 ^ (prefixWord ++ tailWord_258215).sum := by decide
  have hdescent : baseEnd_258215 < baseStart_258215 := by decide
  rcases family_descends (prefixWord ++ tailWord_258215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_258302 : List Nat := [4, 2, 2, 1, 1, 1, 5, 5]
def baseStart_258302 : Nat := 118140960795 + 258302 * 2 ^ 59
def prefixEnd_258302 : Nat := 4983230072969 + 3 ^ 40 * 258302 * 2
def baseEnd_258302 : Nat := 19649345187815351990681

theorem tailTrace_258302 : CollatzResearch.WordTrace tailWord_258302 prefixEnd_258302 19649345187815351990681 := by
  unfold tailWord_258302
  simp only [CollatzResearch.WordTrace]
  refine ⟨1177630988777930414322145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 6280698606815628876384773 1177630988777930414322145)
  ·
    refine ⟨883223241583447810741609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1177630988777930414322145 883223241583447810741609)
    ·
      refine ⟨662417431187585858056207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 883223241583447810741609 662417431187585858056207)
      ·
        refine ⟨993626146781378787084311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 662417431187585858056207 993626146781378787084311)
        ·
          refine ⟨1490439220172068180626467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 993626146781378787084311 1490439220172068180626467)
          ·
            refine ⟨2235658830258102270939701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1490439220172068180626467 2235658830258102270939701)
            ·
              refine ⟨209593015336697087900597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 2235658830258102270939701 209593015336697087900597)
              ·
                refine ⟨19649345187815351990681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 209593015336697087900597 19649345187815351990681)
                ·
                  rfl

theorem cell21_258302_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 5, 5].length) (baseStart_258302 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_258302 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_258302 prefixEnd_258302 := by exact prefixLift 258302
  have htrace : WordTrace (prefixWord ++ tailWord_258302) baseStart_258302 baseEnd_258302 := by
    simpa [prefixWord, tailWord_258302, baseEnd_258302] using wordTrace_append hprefix tailTrace_258302
  have hstable : (prefixWord ++ tailWord_258302).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_258302).length < 2 ^ (prefixWord ++ tailWord_258302).sum := by decide
  have hdescent : baseEnd_258302 < baseStart_258302 := by decide
  rcases family_descends (prefixWord ++ tailWord_258302) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_258333 : List Nat := [1, 4, 2, 3, 2, 1, 2, 1, 5]
def baseStart_258333 : Nat := 118140960795 + 258333 * 2 ^ 59
def prefixEnd_258333 : Nat := 4983230072969 + 3 ^ 40 * 258333 * 2
def baseEnd_258333 : Nat := 58955110185796890955313

theorem tailTrace_258333 : CollatzResearch.WordTrace tailWord_258333 prefixEnd_258333 58955110185796890955313 := by
  unfold tailWord_258333
  simp only [CollatzResearch.WordTrace]
  refine ⟨9422178573111135608955653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6281452382074090405970435 9422178573111135608955653)
  ·
    refine ⟨1766658482458337926679185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 9422178573111135608955653 1766658482458337926679185)
    ·
      refine ⟨1324993861843753445009389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1766658482458337926679185 1324993861843753445009389)
      ·
        refine ⟨496872698191407541878521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1324993861843753445009389 496872698191407541878521)
        ·
          refine ⟨372654523643555656408891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 496872698191407541878521 372654523643555656408891)
          ·
            refine ⟨558981785465333484613337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 372654523643555656408891 558981785465333484613337)
            ·
              refine ⟨419236339099000113460003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 558981785465333484613337 419236339099000113460003)
              ·
                refine ⟨628854508648500170190005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 419236339099000113460003 628854508648500170190005)
                ·
                  refine ⟨58955110185796890955313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 628854508648500170190005 58955110185796890955313)
                  ·
                    rfl

theorem cell21_258333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 2, 1, 2, 1, 5].length) (baseStart_258333 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_258333 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_258333 prefixEnd_258333 := by exact prefixLift 258333
  have htrace : WordTrace (prefixWord ++ tailWord_258333) baseStart_258333 baseEnd_258333 := by
    simpa [prefixWord, tailWord_258333, baseEnd_258333] using wordTrace_append hprefix tailTrace_258333
  have hstable : (prefixWord ++ tailWord_258333).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_258333).length < 2 ^ (prefixWord ++ tailWord_258333).sum := by decide
  have hdescent : baseEnd_258333 < baseStart_258333 := by decide
  rcases family_descends (prefixWord ++ tailWord_258333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_258361 : List Nat := [1, 2, 1, 6, 1, 2, 1, 7]
def baseStart_258361 : Nat := 118140960795 + 258361 * 2 ^ 59
def prefixEnd_258361 : Nat := 4983230072969 + 3 ^ 40 * 258361 * 2
def baseEnd_258361 : Nat := 19653833389091688162863

theorem tailTrace_258361 : CollatzResearch.WordTrace tailWord_258361 prefixEnd_258361 19653833389091688162863 := by
  unfold tailWord_258361
  simp only [CollatzResearch.WordTrace]
  refine ⟨9423199817009696390974937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6282133211339797593983291 9423199817009696390974937)
  ·
    refine ⟨7067399862757272293231203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9423199817009696390974937 7067399862757272293231203)
    ·
      refine ⟨10601099794135908439846805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7067399862757272293231203 10601099794135908439846805)
      ·
        refine ⟨496926552850120708117819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 10601099794135908439846805 496926552850120708117819)
        ·
          refine ⟨745389829275181062176729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 496926552850120708117819 745389829275181062176729)
          ·
            refine ⟨559042371956385796632547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 745389829275181062176729 559042371956385796632547)
            ·
              refine ⟨838563557934578694948821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 559042371956385796632547 838563557934578694948821)
              ·
                refine ⟨19653833389091688162863, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 838563557934578694948821 19653833389091688162863)
                ·
                  rfl

theorem cell21_258361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 2, 1, 7].length) (baseStart_258361 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_258361 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_258361 prefixEnd_258361 := by exact prefixLift 258361
  have htrace : WordTrace (prefixWord ++ tailWord_258361) baseStart_258361 baseEnd_258361 := by
    simpa [prefixWord, tailWord_258361, baseEnd_258361] using wordTrace_append hprefix tailTrace_258361
  have hstable : (prefixWord ++ tailWord_258361).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_258361).length < 2 ^ (prefixWord ++ tailWord_258361).sum := by decide
  have hdescent : baseEnd_258361 < baseStart_258361 := by decide
  rcases family_descends (prefixWord ++ tailWord_258361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_258516 : List Nat := [2, 4, 1, 2, 2, 2, 3, 1, 4]
def baseStart_258516 : Nat := 118140960795 + 258516 * 2 ^ 59
def prefixEnd_258516 : Nat := 4983230072969 + 3 ^ 40 * 258516 * 2
def baseEnd_258516 : Nat := 58996873279029239404939

theorem tailTrace_258516 : CollatzResearch.WordTrace tailWord_258516 prefixEnd_258516 58996873279029239404939 := by
  unfold tailWord_258516
  simp only [CollatzResearch.WordTrace]
  refine ⟨4714426565724078931433701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6285902087632105241911601 4714426565724078931433701)
  ·
    refine ⟨883954981073264799643819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4714426565724078931433701 883954981073264799643819)
    ·
      refine ⟨1325932471609897199465729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 883954981073264799643819 1325932471609897199465729)
      ·
        refine ⟨994449353707422899599297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1325932471609897199465729 994449353707422899599297)
        ·
          refine ⟨745837015280567174699473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 994449353707422899599297 745837015280567174699473)
          ·
            refine ⟨559377761460425381024605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 745837015280567174699473 559377761460425381024605)
            ·
              refine ⟨209766660547659517884227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 559377761460425381024605 209766660547659517884227)
              ·
                refine ⟨314649990821489276826341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 209766660547659517884227 314649990821489276826341)
                ·
                  refine ⟨58996873279029239404939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 314649990821489276826341 58996873279029239404939)
                  ·
                    rfl

theorem cell21_258516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 2, 3, 1, 4].length) (baseStart_258516 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_258516 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_258516 prefixEnd_258516 := by exact prefixLift 258516
  have htrace : WordTrace (prefixWord ++ tailWord_258516) baseStart_258516 baseEnd_258516 := by
    simpa [prefixWord, tailWord_258516, baseEnd_258516] using wordTrace_append hprefix tailTrace_258516
  have hstable : (prefixWord ++ tailWord_258516).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_258516).length < 2 ^ (prefixWord ++ tailWord_258516).sum := by decide
  have hdescent : baseEnd_258516 < baseStart_258516 := by decide
  rcases family_descends (prefixWord ++ tailWord_258516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_258527 : List Nat := [1, 1, 2, 3, 3, 2, 2, 2, 5]
def baseStart_258527 : Nat := 118140960795 + 258527 * 2 ^ 59
def prefixEnd_258527 : Nat := 4983230072969 + 3 ^ 40 * 258527 * 2
def baseEnd_258527 : Nat := 58999383628895664721583

theorem tailTrace_258527 : CollatzResearch.WordTrace tailWord_258527 prefixEnd_258527 58999383628895664721583 := by
  unfold tailWord_258527
  simp only [CollatzResearch.WordTrace]
  refine ⟨9429254334408306741517835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6286169556272204494345223 9429254334408306741517835)
  ·
    refine ⟨14143881501612460112276753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9429254334408306741517835 14143881501612460112276753)
    ·
      refine ⟨10607911126209345084207565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14143881501612460112276753 10607911126209345084207565)
      ·
        refine ⟨3977966672328504406577837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10607911126209345084207565 3977966672328504406577837)
        ·
          refine ⟨1491737502123189152466689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3977966672328504406577837 1491737502123189152466689)
          ·
            refine ⟨1118803126592391864350017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1491737502123189152466689 1118803126592391864350017)
            ·
              refine ⟨839102344944293898262513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1118803126592391864350017 839102344944293898262513)
              ·
                refine ⟨629326758708220423696885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 839102344944293898262513 629326758708220423696885)
                ·
                  refine ⟨58999383628895664721583, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 629326758708220423696885 58999383628895664721583)
                  ·
                    rfl

theorem cell21_258527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 2, 2, 5].length) (baseStart_258527 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_258527 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_258527 prefixEnd_258527 := by exact prefixLift 258527
  have htrace : WordTrace (prefixWord ++ tailWord_258527) baseStart_258527 baseEnd_258527 := by
    simpa [prefixWord, tailWord_258527, baseEnd_258527] using wordTrace_append hprefix tailTrace_258527
  have hstable : (prefixWord ++ tailWord_258527).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_258527).length < 2 ^ (prefixWord ++ tailWord_258527).sum := by decide
  have hdescent : baseEnd_258527 < baseStart_258527 := by decide
  rcases family_descends (prefixWord ++ tailWord_258527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_258572 : List Nat := [2, 2, 1, 2, 4, 1, 1, 8]
def baseStart_258572 : Nat := 118140960795 + 258572 * 2 ^ 59
def prefixEnd_258572 : Nat := 4983230072969 + 3 ^ 40 * 258572 * 2
def baseEnd_258572 : Nat := 19669884413995195490497

theorem tailTrace_258572 : CollatzResearch.WordTrace tailWord_258572 prefixEnd_258572 19669884413995195490497 := by
  unfold tailWord_258572
  simp only [CollatzResearch.WordTrace]
  refine ⟨4715447809622639713452985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6287263746163519617937313 4715447809622639713452985)
  ·
    refine ⟨3536585857216979785089739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4715447809622639713452985 3536585857216979785089739)
    ·
      refine ⟨5304878785825469677634609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3536585857216979785089739 5304878785825469677634609)
      ·
        refine ⟨3978659089369102258225957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5304878785825469677634609 3978659089369102258225957)
        ·
          refine ⟨745998579256706673417367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3978659089369102258225957 745998579256706673417367)
          ·
            refine ⟨1118997868885060010126051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 745998579256706673417367 1118997868885060010126051)
            ·
              refine ⟨1678496803327590015189077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1118997868885060010126051 1678496803327590015189077)
              ·
                refine ⟨19669884413995195490497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1678496803327590015189077 19669884413995195490497)
                ·
                  rfl

theorem cell21_258572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 1, 8].length) (baseStart_258572 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_258572 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_258572 prefixEnd_258572 := by exact prefixLift 258572
  have htrace : WordTrace (prefixWord ++ tailWord_258572) baseStart_258572 baseEnd_258572 := by
    simpa [prefixWord, tailWord_258572, baseEnd_258572] using wordTrace_append hprefix tailTrace_258572
  have hstable : (prefixWord ++ tailWord_258572).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_258572).length < 2 ^ (prefixWord ++ tailWord_258572).sum := by decide
  have hdescent : baseEnd_258572 < baseStart_258572 := by decide
  rcases family_descends (prefixWord ++ tailWord_258572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_258612 : List Nat := [2, 5, 1, 3, 1, 2, 2, 2, 3]
def baseStart_258612 : Nat := 118140960795 + 258612 * 2 ^ 59
def prefixEnd_258612 : Nat := 4983230072969 + 3 ^ 40 * 258612 * 2
def baseEnd_258612 : Nat := 59018781786954405804743

theorem tailTrace_258612 : CollatzResearch.WordTrace tailWord_258612 prefixEnd_258612 59018781786954405804743 := by
  unfold tailWord_258612
  simp only [CollatzResearch.WordTrace]
  refine ⟨4716177269550183129181045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6288236359400244172241393 4716177269550183129181045)
  ·
    refine ⟨442141619020329668360723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 4716177269550183129181045 442141619020329668360723)
    ·
      refine ⟨663212428530494502541085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 442141619020329668360723 663212428530494502541085)
      ·
        refine ⟨248704660698935438452907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 663212428530494502541085 248704660698935438452907)
        ·
          refine ⟨373056991048403157679361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 248704660698935438452907 373056991048403157679361)
          ·
            refine ⟨279792743286302368259521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 373056991048403157679361 279792743286302368259521)
            ·
              refine ⟨209844557464726776194641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 279792743286302368259521 209844557464726776194641)
              ·
                refine ⟨157383418098545082145981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 209844557464726776194641 157383418098545082145981)
                ·
                  refine ⟨59018781786954405804743, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 157383418098545082145981 59018781786954405804743)
                  ·
                    rfl

theorem cell21_258612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 1, 2, 2, 2, 3].length) (baseStart_258612 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_258612 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_258612 prefixEnd_258612 := by exact prefixLift 258612
  have htrace : WordTrace (prefixWord ++ tailWord_258612) baseStart_258612 baseEnd_258612 := by
    simpa [prefixWord, tailWord_258612, baseEnd_258612] using wordTrace_append hprefix tailTrace_258612
  have hstable : (prefixWord ++ tailWord_258612).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_258612).length < 2 ^ (prefixWord ++ tailWord_258612).sum := by decide
  have hdescent : baseEnd_258612 < baseStart_258612 := by decide
  rcases family_descends (prefixWord ++ tailWord_258612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_258634 : List Nat := [3, 1, 2, 1, 1, 4, 2, 3, 4]
def baseStart_258634 : Nat := 118140960795 + 258634 * 2 ^ 59
def prefixEnd_258634 : Nat := 4983230072969 + 3 ^ 40 * 258634 * 2
def baseEnd_258634 : Nat := 59023802486687256438031

theorem tailTrace_258634 : CollatzResearch.WordTrace tailWord_258634 prefixEnd_258634 59023802486687256438031 := by
  unfold tailWord_258634
  simp only [CollatzResearch.WordTrace]
  refine ⟨2358289236255166003915739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6288771296680442677108637 2358289236255166003915739)
  ·
    refine ⟨3537433854382749005873609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2358289236255166003915739 3537433854382749005873609)
    ·
      refine ⟨2653075390787061754405207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3537433854382749005873609 2653075390787061754405207)
      ·
        refine ⟨3979613086180592631607811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2653075390787061754405207 3979613086180592631607811)
        ·
          refine ⟨5969419629270888947411717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3979613086180592631607811 5969419629270888947411717)
          ·
            refine ⟨1119266180488291677639697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5969419629270888947411717 1119266180488291677639697)
            ·
              refine ⟨839449635366218758229773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1119266180488291677639697 839449635366218758229773)
              ·
                refine ⟨314793613262332034336165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 839449635366218758229773 314793613262332034336165)
                ·
                  refine ⟨59023802486687256438031, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 314793613262332034336165 59023802486687256438031)
                  ·
                    rfl

theorem cell21_258634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 2, 3, 4].length) (baseStart_258634 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_258634 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_258634 prefixEnd_258634 := by exact prefixLift 258634
  have htrace : WordTrace (prefixWord ++ tailWord_258634) baseStart_258634 baseEnd_258634 := by
    simpa [prefixWord, tailWord_258634, baseEnd_258634] using wordTrace_append hprefix tailTrace_258634
  have hstable : (prefixWord ++ tailWord_258634).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_258634).length < 2 ^ (prefixWord ++ tailWord_258634).sum := by decide
  have hdescent : baseEnd_258634 < baseStart_258634 := by decide
  rcases family_descends (prefixWord ++ tailWord_258634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_258707 : List Nat := [1, 1, 1, 2, 1, 2, 2, 11]
def baseStart_258707 : Nat := 118140960795 + 258707 * 2 ^ 59
def prefixEnd_258707 : Nat := 4983230072969 + 3 ^ 40 * 258707 * 2
def baseEnd_258707 : Nat := 19680154027085117240405

theorem tailTrace_258707 : CollatzResearch.WordTrace tailWord_258707 prefixEnd_258707 19680154027085117240405 := by
  unfold tailWord_258707
  simp only [CollatzResearch.WordTrace]
  refine ⟨9435819473756197483070375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6290546315837464988713583 9435819473756197483070375)
  ·
    refine ⟨14153729210634296224605563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9435819473756197483070375 14153729210634296224605563)
    ·
      refine ⟨21230593815951444336908345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14153729210634296224605563 21230593815951444336908345)
      ·
        refine ⟨15922945361963583252681259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21230593815951444336908345 15922945361963583252681259)
        ·
          refine ⟨23884418042945374879021889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15922945361963583252681259 23884418042945374879021889)
          ·
            refine ⟨17913313532209031159266417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23884418042945374879021889 17913313532209031159266417)
            ·
              refine ⟨13434985149156773369449813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17913313532209031159266417 13434985149156773369449813)
              ·
                refine ⟨19680154027085117240405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 13434985149156773369449813 19680154027085117240405)
                ·
                  rfl

theorem cell21_258707_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 11].length) (baseStart_258707 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_258707 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_258707 prefixEnd_258707 := by exact prefixLift 258707
  have htrace : WordTrace (prefixWord ++ tailWord_258707) baseStart_258707 baseEnd_258707 := by
    simpa [prefixWord, tailWord_258707, baseEnd_258707] using wordTrace_append hprefix tailTrace_258707
  have hstable : (prefixWord ++ tailWord_258707).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_258707).length < 2 ^ (prefixWord ++ tailWord_258707).sum := by decide
  have hdescent : baseEnd_258707 < baseStart_258707 := by decide
  rcases family_descends (prefixWord ++ tailWord_258707) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_258730 : List Nat := [3, 1, 5, 2, 1, 2, 1, 1, 5]
def baseStart_258730 : Nat := 118140960795 + 258730 * 2 ^ 59
def prefixEnd_258730 : Nat := 4983230072969 + 3 ^ 40 * 258730 * 2
def baseEnd_258730 : Nat := 59045710994612422837835

theorem tailTrace_258730 : CollatzResearch.WordTrace tailWord_258730 prefixEnd_258730 59045710994612422837835 := by
  unfold tailWord_258730
  simp only [CollatzResearch.WordTrace]
  refine ⟨2359164588168218102789411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6291105568448581607438429 2359164588168218102789411)
  ·
    refine ⟨3538746882252327154184117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2359164588168218102789411 3538746882252327154184117)
    ·
      refine ⟨331757520211155670704761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 3538746882252327154184117 331757520211155670704761)
      ·
        refine ⟨248818140158366753028571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 331757520211155670704761 248818140158366753028571)
        ·
          refine ⟨373227210237550129542857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 248818140158366753028571 373227210237550129542857)
          ·
            refine ⟨279920407678162597157143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 373227210237550129542857 279920407678162597157143)
            ·
              refine ⟨419880611517243895735715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 279920407678162597157143 419880611517243895735715)
              ·
                refine ⟨629820917275865843603573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 419880611517243895735715 629820917275865843603573)
                ·
                  refine ⟨59045710994612422837835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 629820917275865843603573 59045710994612422837835)
                  ·
                    rfl

theorem cell21_258730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 1, 2, 1, 1, 5].length) (baseStart_258730 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_258730 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_258730 prefixEnd_258730 := by exact prefixLift 258730
  have htrace : WordTrace (prefixWord ++ tailWord_258730) baseStart_258730 baseEnd_258730 := by
    simpa [prefixWord, tailWord_258730, baseEnd_258730] using wordTrace_append hprefix tailTrace_258730
  have hstable : (prefixWord ++ tailWord_258730).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_258730).length < 2 ^ (prefixWord ++ tailWord_258730).sum := by decide
  have hdescent : baseEnd_258730 < baseStart_258730 := by decide
  rcases family_descends (prefixWord ++ tailWord_258730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_258741 : List Nat := [1, 3, 3, 3, 1, 2, 2, 6]
def baseStart_258741 : Nat := 118140960795 + 258741 * 2 ^ 59
def prefixEnd_258741 : Nat := 4983230072969 + 3 ^ 40 * 258741 * 2
def baseEnd_258741 : Nat := 19682740448159616051493

theorem tailTrace_258741 : CollatzResearch.WordTrace tailWord_258741 prefixEnd_258741 19682740448159616051493 := by
  unfold tailWord_258741
  simp only [CollatzResearch.WordTrace]
  refine ⟨9437059555633021289808077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6291373037088680859872051 9437059555633021289808077)
  ·
    refine ⟨3538897333362382983678029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9437059555633021289808077 3538897333362382983678029)
    ·
      refine ⟨1327086500010893618879261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3538897333362382983678029 1327086500010893618879261)
      ·
        refine ⟨497657437504085107079723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1327086500010893618879261 497657437504085107079723)
        ·
          refine ⟨746486156256127660619585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 497657437504085107079723 746486156256127660619585)
          ·
            refine ⟨559864617192095745464689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 746486156256127660619585 559864617192095745464689)
            ·
              refine ⟨419898462894071809098517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 559864617192095745464689 419898462894071809098517)
              ·
                refine ⟨19682740448159616051493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 419898462894071809098517 19682740448159616051493)
                ·
                  rfl

theorem cell21_258741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 2, 2, 6].length) (baseStart_258741 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_258741 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_258741 prefixEnd_258741 := by exact prefixLift 258741
  have htrace : WordTrace (prefixWord ++ tailWord_258741) baseStart_258741 baseEnd_258741 := by
    simpa [prefixWord, tailWord_258741, baseEnd_258741] using wordTrace_append hprefix tailTrace_258741
  have hstable : (prefixWord ++ tailWord_258741).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_258741).length < 2 ^ (prefixWord ++ tailWord_258741).sum := by decide
  have hdescent : baseEnd_258741 < baseStart_258741 := by decide
  rcases family_descends (prefixWord ++ tailWord_258741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_258783 : List Nat := [1, 1, 2, 3, 2, 12]
def baseStart_258783 : Nat := 118140960795 + 258783 * 2 ^ 59
def prefixEnd_258783 : Nat := 4983230072969 + 3 ^ 40 * 258783 * 2
def baseEnd_258783 : Nat := 2187326159877633646459

theorem tailTrace_258783 : CollatzResearch.WordTrace tailWord_258783 prefixEnd_258783 2187326159877633646459 := by
  unfold tailWord_258783
  simp only [CollatzResearch.WordTrace]
  refine ⟨9438591421480862462837003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6292394280987241641891335 9438591421480862462837003)
  ·
    refine ⟨14157887132221293694255505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9438591421480862462837003 14157887132221293694255505)
    ·
      refine ⟨10618415349165970270691629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14157887132221293694255505 10618415349165970270691629)
      ·
        refine ⟨3981905755937238851509361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10618415349165970270691629 3981905755937238851509361)
        ·
          refine ⟨2986429316952929138632021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3981905755937238851509361 2986429316952929138632021)
          ·
            refine ⟨2187326159877633646459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 12 2986429316952929138632021 2187326159877633646459)
            ·
              rfl

theorem cell21_258783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 12].length) (baseStart_258783 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_258783 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_258783 prefixEnd_258783 := by exact prefixLift 258783
  have htrace : WordTrace (prefixWord ++ tailWord_258783) baseStart_258783 baseEnd_258783 := by
    simpa [prefixWord, tailWord_258783, baseEnd_258783] using wordTrace_append hprefix tailTrace_258783
  have hstable : (prefixWord ++ tailWord_258783).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_258783).length < 2 ^ (prefixWord ++ tailWord_258783).sum := by decide
  have hdescent : baseEnd_258783 < baseStart_258783 := by decide
  rcases family_descends (prefixWord ++ tailWord_258783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_258789 : List Nat := [1, 3, 1, 4, 1, 2, 4, 2, 3]
def baseStart_258789 : Nat := 118140960795 + 258789 * 2 ^ 59
def prefixEnd_258789 : Nat := 4983230072969 + 3 ^ 40 * 258789 * 2
def baseEnd_258789 : Nat := 59059175598441431354381

theorem tailTrace_258789 : CollatzResearch.WordTrace tailWord_258789 prefixEnd_258789 59059175598441431354381 := by
  unfold tailWord_258789
  simp only [CollatzResearch.WordTrace]
  refine ⟨9438810259459125487555421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6292540172972750325036947 9438810259459125487555421)
  ·
    refine ⟨3539553847297172057833283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9438810259459125487555421 3539553847297172057833283)
    ·
      refine ⟨5309330770945758086749925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3539553847297172057833283 5309330770945758086749925)
      ·
        refine ⟨995499519552329641265611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5309330770945758086749925 995499519552329641265611)
        ·
          refine ⟨1493249279328494461898417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 995499519552329641265611 1493249279328494461898417)
          ·
            refine ⟨1119936959496370846423813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1493249279328494461898417 1119936959496370846423813)
            ·
              refine ⟨209988179905569533704465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1119936959496370846423813 209988179905569533704465)
              ·
                refine ⟨157491134929177150278349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 209988179905569533704465 157491134929177150278349)
                ·
                  refine ⟨59059175598441431354381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 157491134929177150278349 59059175598441431354381)
                  ·
                    rfl

theorem cell21_258789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 4, 2, 3].length) (baseStart_258789 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_258789 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_258789 prefixEnd_258789 := by exact prefixLift 258789
  have htrace : WordTrace (prefixWord ++ tailWord_258789) baseStart_258789 baseEnd_258789 := by
    simpa [prefixWord, tailWord_258789, baseEnd_258789] using wordTrace_append hprefix tailTrace_258789
  have hstable : (prefixWord ++ tailWord_258789).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_258789).length < 2 ^ (prefixWord ++ tailWord_258789).sum := by decide
  have hdescent : baseEnd_258789 < baseStart_258789 := by decide
  rcases family_descends (prefixWord ++ tailWord_258789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_258848 : List Nat := [2, 1, 1, 5, 1, 2, 2, 4, 3]
def baseStart_258848 : Nat := 118140960795 + 258848 * 2 ^ 59
def prefixEnd_258848 : Nat := 4983230072969 + 3 ^ 40 * 258848 * 2
def baseEnd_258848 : Nat := 59072640202270439870927

theorem tailTrace_258848 : CollatzResearch.WordTrace tailWord_258848 prefixEnd_258848 59072640202270439870927 := by
  unfold tailWord_258848
  simp only [CollatzResearch.WordTrace]
  refine ⟨4720481083122689281976599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6293974777496919042635465 4720481083122689281976599)
  ·
    refine ⟨7080721624684033922964899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4720481083122689281976599 7080721624684033922964899)
    ·
      refine ⟨10621082437026050884447349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7080721624684033922964899 10621082437026050884447349)
      ·
        refine ⟨995726478471192270416939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 10621082437026050884447349 995726478471192270416939)
        ·
          refine ⟨1493589717706788405625409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 995726478471192270416939 1493589717706788405625409)
          ·
            refine ⟨1120192288280091304219057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1493589717706788405625409 1120192288280091304219057)
            ·
              refine ⟨840144216210068478164293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1120192288280091304219057 840144216210068478164293)
              ·
                refine ⟨157527040539387839655805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 840144216210068478164293 157527040539387839655805)
                ·
                  refine ⟨59072640202270439870927, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 157527040539387839655805 59072640202270439870927)
                  ·
                    rfl

theorem cell21_258848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 2, 4, 3].length) (baseStart_258848 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_258848 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_258848 prefixEnd_258848 := by exact prefixLift 258848
  have htrace : WordTrace (prefixWord ++ tailWord_258848) baseStart_258848 baseEnd_258848 := by
    simpa [prefixWord, tailWord_258848, baseEnd_258848] using wordTrace_append hprefix tailTrace_258848
  have hstable : (prefixWord ++ tailWord_258848).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_258848).length < 2 ^ (prefixWord ++ tailWord_258848).sum := by decide
  have hdescent : baseEnd_258848 < baseStart_258848 := by decide
  rcases family_descends (prefixWord ++ tailWord_258848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_258997 : List Nat := [1, 3, 3, 2, 1, 1, 2, 2, 6]
def baseStart_258997 : Nat := 118140960795 + 258997 * 2 ^ 59
def prefixEnd_258997 : Nat := 4983230072969 + 3 ^ 40 * 258997 * 2
def baseEnd_258997 : Nat := 59106644032279291887289

theorem tailTrace_258997 : CollatzResearch.WordTrace tailWord_258997 prefixEnd_258997 59106644032279291887289 := by
  unfold tailWord_258997
  simp only [CollatzResearch.WordTrace]
  refine ⟨9446396642705577011127245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6297597761803718007418163 9446396642705577011127245)
  ·
    refine ⟨3542398741014591379172717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9446396642705577011127245 3542398741014591379172717)
    ·
      refine ⟨1328399527880471767189769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3542398741014591379172717 1328399527880471767189769)
      ·
        refine ⟨996299645910353825392327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1328399527880471767189769 996299645910353825392327)
        ·
          refine ⟨1494449468865530738088491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 996299645910353825392327 1494449468865530738088491)
          ·
            refine ⟨2241674203298296107132737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1494449468865530738088491 2241674203298296107132737)
            ·
              refine ⟨1681255652473722080349553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2241674203298296107132737 1681255652473722080349553)
              ·
                refine ⟨1260941739355291560262165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1681255652473722080349553 1260941739355291560262165)
                ·
                  refine ⟨59106644032279291887289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1260941739355291560262165 59106644032279291887289)
                  ·
                    rfl

theorem cell21_258997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 2, 2, 6].length) (baseStart_258997 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_258997 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_258997 prefixEnd_258997 := by exact prefixLift 258997
  have htrace : WordTrace (prefixWord ++ tailWord_258997) baseStart_258997 baseEnd_258997 := by
    simpa [prefixWord, tailWord_258997, baseEnd_258997] using wordTrace_append hprefix tailTrace_258997
  have hstable : (prefixWord ++ tailWord_258997).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_258997).length < 2 ^ (prefixWord ++ tailWord_258997).sum := by decide
  have hdescent : baseEnd_258997 < baseStart_258997 := by decide
  rcases family_descends (prefixWord ++ tailWord_258997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_259000 : List Nat := [2, 1, 2, 1, 2, 5, 2, 3, 3]
def baseStart_259000 : Nat := 118140960795 + 259000 * 2 ^ 59
def prefixEnd_259000 : Nat := 4983230072969 + 3 ^ 40 * 259000 * 2
def baseEnd_259000 : Nat := 59107328673151953337283

theorem tailTrace_259000 : CollatzResearch.WordTrace tailWord_259000 prefixEnd_259000 59107328673151953337283 := by
  unfold tailWord_259000
  simp only [CollatzResearch.WordTrace]
  refine ⟨4723253030847354261743227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6297670707796472348990969 4723253030847354261743227)
  ·
    refine ⟨7084879546271031392614841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4723253030847354261743227 7084879546271031392614841)
    ·
      refine ⟨5313659659703273544461131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7084879546271031392614841 5313659659703273544461131)
      ·
        refine ⟨7970489489554910316691697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5313659659703273544461131 7970489489554910316691697)
        ·
          refine ⟨5977867117166182737518773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7970489489554910316691697 5977867117166182737518773)
          ·
            refine ⟨560425042234329631642385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 5977867117166182737518773 560425042234329631642385)
            ·
              refine ⟨420318781675747223731789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 560425042234329631642385 420318781675747223731789)
              ·
                refine ⟨157619543128405208899421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 420318781675747223731789 157619543128405208899421)
                ·
                  refine ⟨59107328673151953337283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 157619543128405208899421 59107328673151953337283)
                  ·
                    rfl

theorem cell21_259000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 5, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 5, 2, 3, 3].length) (baseStart_259000 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_259000 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_259000 prefixEnd_259000 := by exact prefixLift 259000
  have htrace : WordTrace (prefixWord ++ tailWord_259000) baseStart_259000 baseEnd_259000 := by
    simpa [prefixWord, tailWord_259000, baseEnd_259000] using wordTrace_append hprefix tailTrace_259000
  have hstable : (prefixWord ++ tailWord_259000).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_259000).length < 2 ^ (prefixWord ++ tailWord_259000).sum := by decide
  have hdescent : baseEnd_259000 < baseStart_259000 := by decide
  rcases family_descends (prefixWord ++ tailWord_259000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_259045 : List Nat := [1, 3, 1, 6, 1, 1, 1, 7]
def baseStart_259045 : Nat := 118140960795 + 259045 * 2 ^ 59
def prefixEnd_259045 : Nat := 4983230072969 + 3 ^ 40 * 259045 * 2
def baseEnd_259045 : Nat := 19705866095413958362397

theorem tailTrace_259045 : CollatzResearch.WordTrace tailWord_259045 prefixEnd_259045 19705866095413958362397 := by
  unfold tailWord_259045
  simp only [CollatzResearch.WordTrace]
  refine ⟨9448147346531681208874589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6298764897687787472583059 9448147346531681208874589)
  ·
    refine ⟨3543055254949380453327971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9448147346531681208874589 3543055254949380453327971)
    ·
      refine ⟨5314582882424070679991957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3543055254949380453327971 5314582882424070679991957)
      ·
        refine ⟨249121072613628313124623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 5314582882424070679991957 249121072613628313124623)
        ·
          refine ⟨373681608920442469686935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 249121072613628313124623 373681608920442469686935)
          ·
            refine ⟨560522413380663704530403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 373681608920442469686935 560522413380663704530403)
            ·
              refine ⟨840783620070995556795605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 560522413380663704530403 840783620070995556795605)
              ·
                refine ⟨19705866095413958362397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 840783620070995556795605 19705866095413958362397)
                ·
                  rfl

theorem cell21_259045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 1, 1, 1, 7].length) (baseStart_259045 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_259045 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_259045 prefixEnd_259045 := by exact prefixLift 259045
  have htrace : WordTrace (prefixWord ++ tailWord_259045) baseStart_259045 baseEnd_259045 := by
    simpa [prefixWord, tailWord_259045, baseEnd_259045] using wordTrace_append hprefix tailTrace_259045
  have hstable : (prefixWord ++ tailWord_259045).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_259045).length < 2 ^ (prefixWord ++ tailWord_259045).sum := by decide
  have hdescent : baseEnd_259045 < baseStart_259045 := by decide
  rcases family_descends (prefixWord ++ tailWord_259045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_259073 : List Nat := [1, 2, 4, 1, 2, 2, 2, 1, 6]
def baseStart_259073 : Nat := 118140960795 + 259073 * 2 ^ 59
def prefixEnd_259073 : Nat := 4983230072969 + 3 ^ 40 * 259073 * 2
def baseEnd_259073 : Nat := 59123988267720048620467

theorem tailTrace_259073 : CollatzResearch.WordTrace tailWord_259073 prefixEnd_259073 59123988267720048620467 := by
  unfold tailWord_259073
  simp only [CollatzResearch.WordTrace]
  refine ⟨9449168590430241990893873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6299445726953494660595915 9449168590430241990893873)
  ·
    refine ⟨7086876442822681493170405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9449168590430241990893873 7086876442822681493170405)
    ·
      refine ⟨1328789333029252779969451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7086876442822681493170405 1328789333029252779969451)
      ·
        refine ⟨1993183999543879169954177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1328789333029252779969451 1993183999543879169954177)
        ·
          refine ⟨1494887999657909377465633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1993183999543879169954177 1494887999657909377465633)
          ·
            refine ⟨1121165999743432033099225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1494887999657909377465633 1121165999743432033099225)
            ·
              refine ⟨840874499807574024824419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1121165999743432033099225 840874499807574024824419)
              ·
                refine ⟨1261311749711361037236629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 840874499807574024824419 1261311749711361037236629)
                ·
                  refine ⟨59123988267720048620467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1261311749711361037236629 59123988267720048620467)
                  ·
                    rfl

theorem cell21_259073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 2, 1, 6].length) (baseStart_259073 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_259073 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_259073 prefixEnd_259073 := by exact prefixLift 259073
  have htrace : WordTrace (prefixWord ++ tailWord_259073) baseStart_259073 baseEnd_259073 := by
    simpa [prefixWord, tailWord_259073, baseEnd_259073] using wordTrace_append hprefix tailTrace_259073
  have hstable : (prefixWord ++ tailWord_259073).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_259073).length < 2 ^ (prefixWord ++ tailWord_259073).sum := by decide
  have hdescent : baseEnd_259073 < baseStart_259073 := by decide
  rcases family_descends (prefixWord ++ tailWord_259073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_259228 : List Nat := [2, 2, 3, 2, 1, 2, 3, 3, 3]
def baseStart_259228 : Nat := 118140960795 + 259228 * 2 ^ 59
def prefixEnd_259228 : Nat := 4983230072969 + 3 ^ 40 * 259228 * 2
def baseEnd_259228 : Nat := 59159361379474223536817

theorem tailTrace_259228 : CollatzResearch.WordTrace tailWord_259228 prefixEnd_259228 59159361379474223536817 := by
  unfold tailWord_259228
  simp only [CollatzResearch.WordTrace]
  refine ⟨4727410952434351731393169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6303214603245802308524225 4727410952434351731393169)
  ·
    refine ⟨3545558214325763798544877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4727410952434351731393169 3545558214325763798544877)
    ·
      refine ⟨1329584330372161424454329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3545558214325763798544877 1329584330372161424454329)
      ·
        refine ⟨997188247779121068340747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1329584330372161424454329 997188247779121068340747)
        ·
          refine ⟨1495782371668681602511121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 997188247779121068340747 1495782371668681602511121)
          ·
            refine ⟨1121836778751511201883341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1495782371668681602511121 1121836778751511201883341)
            ·
              refine ⟨420688792031816700706253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1121836778751511201883341 420688792031816700706253)
              ·
                refine ⟨157758297011931262764845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 420688792031816700706253 157758297011931262764845)
                ·
                  refine ⟨59159361379474223536817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 157758297011931262764845 59159361379474223536817)
                  ·
                    rfl

theorem cell21_259228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 3, 3, 3].length) (baseStart_259228 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_259228 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_259228 prefixEnd_259228 := by exact prefixLift 259228
  have htrace : WordTrace (prefixWord ++ tailWord_259228) baseStart_259228 baseEnd_259228 := by
    simpa [prefixWord, tailWord_259228, baseEnd_259228] using wordTrace_append hprefix tailTrace_259228
  have hstable : (prefixWord ++ tailWord_259228).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_259228).length < 2 ^ (prefixWord ++ tailWord_259228).sum := by decide
  have hdescent : baseEnd_259228 < baseStart_259228 := by decide
  rcases family_descends (prefixWord ++ tailWord_259228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_259242 : List Nat := [3, 1, 5, 1, 1, 1, 2, 1, 6]
def baseStart_259242 : Nat := 118140960795 + 259242 * 2 ^ 59
def prefixEnd_259242 : Nat := 4983230072969 + 3 ^ 40 * 259242 * 2
def baseEnd_259242 : Nat := 59162556370213310303455

theorem tailTrace_259242 : CollatzResearch.WordTrace tailWord_259242 prefixEnd_259242 59162556370213310303455 := by
  unfold tailWord_259242
  simp only [CollatzResearch.WordTrace]
  refine ⟨2363833131704495963448995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6303555017878655902530653 2363833131704495963448995)
  ·
    refine ⟨3545749697556743945173493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2363833131704495963448995 3545749697556743945173493)
    ·
      refine ⟨332414034145944744860015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 3545749697556743945173493 332414034145944744860015)
      ·
        refine ⟨498621051218917117290023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 332414034145944744860015 498621051218917117290023)
        ·
          refine ⟨747931576828375675935035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 498621051218917117290023 747931576828375675935035)
          ·
            refine ⟨1121897365242563513902553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 747931576828375675935035 1121897365242563513902553)
            ·
              refine ⟨841423023931922635426915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1121897365242563513902553 841423023931922635426915)
              ·
                refine ⟨1262134535897883953140373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 841423023931922635426915 1262134535897883953140373)
                ·
                  refine ⟨59162556370213310303455, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1262134535897883953140373 59162556370213310303455)
                  ·
                    rfl

theorem cell21_259242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 2, 1, 6].length) (baseStart_259242 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_259242 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_259242 prefixEnd_259242 := by exact prefixLift 259242
  have htrace : WordTrace (prefixWord ++ tailWord_259242) baseStart_259242 baseEnd_259242 := by
    simpa [prefixWord, tailWord_259242, baseEnd_259242] using wordTrace_append hprefix tailTrace_259242
  have hstable : (prefixWord ++ tailWord_259242).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_259242).length < 2 ^ (prefixWord ++ tailWord_259242).sum := by decide
  have hdescent : baseEnd_259242 < baseStart_259242 := by decide
  rcases family_descends (prefixWord ++ tailWord_259242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_259245 : List Nat := [1, 5, 2, 1, 4, 1, 1, 1, 5]
def baseStart_259245 : Nat := 118140960795 + 259245 * 2 ^ 59
def prefixEnd_259245 : Nat := 4983230072969 + 3 ^ 40 * 259245 * 2
def baseEnd_259245 : Nat := 59163241011085971753449

theorem tailTrace_259245 : CollatzResearch.WordTrace tailWord_259245 prefixEnd_259245 59163241011085971753449 := by
  unfold tailWord_259245
  simp only [CollatzResearch.WordTrace]
  refine ⟨9455441945807115366155189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6303627963871410244103459 9455441945807115366155189)
  ·
    refine ⟨886447682419417065577049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 9455441945807115366155189 886447682419417065577049)
    ·
      refine ⟨664835761814562799182787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 886447682419417065577049 664835761814562799182787)
      ·
        refine ⟨997253642721844198774181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 664835761814562799182787 997253642721844198774181)
        ·
          refine ⟨186985058010345787270159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 997253642721844198774181 186985058010345787270159)
          ·
            refine ⟨280477587015518680905239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 186985058010345787270159 280477587015518680905239)
            ·
              refine ⟨420716380523278021357859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 280477587015518680905239 420716380523278021357859)
              ·
                refine ⟨631074570784917032036789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 420716380523278021357859 631074570784917032036789)
                ·
                  refine ⟨59163241011085971753449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 631074570784917032036789 59163241011085971753449)
                  ·
                    rfl

theorem cell21_259245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 4, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 4, 1, 1, 1, 5].length) (baseStart_259245 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_259245 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_259245 prefixEnd_259245 := by exact prefixLift 259245
  have htrace : WordTrace (prefixWord ++ tailWord_259245) baseStart_259245 baseEnd_259245 := by
    simpa [prefixWord, tailWord_259245, baseEnd_259245] using wordTrace_append hprefix tailTrace_259245
  have hstable : (prefixWord ++ tailWord_259245).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_259245).length < 2 ^ (prefixWord ++ tailWord_259245).sum := by decide
  have hdescent : baseEnd_259245 < baseStart_259245 := by decide
  rcases family_descends (prefixWord ++ tailWord_259245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_259315 : List Nat := [1, 1, 1, 2, 2, 5, 3, 6]
def baseStart_259315 : Nat := 118140960795 + 259315 * 2 ^ 59
def prefixEnd_259315 : Nat := 4983230072969 + 3 ^ 40 * 259315 * 2
def baseEnd_259315 : Nat := 19726405321593801862213

theorem tailTrace_259315 : CollatzResearch.WordTrace tailWord_259315 prefixEnd_259315 19726405321593801862213 := by
  unfold tailWord_259315
  simp only [CollatzResearch.WordTrace]
  refine ⟨9457995055553517321203399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6305330037035678214135599 9457995055553517321203399)
  ·
    refine ⟨14186992583330275981805099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9457995055553517321203399 14186992583330275981805099)
    ·
      refine ⟨21280488874995413972707649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14186992583330275981805099 21280488874995413972707649)
      ·
        refine ⟨15960366656246560479530737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21280488874995413972707649 15960366656246560479530737)
        ·
          refine ⟨11970274992184920359648053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15960366656246560479530737 11970274992184920359648053)
          ·
            refine ⟨1122213280517336283717005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 11970274992184920359648053 1122213280517336283717005)
            ·
              refine ⟨420829980194001106393877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1122213280517336283717005 420829980194001106393877)
              ·
                refine ⟨19726405321593801862213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 420829980194001106393877 19726405321593801862213)
                ·
                  rfl

theorem cell21_259315_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 3, 6].length) (baseStart_259315 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_259315 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_259315 prefixEnd_259315 := by exact prefixLift 259315
  have htrace : WordTrace (prefixWord ++ tailWord_259315) baseStart_259315 baseEnd_259315 := by
    simpa [prefixWord, tailWord_259315, baseEnd_259315] using wordTrace_append hprefix tailTrace_259315
  have hstable : (prefixWord ++ tailWord_259315).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_259315).length < 2 ^ (prefixWord ++ tailWord_259315).sum := by decide
  have hdescent : baseEnd_259315 < baseStart_259315 := by decide
  rcases family_descends (prefixWord ++ tailWord_259315) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_259363 : List Nat := [1, 1, 1, 4, 2, 3, 2, 4, 3]
def baseStart_259363 : Nat := 118140960795 + 259363 * 2 ^ 59
def prefixEnd_259363 : Nat := 4983230072969 + 3 ^ 40 * 259363 * 2
def baseEnd_259363 : Nat := 59190170218743988786541

theorem tailTrace_259363 : CollatzResearch.WordTrace tailWord_259363 prefixEnd_259363 59190170218743988786541 := by
  unfold tailWord_259363
  simp only [CollatzResearch.WordTrace]
  refine ⟨9459745759379621518950743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6306497172919747679300495 9459745759379621518950743)
  ·
    refine ⟨14189618639069432278426115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9459745759379621518950743 14189618639069432278426115)
    ·
      refine ⟨21284427958604148417639173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14189618639069432278426115 21284427958604148417639173)
      ·
        refine ⟨3990830242238277828307345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 21284427958604148417639173 3990830242238277828307345)
        ·
          refine ⟨2993122681678708371230509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3990830242238277828307345 2993122681678708371230509)
          ·
            refine ⟨1122421005629515639211441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2993122681678708371230509 1122421005629515639211441)
            ·
              refine ⟨841815754222136729408581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1122421005629515639211441 841815754222136729408581)
              ·
                refine ⟨157840453916650636764109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 841815754222136729408581 157840453916650636764109)
                ·
                  refine ⟨59190170218743988786541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 157840453916650636764109 59190170218743988786541)
                  ·
                    rfl

theorem cell21_259363_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 2, 4, 3].length) (baseStart_259363 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_259363 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_259363 prefixEnd_259363 := by exact prefixLift 259363
  have htrace : WordTrace (prefixWord ++ tailWord_259363) baseStart_259363 baseEnd_259363 := by
    simpa [prefixWord, tailWord_259363, baseEnd_259363] using wordTrace_append hprefix tailTrace_259363
  have hstable : (prefixWord ++ tailWord_259363).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_259363).length < 2 ^ (prefixWord ++ tailWord_259363).sum := by decide
  have hdescent : baseEnd_259363 < baseStart_259363 := by decide
  rcases family_descends (prefixWord ++ tailWord_259363) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_259391 : List Nat := [1, 1, 2, 2, 4, 3, 1, 7]
def baseStart_259391 : Nat := 118140960795 + 259391 * 2 ^ 59
def prefixEnd_259391 : Nat := 4983230072969 + 3 ^ 40 * 259391 * 2
def baseEnd_259391 : Nat := 19732186733407387439939

theorem tailTrace_259391 : CollatzResearch.WordTrace tailWord_259391 prefixEnd_259391 19732186733407387439939 := by
  unfold tailWord_259391
  simp only [CollatzResearch.WordTrace]
  refine ⟨9460767003278182300970027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6307178002185454867313351 9460767003278182300970027)
  ·
    refine ⟨14191150504917273451455041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9460767003278182300970027 14191150504917273451455041)
    ·
      refine ⟨10643362878687955088591281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14191150504917273451455041 10643362878687955088591281)
      ·
        refine ⟨7982522159015966316443461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10643362878687955088591281 7982522159015966316443461)
        ·
          refine ⟨1496722904815493684333149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7982522159015966316443461 1496722904815493684333149)
          ·
            refine ⟨561271089305810131624931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1496722904815493684333149 561271089305810131624931)
            ·
              refine ⟨841906633958715197437397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 561271089305810131624931 841906633958715197437397)
              ·
                refine ⟨19732186733407387439939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 841906633958715197437397 19732186733407387439939)
                ·
                  rfl

theorem cell21_259391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 3, 1, 7].length) (baseStart_259391 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_259391 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_259391 prefixEnd_259391 := by exact prefixLift 259391
  have htrace : WordTrace (prefixWord ++ tailWord_259391) baseStart_259391 baseEnd_259391 := by
    simpa [prefixWord, tailWord_259391, baseEnd_259391] using wordTrace_append hprefix tailTrace_259391
  have hstable : (prefixWord ++ tailWord_259391).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_259391).length < 2 ^ (prefixWord ++ tailWord_259391).sum := by decide
  have hdescent : baseEnd_259391 < baseStart_259391 := by decide
  rcases family_descends (prefixWord ++ tailWord_259391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_259501 : List Nat := [1, 5, 2, 2, 1, 2, 3, 5]
def baseStart_259501 : Nat := 118140960795 + 259501 * 2 ^ 59
def prefixEnd_259501 : Nat := 4983230072969 + 3 ^ 40 * 259501 * 2
def baseEnd_259501 : Nat := 19740554566295471828753

theorem tailTrace_259501 : CollatzResearch.WordTrace tailWord_259501 prefixEnd_259501 19740554566295471828753 := by
  unfold tailWord_259501
  simp only [CollatzResearch.WordTrace]
  refine ⟨9464779032879671087474357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6309852688586447391649571 9464779032879671087474357)
  ·
    refine ⟨887323034332469164450721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 9464779032879671087474357 887323034332469164450721)
    ·
      refine ⟨665492275749351873338041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 887323034332469164450721 665492275749351873338041)
      ·
        refine ⟨499119206812013905003531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 665492275749351873338041 499119206812013905003531)
        ·
          refine ⟨748678810218020857505297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 499119206812013905003531 748678810218020857505297)
          ·
            refine ⟨561509107663515643128973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 748678810218020857505297 561509107663515643128973)
            ·
              refine ⟨210565915373818366173365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 561509107663515643128973 210565915373818366173365)
              ·
                refine ⟨19740554566295471828753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 210565915373818366173365 19740554566295471828753)
                ·
                  rfl

theorem cell21_259501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 2, 3, 5].length) (baseStart_259501 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_259501 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_259501 prefixEnd_259501 := by exact prefixLift 259501
  have htrace : WordTrace (prefixWord ++ tailWord_259501) baseStart_259501 baseEnd_259501 := by
    simpa [prefixWord, tailWord_259501, baseEnd_259501] using wordTrace_append hprefix tailTrace_259501
  have hstable : (prefixWord ++ tailWord_259501).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_259501).length < 2 ^ (prefixWord ++ tailWord_259501).sum := by decide
  have hdescent : baseEnd_259501 < baseStart_259501 := by decide
  rcases family_descends (prefixWord ++ tailWord_259501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_259546 : List Nat := [3, 1, 1, 2, 3, 3, 3, 1, 4]
def baseStart_259546 : Nat := 118140960795 + 259546 * 2 ^ 59
def prefixEnd_259546 : Nat := 4983230072969 + 3 ^ 40 * 259546 * 2
def baseEnd_259546 : Nat := 59231933311976337236167

theorem tailTrace_259546 : CollatzResearch.WordTrace tailWord_259546 prefixEnd_259546 59231933311976337236167 := by
  unfold tailWord_259546
  simp only [CollatzResearch.WordTrace]
  refine ⟨2366605079429160943215623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6310946878477762515241661 2366605079429160943215623)
  ·
    refine ⟨3549907619143741414823435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2366605079429160943215623 3549907619143741414823435)
    ·
      refine ⟨5324861428715612122235153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3549907619143741414823435 5324861428715612122235153)
      ·
        refine ⟨3993646071536709091676365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5324861428715612122235153 3993646071536709091676365)
        ·
          refine ⟨1497617276826265909378637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3993646071536709091676365 1497617276826265909378637)
          ·
            refine ⟨561606478809849716016989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1497617276826265909378637 561606478809849716016989)
            ·
              refine ⟨210602429553693643506371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 561606478809849716016989 210602429553693643506371)
              ·
                refine ⟨315903644330540465259557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 210602429553693643506371 315903644330540465259557)
                ·
                  refine ⟨59231933311976337236167, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 315903644330540465259557 59231933311976337236167)
                  ·
                    rfl

theorem cell21_259546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 3, 3, 1, 4].length) (baseStart_259546 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_259546 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_259546 prefixEnd_259546 := by exact prefixLift 259546
  have htrace : WordTrace (prefixWord ++ tailWord_259546) baseStart_259546 baseEnd_259546 := by
    simpa [prefixWord, tailWord_259546, baseEnd_259546] using wordTrace_append hprefix tailTrace_259546
  have hstable : (prefixWord ++ tailWord_259546).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_259546).length < 2 ^ (prefixWord ++ tailWord_259546).sum := by decide
  have hdescent : baseEnd_259546 < baseStart_259546 := by decide
  rcases family_descends (prefixWord ++ tailWord_259546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_259591 : List Nat := [1, 1, 4, 3, 2, 3, 1, 1, 5]
def baseStart_259591 : Nat := 118140960795 + 259591 * 2 ^ 59
def prefixEnd_259591 : Nat := 4983230072969 + 3 ^ 40 * 259591 * 2
def baseEnd_259591 : Nat := 59242202925066258986075

theorem tailTrace_259591 : CollatzResearch.WordTrace tailWord_259591 prefixEnd_259591 59242202925066258986075 := by
  unfold tailWord_259591
  simp only [CollatzResearch.WordTrace]
  refine ⟨9468061602553616458250627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6312041068369077638833751 9468061602553616458250627)
  ·
    refine ⟨14202092403830424687375941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9468061602553616458250627 14202092403830424687375941)
    ·
      refine ⟨2662892325718204628882989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 14202092403830424687375941 2662892325718204628882989)
      ·
        refine ⟨998584622144326735831121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2662892325718204628882989 998584622144326735831121)
        ·
          refine ⟨748938466608245051873341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 998584622144326735831121 748938466608245051873341)
          ·
            refine ⟨280851924978091894452503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 748938466608245051873341 280851924978091894452503)
            ·
              refine ⟨421277887467137841678755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 280851924978091894452503 421277887467137841678755)
              ·
                refine ⟨631916831200706762518133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 421277887467137841678755 631916831200706762518133)
                ·
                  refine ⟨59242202925066258986075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 631916831200706762518133 59242202925066258986075)
                  ·
                    rfl

theorem cell21_259591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 3, 1, 1, 5].length) (baseStart_259591 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_259591 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_259591 prefixEnd_259591 := by exact prefixLift 259591
  have htrace : WordTrace (prefixWord ++ tailWord_259591) baseStart_259591 baseEnd_259591 := by
    simpa [prefixWord, tailWord_259591, baseEnd_259591] using wordTrace_append hprefix tailTrace_259591
  have hstable : (prefixWord ++ tailWord_259591).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_259591).length < 2 ^ (prefixWord ++ tailWord_259591).sum := by decide
  have hdescent : baseEnd_259591 < baseStart_259591 := by decide
  rcases family_descends (prefixWord ++ tailWord_259591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_259597 : List Nat := [1, 7, 1, 1, 2, 2, 2, 1, 4]
def baseStart_259597 : Nat := 118140960795 + 259597 * 2 ^ 59
def prefixEnd_259597 : Nat := 4983230072969 + 3 ^ 40 * 259597 * 2
def baseEnd_259597 : Nat := 59243572206811581886063

theorem tailTrace_259597 : CollatzResearch.WordTrace tailWord_259597 prefixEnd_259597 59243572206811581886063 := by
  unfold tailWord_259597
  simp only [CollatzResearch.WordTrace]
  refine ⟨9468280440531879482969045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6312186960354586321979363 9468280440531879482969045)
  ·
    refine ⟨221912822824965925382087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 9468280440531879482969045 221912822824965925382087)
    ·
      refine ⟨332869234237448888073131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 221912822824965925382087 332869234237448888073131)
      ·
        refine ⟨499303851356173332109697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 332869234237448888073131 499303851356173332109697)
        ·
          refine ⟨374477888517129999082273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 499303851356173332109697 374477888517129999082273)
          ·
            refine ⟨280858416387847499311705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 374477888517129999082273 280858416387847499311705)
            ·
              refine ⟨210643812290885624483779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 280858416387847499311705 210643812290885624483779)
              ·
                refine ⟨315965718436328436725669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 210643812290885624483779 315965718436328436725669)
                ·
                  refine ⟨59243572206811581886063, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 315965718436328436725669 59243572206811581886063)
                  ·
                    rfl

theorem cell21_259597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 2, 2, 2, 1, 4].length) (baseStart_259597 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_259597 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_259597 prefixEnd_259597 := by exact prefixLift 259597
  have htrace : WordTrace (prefixWord ++ tailWord_259597) baseStart_259597 baseEnd_259597 := by
    simpa [prefixWord, tailWord_259597, baseEnd_259597] using wordTrace_append hprefix tailTrace_259597
  have hstable : (prefixWord ++ tailWord_259597).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_259597).length < 2 ^ (prefixWord ++ tailWord_259597).sum := by decide
  have hdescent : baseEnd_259597 < baseStart_259597 := by decide
  rcases family_descends (prefixWord ++ tailWord_259597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_259605 : List Nat := [1, 3, 2, 1, 3, 3, 1, 3, 4]
def baseStart_259605 : Nat := 118140960795 + 259605 * 2 ^ 59
def prefixEnd_259605 : Nat := 4983230072969 + 3 ^ 40 * 259605 * 2
def baseEnd_259605 : Nat := 59245397915805345752713

theorem tailTrace_259605 : CollatzResearch.WordTrace tailWord_259605 prefixEnd_259605 59245397915805345752713 := by
  unfold tailWord_259605
  simp only [CollatzResearch.WordTrace]
  refine ⟨9468572224502896849260269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6312381483001931232840179 9468572224502896849260269)
  ·
    refine ⟨3550714584188586318472601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9468572224502896849260269 3550714584188586318472601)
    ·
      refine ⟨2663035938141439738854451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3550714584188586318472601 2663035938141439738854451)
      ·
        refine ⟨3994553907212159608281677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2663035938141439738854451 3994553907212159608281677)
        ·
          refine ⟨1497957715204559853105629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3994553907212159608281677 1497957715204559853105629)
          ·
            refine ⟨561734143201709944914611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1497957715204559853105629 561734143201709944914611)
            ·
              refine ⟨842601214802564917371917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 561734143201709944914611 842601214802564917371917)
              ·
                refine ⟨315975455550961844014469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 842601214802564917371917 315975455550961844014469)
                ·
                  refine ⟨59245397915805345752713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 315975455550961844014469 59245397915805345752713)
                  ·
                    rfl

theorem cell21_259605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 3, 1, 3, 4].length) (baseStart_259605 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_259605 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_259605 prefixEnd_259605 := by exact prefixLift 259605
  have htrace : WordTrace (prefixWord ++ tailWord_259605) baseStart_259605 baseEnd_259605 := by
    simpa [prefixWord, tailWord_259605, baseEnd_259605] using wordTrace_append hprefix tailTrace_259605
  have hstable : (prefixWord ++ tailWord_259605).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_259605).length < 2 ^ (prefixWord ++ tailWord_259605).sum := by decide
  have hdescent : baseEnd_259605 < baseStart_259605 := by decide
  rcases family_descends (prefixWord ++ tailWord_259605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_259664 : List Nat := [2, 1, 1, 1, 1, 3, 3, 5, 4]
def baseStart_259664 : Nat := 118140960795 + 259664 * 2 ^ 59
def prefixEnd_259664 : Nat := 4983230072969 + 3 ^ 40 * 259664 * 2
def baseEnd_259664 : Nat := 59258862519634354269259

theorem tailTrace_259664 : CollatzResearch.WordTrace tailWord_259664 prefixEnd_259664 59258862519634354269259 := by
  unfold tailWord_259664
  simp only [CollatzResearch.WordTrace]
  refine ⟨4735362065644574962829023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6313816087526099950438697 4735362065644574962829023)
  ·
    refine ⟨7103043098466862444243535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4735362065644574962829023 7103043098466862444243535)
    ·
      refine ⟨10654564647700293666365303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7103043098466862444243535 10654564647700293666365303)
      ·
        refine ⟨15981846971550440499547955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10654564647700293666365303 15981846971550440499547955)
        ·
          refine ⟨23972770457325660749321933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15981846971550440499547955 23972770457325660749321933)
          ·
            refine ⟨8989788921497122780995725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23972770457325660749321933 8989788921497122780995725)
            ·
              refine ⟨3371170845561421042873397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8989788921497122780995725 3371170845561421042873397)
              ·
                refine ⟨316047266771383222769381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3371170845561421042873397 316047266771383222769381)
                ·
                  refine ⟨59258862519634354269259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 316047266771383222769381 59258862519634354269259)
                  ·
                    rfl

theorem cell21_259664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 3, 5, 4].length) (baseStart_259664 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_259664 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_259664 prefixEnd_259664 := by exact prefixLift 259664
  have htrace : WordTrace (prefixWord ++ tailWord_259664) baseStart_259664 baseEnd_259664 := by
    simpa [prefixWord, tailWord_259664, baseEnd_259664] using wordTrace_append hprefix tailTrace_259664
  have hstable : (prefixWord ++ tailWord_259664).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_259664).length < 2 ^ (prefixWord ++ tailWord_259664).sum := by decide
  have hdescent : baseEnd_259664 < baseStart_259664 := by decide
  rcases family_descends (prefixWord ++ tailWord_259664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_259698 : List Nat := [3, 2, 1, 2, 3, 3, 1, 2, 4]
def baseStart_259698 : Nat := 118140960795 + 259698 * 2 ^ 59
def prefixEnd_259698 : Nat := 4983230072969 + 3 ^ 40 * 259698 * 2
def baseEnd_259698 : Nat := 59266621782857850702523

theorem tailTrace_259698 : CollatzResearch.WordTrace tailWord_259698 prefixEnd_259698 59266621782857850702523 := by
  unfold tailWord_259698
  simp only [CollatzResearch.WordTrace]
  refine ⟨2367991053291493433098937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6314642808777315821597165 2367991053291493433098937)
  ·
    refine ⟨1775993289968620074824203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2367991053291493433098937 1775993289968620074824203)
    ·
      refine ⟨2663989934952930112236305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1775993289968620074824203 2663989934952930112236305)
      ·
        refine ⟨1997992451214697584177229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2663989934952930112236305 1997992451214697584177229)
        ·
          refine ⟨749247169205511594066461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1997992451214697584177229 749247169205511594066461)
          ·
            refine ⟨280967688452066847774923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 749247169205511594066461 280967688452066847774923)
            ·
              refine ⟨421451532678100271662385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 280967688452066847774923 421451532678100271662385)
              ·
                refine ⟨316088649508575203746789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 421451532678100271662385 316088649508575203746789)
                ·
                  refine ⟨59266621782857850702523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 316088649508575203746789 59266621782857850702523)
                  ·
                    rfl

theorem cell21_259698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 3, 1, 2, 4].length) (baseStart_259698 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_259698 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_259698 prefixEnd_259698 := by exact prefixLift 259698
  have htrace : WordTrace (prefixWord ++ tailWord_259698) baseStart_259698 baseEnd_259698 := by
    simpa [prefixWord, tailWord_259698, baseEnd_259698] using wordTrace_append hprefix tailTrace_259698
  have hstable : (prefixWord ++ tailWord_259698).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_259698).length < 2 ^ (prefixWord ++ tailWord_259698).sum := by decide
  have hdescent : baseEnd_259698 < baseStart_259698 := by decide
  rcases family_descends (prefixWord ++ tailWord_259698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_259726 : List Nat := [4, 1, 1, 3, 1, 2, 2, 2, 5]
def baseStart_259726 : Nat := 118140960795 + 259726 * 2 ^ 59
def prefixEnd_259726 : Nat := 4983230072969 + 3 ^ 40 * 259726 * 2
def baseEnd_259726 : Nat := 59273011764336024235799

theorem tailTrace_259726 : CollatzResearch.WordTrace tailWord_259726 prefixEnd_259726 59273011764336024235799 := by
  unfold tailWord_259726
  simp only [CollatzResearch.WordTrace]
  refine ⟨1184123182133066814301879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 6315323638043023009610021 1184123182133066814301879)
  ·
    refine ⟨1776184773199600221452819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1184123182133066814301879 1776184773199600221452819)
    ·
      refine ⟨2664277159799400332179229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1776184773199600221452819 2664277159799400332179229)
      ·
        refine ⟨999103934924775124567211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2664277159799400332179229 999103934924775124567211)
        ·
          refine ⟨1498655902387162686850817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 999103934924775124567211 1498655902387162686850817)
          ·
            refine ⟨1123991926790372015138113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1498655902387162686850817 1123991926790372015138113)
            ·
              refine ⟨842993945092779011353585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1123991926790372015138113 842993945092779011353585)
              ·
                refine ⟨632245458819584258515189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 842993945092779011353585 632245458819584258515189)
                ·
                  refine ⟨59273011764336024235799, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 632245458819584258515189 59273011764336024235799)
                  ·
                    rfl

theorem cell21_259726_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 2, 2, 5].length) (baseStart_259726 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_259726 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_259726 prefixEnd_259726 := by exact prefixLift 259726
  have htrace : WordTrace (prefixWord ++ tailWord_259726) baseStart_259726 baseEnd_259726 := by
    simpa [prefixWord, tailWord_259726, baseEnd_259726] using wordTrace_append hprefix tailTrace_259726
  have hstable : (prefixWord ++ tailWord_259726).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_259726).length < 2 ^ (prefixWord ++ tailWord_259726).sum := by decide
  have hdescent : baseEnd_259726 < baseStart_259726 := by decide
  rcases family_descends (prefixWord ++ tailWord_259726) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_259757 : List Nat := [1, 5, 2, 1, 1, 1, 2, 4, 4]
def baseStart_259757 : Nat := 118140960795 + 259757 * 2 ^ 59
def prefixEnd_259757 : Nat := 4983230072969 + 3 ^ 40 * 259757 * 2
def baseEnd_259757 : Nat := 59280086386686859219069

theorem tailTrace_259757 : CollatzResearch.WordTrace tailWord_259757 prefixEnd_259757 59280086386686859219069 := by
  unfold tailWord_259757
  simp only [CollatzResearch.WordTrace]
  refine ⟨9474116119952226808793525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6316077413301484539195683 9474116119952226808793525)
  ·
    refine ⟨888198386245521263324393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 9474116119952226808793525 888198386245521263324393)
    ·
      refine ⟨666148789684140947493295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 888198386245521263324393 666148789684140947493295)
      ·
        refine ⟨999223184526211421239943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 666148789684140947493295 999223184526211421239943)
        ·
          refine ⟨1498834776789317131859915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 999223184526211421239943 1498834776789317131859915)
          ·
            refine ⟨2248252165183975697789873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1498834776789317131859915 2248252165183975697789873)
            ·
              refine ⟨1686189123887981773342405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2248252165183975697789873 1686189123887981773342405)
              ·
                refine ⟨316160460728996582501701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1686189123887981773342405 316160460728996582501701)
                ·
                  refine ⟨59280086386686859219069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 316160460728996582501701 59280086386686859219069)
                  ·
                    rfl

theorem cell21_259757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 2, 4, 4].length) (baseStart_259757 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_259757 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_259757 prefixEnd_259757 := by exact prefixLift 259757
  have htrace : WordTrace (prefixWord ++ tailWord_259757) baseStart_259757 baseEnd_259757 := by
    simpa [prefixWord, tailWord_259757, baseEnd_259757] using wordTrace_append hprefix tailTrace_259757
  have hstable : (prefixWord ++ tailWord_259757).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_259757).length < 2 ^ (prefixWord ++ tailWord_259757).sum := by decide
  have hdescent : baseEnd_259757 < baseStart_259757 := by decide
  rcases family_descends (prefixWord ++ tailWord_259757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_259774 : List Nat := [4, 2, 1, 1, 2, 2, 4, 1, 4]
def baseStart_259774 : Nat := 118140960795 + 259774 * 2 ^ 59
def prefixEnd_259774 : Nat := 4983230072969 + 3 ^ 40 * 259774 * 2
def baseEnd_259774 : Nat := 59283966018298607435701

theorem tailTrace_259774 : CollatzResearch.WordTrace tailWord_259774 prefixEnd_259774 59283966018298607435701 := by
  unfold tailWord_259774
  simp only [CollatzResearch.WordTrace]
  refine ⟨1184342020111329839020297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 6316490773927092474774917 1184342020111329839020297)
  ·
    refine ⟨888256515083497379265223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1184342020111329839020297 888256515083497379265223)
    ·
      refine ⟨1332384772625246068897835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 888256515083497379265223 1332384772625246068897835)
      ·
        refine ⟨1998577158937869103346753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1332384772625246068897835 1998577158937869103346753)
        ·
          refine ⟨1498932869203401827510065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1998577158937869103346753 1498932869203401827510065)
          ·
            refine ⟨1124199651902551370632549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1498932869203401827510065 1124199651902551370632549)
            ·
              refine ⟨210787434731728381993603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1124199651902551370632549 210787434731728381993603)
              ·
                refine ⟨316181152097592572990405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 210787434731728381993603 316181152097592572990405)
                ·
                  refine ⟨59283966018298607435701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 316181152097592572990405 59283966018298607435701)
                  ·
                    rfl

theorem cell21_259774_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 4, 1, 4].length) (baseStart_259774 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_259774 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_259774 prefixEnd_259774 := by exact prefixLift 259774
  have htrace : WordTrace (prefixWord ++ tailWord_259774) baseStart_259774 baseEnd_259774 := by
    simpa [prefixWord, tailWord_259774, baseEnd_259774] using wordTrace_append hprefix tailTrace_259774
  have hstable : (prefixWord ++ tailWord_259774).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_259774).length < 2 ^ (prefixWord ++ tailWord_259774).sum := by decide
  have hdescent : baseEnd_259774 < baseStart_259774 := by decide
  rcases family_descends (prefixWord ++ tailWord_259774) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_259819 : List Nat := [1, 1, 1, 1, 2, 4, 6, 2, 3]
def baseStart_259819 : Nat := 118140960795 + 259819 * 2 ^ 59
def prefixEnd_259819 : Nat := 4983230072969 + 3 ^ 40 * 259819 * 2
def baseEnd_259819 : Nat := 59294235631388529185609

theorem tailTrace_259819 : CollatzResearch.WordTrace tailWord_259819 prefixEnd_259819 59294235631388529185609 := by
  unfold tailWord_259819
  simp only [CollatzResearch.WordTrace]
  refine ⟨9476377445727611397550511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6317584963818407598367007 9476377445727611397550511)
  ·
    refine ⟨14214566168591417096325767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9476377445727611397550511 14214566168591417096325767)
    ·
      refine ⟨21321849252887125644488651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14214566168591417096325767 21321849252887125644488651)
      ·
        refine ⟨31982773879330688466732977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21321849252887125644488651 31982773879330688466732977)
        ·
          refine ⟨23987080409498016350049733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31982773879330688466732977 23987080409498016350049733)
          ·
            refine ⟨4497577576780878065634325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 23987080409498016350049733 4497577576780878065634325)
            ·
              refine ⟨210823948911603659326609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 4497577576780878065634325 210823948911603659326609)
              ·
                refine ⟨158117961683702744494957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 210823948911603659326609 158117961683702744494957)
                ·
                  refine ⟨59294235631388529185609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 158117961683702744494957 59294235631388529185609)
                  ·
                    rfl

theorem cell21_259819_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 6, 2, 3].length) (baseStart_259819 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_259819 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_259819 prefixEnd_259819 := by exact prefixLift 259819
  have htrace : WordTrace (prefixWord ++ tailWord_259819) baseStart_259819 baseEnd_259819 := by
    simpa [prefixWord, tailWord_259819, baseEnd_259819] using wordTrace_append hprefix tailTrace_259819
  have hstable : (prefixWord ++ tailWord_259819).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_259819).length < 2 ^ (prefixWord ++ tailWord_259819).sum := by decide
  have hdescent : baseEnd_259819 < baseStart_259819 := by decide
  rcases family_descends (prefixWord ++ tailWord_259819) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_259988 : List Nat := [2, 4, 2, 1, 1, 2, 4, 2, 3]
def baseStart_259988 : Nat := 118140960795 + 259988 * 2 ^ 59
def prefixEnd_259988 : Nat := 4983230072969 + 3 ^ 40 * 259988 * 2
def baseEnd_259988 : Nat := 59332803733881790868597

theorem tailTrace_259988 : CollatzResearch.WordTrace tailWord_259988 prefixEnd_259988 59332803733881790868597 := by
  unfold tailWord_259988
  simp only [CollatzResearch.WordTrace]
  refine ⟨4741270691057676630226309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6321694254743568840301745 4741270691057676630226309)
  ·
    refine ⟨888988254573314368167433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4741270691057676630226309 888988254573314368167433)
    ·
      refine ⟨666741190929985776125575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 888988254573314368167433 666741190929985776125575)
      ·
        refine ⟨1000111786394978664188363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 666741190929985776125575 1000111786394978664188363)
        ·
          refine ⟨1500167679592467996282545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1000111786394978664188363 1500167679592467996282545)
          ·
            refine ⟨1125125759694350997211909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1500167679592467996282545 1125125759694350997211909)
            ·
              refine ⟨210961079942690811977233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1125125759694350997211909 210961079942690811977233)
              ·
                refine ⟨158220809957018108982925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 210961079942690811977233 158220809957018108982925)
                ·
                  refine ⟨59332803733881790868597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 158220809957018108982925 59332803733881790868597)
                  ·
                    rfl

theorem cell21_259988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 4, 2, 3].length) (baseStart_259988 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_259988 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_259988 prefixEnd_259988 := by exact prefixLift 259988
  have htrace : WordTrace (prefixWord ++ tailWord_259988) baseStart_259988 baseEnd_259988 := by
    simpa [prefixWord, tailWord_259988, baseEnd_259988] using wordTrace_append hprefix tailTrace_259988
  have hstable : (prefixWord ++ tailWord_259988).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_259988).length < 2 ^ (prefixWord ++ tailWord_259988).sum := by decide
  have hdescent : baseEnd_259988 < baseStart_259988 := by decide
  rcases family_descends (prefixWord ++ tailWord_259988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_260044 : List Nat := [2, 2, 1, 4, 1, 3, 1, 1, 6]
def baseStart_260044 : Nat := 118140960795 + 260044 * 2 ^ 59
def prefixEnd_260044 : Nat := 4983230072969 + 3 ^ 40 * 260044 * 2
def baseEnd_260044 : Nat := 59345583696838137935149

theorem tailTrace_260044 : CollatzResearch.WordTrace tailWord_260044 prefixEnd_260044 59345583696838137935149 := by
  unfold tailWord_260044
  simp only [CollatzResearch.WordTrace]
  refine ⟨4742291934956237412245593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6323055913274983216327457 4742291934956237412245593)
  ·
    refine ⟨3556718951217178059184195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4742291934956237412245593 3556718951217178059184195)
    ·
      refine ⟨5335078426825767088776293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3556718951217178059184195 5335078426825767088776293)
      ·
        refine ⟨1000327205029831329145555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5335078426825767088776293 1000327205029831329145555)
        ·
          refine ⟨1500490807544746993718333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1000327205029831329145555 1500490807544746993718333)
          ·
            refine ⟨562684052829280122644375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1500490807544746993718333 562684052829280122644375)
            ·
              refine ⟨844026079243920183966563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 562684052829280122644375 844026079243920183966563)
              ·
                refine ⟨1266039118865880275949845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 844026079243920183966563 1266039118865880275949845)
                ·
                  refine ⟨59345583696838137935149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1266039118865880275949845 59345583696838137935149)
                  ·
                    rfl

theorem cell21_260044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 3, 1, 1, 6].length) (baseStart_260044 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_260044 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_260044 prefixEnd_260044 := by exact prefixLift 260044
  have htrace : WordTrace (prefixWord ++ tailWord_260044) baseStart_260044 baseEnd_260044 := by
    simpa [prefixWord, tailWord_260044, baseEnd_260044] using wordTrace_append hprefix tailTrace_260044
  have hstable : (prefixWord ++ tailWord_260044).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_260044).length < 2 ^ (prefixWord ++ tailWord_260044).sum := by decide
  have hdescent : baseEnd_260044 < baseStart_260044 := by decide
  rcases family_descends (prefixWord ++ tailWord_260044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_260120 : List Nat := [2, 1, 2, 3, 2, 1, 3, 3, 4]
def baseStart_260120 : Nat := 118140960795 + 260120 * 2 ^ 59
def prefixEnd_260120 : Nat := 4983230072969 + 3 ^ 40 * 260120 * 2
def baseEnd_260120 : Nat := 59362927932278894668327

theorem tailTrace_260120 : CollatzResearch.WordTrace tailWord_260120 prefixEnd_260120 59362927932278894668327 := by
  unfold tailWord_260120
  simp only [CollatzResearch.WordTrace]
  refine ⟨4743677908818569902128907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6324903878424759869505209 4743677908818569902128907)
  ·
    refine ⟨7115516863227854853193361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4743677908818569902128907 7115516863227854853193361)
    ·
      refine ⟨5336637647420891139895021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7115516863227854853193361 5336637647420891139895021)
      ·
        refine ⟨2001239117782834177460633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5336637647420891139895021 2001239117782834177460633)
        ·
          refine ⟨1500929338337125633095475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2001239117782834177460633 1500929338337125633095475)
          ·
            refine ⟨2251394007505688449643213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1500929338337125633095475 2251394007505688449643213)
            ·
              refine ⟨844272752814633168616205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2251394007505688449643213 844272752814633168616205)
              ·
                refine ⟨316602282305487438231077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 844272752814633168616205 316602282305487438231077)
                ·
                  refine ⟨59362927932278894668327, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 316602282305487438231077 59362927932278894668327)
                  ·
                    rfl

theorem cell21_260120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 3, 3, 4].length) (baseStart_260120 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_260120 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_260120 prefixEnd_260120 := by exact prefixLift 260120
  have htrace : WordTrace (prefixWord ++ tailWord_260120) baseStart_260120 baseEnd_260120 := by
    simpa [prefixWord, tailWord_260120, baseEnd_260120] using wordTrace_append hprefix tailTrace_260120
  have hstable : (prefixWord ++ tailWord_260120).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_260120).length < 2 ^ (prefixWord ++ tailWord_260120).sum := by decide
  have hdescent : baseEnd_260120 < baseStart_260120 := by decide
  rcases family_descends (prefixWord ++ tailWord_260120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_260210 : List Nat := [3, 2, 1, 2, 2, 3, 8]
def baseStart_260210 : Nat := 118140960795 + 260210 * 2 ^ 59
def prefixEnd_260210 : Nat := 4983230072969 + 3 ^ 40 * 260210 * 2
def baseEnd_260210 : Nat := 6598163017606526463127

theorem tailTrace_260210 : CollatzResearch.WordTrace tailWord_260210 prefixEnd_260210 6598163017606526463127 := by
  unfold tailWord_260210
  simp only [CollatzResearch.WordTrace]
  refine ⟨2372659596827771293758521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6327092258207390116689389 2372659596827771293758521)
  ·
    refine ⟨1779494697620828470318891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2372659596827771293758521 1779494697620828470318891)
    ·
      refine ⟨2669242046431242705478337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1779494697620828470318891 2669242046431242705478337)
      ·
        refine ⟨2001931534823432029108753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2669242046431242705478337 2001931534823432029108753)
        ·
          refine ⟨1501448651117574021831565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2001931534823432029108753 1501448651117574021831565)
          ·
            refine ⟨563043244169090258186837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1501448651117574021831565 563043244169090258186837)
            ·
              refine ⟨6598163017606526463127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 563043244169090258186837 6598163017606526463127)
              ·
                rfl

theorem cell21_260210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 3, 8].length) (baseStart_260210 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_260210 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_260210 prefixEnd_260210 := by exact prefixLift 260210
  have htrace : WordTrace (prefixWord ++ tailWord_260210) baseStart_260210 baseEnd_260210 := by
    simpa [prefixWord, tailWord_260210, baseEnd_260210] using wordTrace_append hprefix tailTrace_260210
  have hstable : (prefixWord ++ tailWord_260210).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_260210).length < 2 ^ (prefixWord ++ tailWord_260210).sum := by decide
  have hdescent : baseEnd_260210 < baseStart_260210 := by decide
  rcases family_descends (prefixWord ++ tailWord_260210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_260244 : List Nat := [2, 4, 2, 3, 1, 1, 1, 7]
def baseStart_260244 : Nat := 118140960795 + 260244 * 2 ^ 59
def prefixEnd_260244 : Nat := 4983230072969 + 3 ^ 40 * 260244 * 2
def baseEnd_260244 : Nat := 19797075473894078200469

theorem tailTrace_260244 : CollatzResearch.WordTrace tailWord_260244 prefixEnd_260244 19797075473894078200469 := by
  unfold tailWord_260244
  simp only [CollatzResearch.WordTrace]
  refine ⟨4745939234593954490885893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6327918979458605987847857 4745939234593954490885893)
  ·
    refine ⟨889863606486366467041105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4745939234593954490885893 889863606486366467041105)
    ·
      refine ⟨667397704864774850280829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 889863606486366467041105 667397704864774850280829)
      ·
        refine ⟨250274139324290568855311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 667397704864774850280829 250274139324290568855311)
        ·
          refine ⟨375411208986435853282967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 250274139324290568855311 375411208986435853282967)
          ·
            refine ⟨563116813479653779924451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 375411208986435853282967 563116813479653779924451)
            ·
              refine ⟨844675220219480669886677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 563116813479653779924451 844675220219480669886677)
              ·
                refine ⟨19797075473894078200469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 844675220219480669886677 19797075473894078200469)
                ·
                  rfl

theorem cell21_260244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 1, 1, 1, 7].length) (baseStart_260244 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_260244 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_260244 prefixEnd_260244 := by exact prefixLift 260244
  have htrace : WordTrace (prefixWord ++ tailWord_260244) baseStart_260244 baseEnd_260244 := by
    simpa [prefixWord, tailWord_260244, baseEnd_260244] using wordTrace_append hprefix tailTrace_260244
  have hstable : (prefixWord ++ tailWord_260244).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_260244).length < 2 ^ (prefixWord ++ tailWord_260244).sum := by decide
  have hdescent : baseEnd_260244 < baseStart_260244 := by decide
  rcases family_descends (prefixWord ++ tailWord_260244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_260345 : List Nat := [1, 2, 1, 3, 1, 1, 2, 10]
def baseStart_260345 : Nat := 118140960795 + 260345 * 2 ^ 59
def prefixEnd_260345 : Nat := 4983230072969 + 3 ^ 40 * 260345 * 2
def baseEnd_260345 : Nat := 19804758665909501139289

theorem tailTrace_260345 : CollatzResearch.WordTrace tailWord_260345 prefixEnd_260345 19804758665909501139289 := by
  unfold tailWord_260345
  simp only [CollatzResearch.WordTrace]
  refine ⟨9495562241822003231198489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6330374827881335487465659 9495562241822003231198489)
  ·
    refine ⟨7121671681366502423398867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9495562241822003231198489 7121671681366502423398867)
    ·
      refine ⟨10682507522049753635098301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7121671681366502423398867 10682507522049753635098301)
      ·
        refine ⟨4005940320768657613161863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10682507522049753635098301 4005940320768657613161863)
        ·
          refine ⟨6008910481152986419742795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4005940320768657613161863 6008910481152986419742795)
          ·
            refine ⟨9013365721729479629614193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6008910481152986419742795 9013365721729479629614193)
            ·
              refine ⟨6760024291297109722210645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9013365721729479629614193 6760024291297109722210645)
              ·
                refine ⟨19804758665909501139289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 6760024291297109722210645 19804758665909501139289)
                ·
                  rfl

theorem cell21_260345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 2, 10].length) (baseStart_260345 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_260345 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_260345 prefixEnd_260345 := by exact prefixLift 260345
  have htrace : WordTrace (prefixWord ++ tailWord_260345) baseStart_260345 baseEnd_260345 := by
    simpa [prefixWord, tailWord_260345, baseEnd_260345] using wordTrace_append hprefix tailTrace_260345
  have hstable : (prefixWord ++ tailWord_260345).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_260345).length < 2 ^ (prefixWord ++ tailWord_260345).sum := by decide
  have hdescent : baseEnd_260345 < baseStart_260345 := by decide
  rcases family_descends (prefixWord ++ tailWord_260345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_260348 : List Nat := [2, 2, 2, 1, 4, 1, 2, 3, 4]
def baseStart_260348 : Nat := 118140960795 + 260348 * 2 ^ 59
def prefixEnd_260348 : Nat := 4983230072969 + 3 ^ 40 * 260348 * 2
def baseEnd_260348 : Nat := 59414960638601164867861

theorem tailTrace_260348 : CollatzResearch.WordTrace tailWord_260348 prefixEnd_260348 59414960638601164867861 := by
  unfold tailWord_260348
  simp only [CollatzResearch.WordTrace]
  refine ⟨4747835830405567371778849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6330447773874089829038465 4747835830405567371778849)
  ·
    refine ⟨3560876872804175528834137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4747835830405567371778849 3560876872804175528834137)
    ·
      refine ⟨2670657654603131646625603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3560876872804175528834137 2670657654603131646625603)
      ·
        refine ⟨4005986481904697469938405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2670657654603131646625603 4005986481904697469938405)
        ·
          refine ⟨751122465357130775613451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4005986481904697469938405 751122465357130775613451)
          ·
            refine ⟨1126683698035696163420177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 751122465357130775613451 1126683698035696163420177)
            ·
              refine ⟨845012773526772122565133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1126683698035696163420177 845012773526772122565133)
              ·
                refine ⟨316879790072539545961925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 845012773526772122565133 316879790072539545961925)
                ·
                  refine ⟨59414960638601164867861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 316879790072539545961925 59414960638601164867861)
                  ·
                    rfl

theorem cell21_260348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 2, 3, 4].length) (baseStart_260348 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_260348 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_260348 prefixEnd_260348 := by exact prefixLift 260348
  have htrace : WordTrace (prefixWord ++ tailWord_260348) baseStart_260348 baseEnd_260348 := by
    simpa [prefixWord, tailWord_260348, baseEnd_260348] using wordTrace_append hprefix tailTrace_260348
  have hstable : (prefixWord ++ tailWord_260348).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_260348).length < 2 ^ (prefixWord ++ tailWord_260348).sum := by decide
  have hdescent : baseEnd_260348 < baseStart_260348 := by decide
  rcases family_descends (prefixWord ++ tailWord_260348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_260376 : List Nat := [2, 1, 2, 3, 1, 2, 1, 2, 7]
def baseStart_260376 : Nat := 118140960795 + 260376 * 2 ^ 59
def prefixEnd_260376 : Nat := 4983230072969 + 3 ^ 40 * 260376 * 2
def baseEnd_260376 : Nat := 59421350620079338401137

theorem tailTrace_260376 : CollatzResearch.WordTrace tailWord_260376 prefixEnd_260376 59421350620079338401137 := by
  unfold tailWord_260376
  simp only [CollatzResearch.WordTrace]
  refine ⟨4748346452354847762788491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6331128603139797017051321 4748346452354847762788491)
  ·
    refine ⟨7122519678532271644182737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4748346452354847762788491 7122519678532271644182737)
    ·
      refine ⟨5341889758899203733137053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7122519678532271644182737 5341889758899203733137053)
      ·
        refine ⟨2003208659587201399926395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5341889758899203733137053 2003208659587201399926395)
        ·
          refine ⟨3004812989380802099889593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2003208659587201399926395 3004812989380802099889593)
          ·
            refine ⟨2253609742035601574917195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3004812989380802099889593 2253609742035601574917195)
            ·
              refine ⟨3380414613053402362375793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2253609742035601574917195 3380414613053402362375793)
              ·
                refine ⟨2535310959790051771781845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3380414613053402362375793 2535310959790051771781845)
                ·
                  refine ⟨59421350620079338401137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2535310959790051771781845 59421350620079338401137)
                  ·
                    rfl

theorem cell21_260376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 1, 2, 7].length) (baseStart_260376 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_260376 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_260376 prefixEnd_260376 := by exact prefixLift 260376
  have htrace : WordTrace (prefixWord ++ tailWord_260376) baseStart_260376 baseEnd_260376 := by
    simpa [prefixWord, tailWord_260376, baseEnd_260376] using wordTrace_append hprefix tailTrace_260376
  have hstable : (prefixWord ++ tailWord_260376).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_260376).length < 2 ^ (prefixWord ++ tailWord_260376).sum := by decide
  have hdescent : baseEnd_260376 < baseStart_260376 := by decide
  rcases family_descends (prefixWord ++ tailWord_260376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_260382 : List Nat := [4, 3, 2, 1, 1, 1, 3, 2, 4]
def baseStart_260382 : Nat := 118140960795 + 260382 * 2 ^ 59
def prefixEnd_260382 : Nat := 4983230072969 + 3 ^ 40 * 260382 * 2
def baseEnd_260382 : Nat := 59422719901824661301125

theorem tailTrace_260382 : CollatzResearch.WordTrace tailWord_260382 prefixEnd_260382 59422719901824661301125 := by
  unfold tailWord_260382
  simp only [CollatzResearch.WordTrace]
  refine ⟨1187113967835994818786925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 6331274495125305700196933 1187113967835994818786925)
  ·
    refine ⟨445167737938498057045097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1187113967835994818786925 445167737938498057045097)
    ·
      refine ⟨333875803453873542783823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 445167737938498057045097 333875803453873542783823)
      ·
        refine ⟨500813705180810314175735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 333875803453873542783823 500813705180810314175735)
        ·
          refine ⟨751220557771215471263603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 500813705180810314175735 751220557771215471263603)
          ·
            refine ⟨1126830836656823206895405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 751220557771215471263603 1126830836656823206895405)
            ·
              refine ⟨422561563746308702585777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1126830836656823206895405 422561563746308702585777)
              ·
                refine ⟨316921172809731526939333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 422561563746308702585777 316921172809731526939333)
                ·
                  refine ⟨59422719901824661301125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 316921172809731526939333 59422719901824661301125)
                  ·
                    rfl

theorem cell21_260382_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 3, 2, 4].length) (baseStart_260382 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_260382 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_260382 prefixEnd_260382 := by exact prefixLift 260382
  have htrace : WordTrace (prefixWord ++ tailWord_260382) baseStart_260382 baseEnd_260382 := by
    simpa [prefixWord, tailWord_260382, baseEnd_260382] using wordTrace_append hprefix tailTrace_260382
  have hstable : (prefixWord ++ tailWord_260382).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_260382).length < 2 ^ (prefixWord ++ tailWord_260382).sum := by decide
  have hdescent : baseEnd_260382 < baseStart_260382 := by decide
  rcases family_descends (prefixWord ++ tailWord_260382) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_260407 : List Nat := [1, 1, 3, 1, 2, 1, 1, 7, 4]
def baseStart_260407 : Nat := 118140960795 + 260407 * 2 ^ 59
def prefixEnd_260407 : Nat := 4983230072969 + 3 ^ 40 * 260407 * 2
def baseEnd_260407 : Nat := 59428425242430173384407

theorem tailTrace_260407 : CollatzResearch.WordTrace tailWord_260407 prefixEnd_260407 59428425242430173384407 := by
  unfold tailWord_260407
  simp only [CollatzResearch.WordTrace]
  refine ⟨9497823567597387819955475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6331882378398258546636983 9497823567597387819955475)
  ·
    refine ⟨14246735351396081729933213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9497823567597387819955475 14246735351396081729933213)
    ·
      refine ⟨5342525756773530648724955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14246735351396081729933213 5342525756773530648724955)
      ·
        refine ⟨8013788635160295973087433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5342525756773530648724955 8013788635160295973087433)
        ·
          refine ⟨6010341476370221979815575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8013788635160295973087433 6010341476370221979815575)
          ·
            refine ⟨9015512214555332969723363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6010341476370221979815575 9015512214555332969723363)
            ·
              refine ⟨13523268321832999454585045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9015512214555332969723363 13523268321832999454585045)
              ·
                refine ⟨316951601292960924716837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 13523268321832999454585045 316951601292960924716837)
                ·
                  refine ⟨59428425242430173384407, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 316951601292960924716837 59428425242430173384407)
                  ·
                    rfl

theorem cell21_260407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 7, 4].length) (baseStart_260407 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_260407 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_260407 prefixEnd_260407 := by exact prefixLift 260407
  have htrace : WordTrace (prefixWord ++ tailWord_260407) baseStart_260407 baseEnd_260407 := by
    simpa [prefixWord, tailWord_260407, baseEnd_260407] using wordTrace_append hprefix tailTrace_260407
  have hstable : (prefixWord ++ tailWord_260407).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_260407).length < 2 ^ (prefixWord ++ tailWord_260407).sum := by decide
  have hdescent : baseEnd_260407 < baseStart_260407 := by decide
  rcases family_descends (prefixWord ++ tailWord_260407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_260444 : List Nat := [2, 2, 4, 3, 2, 1, 1, 1, 5]
def baseStart_260444 : Nat := 118140960795 + 260444 * 2 ^ 59
def prefixEnd_260444 : Nat := 4983230072969 + 3 ^ 40 * 260444 * 2
def baseEnd_260444 : Nat := 59436869146526331267665

theorem tailTrace_260444 : CollatzResearch.WordTrace tailWord_260444 prefixEnd_260444 59436869146526331267665 := by
  unfold tailWord_260444
  simp only [CollatzResearch.WordTrace]
  refine ⟨4749586534231671569526193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6332782045642228759368257 4749586534231671569526193)
  ·
    refine ⟨3562189900673753677144645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4749586534231671569526193 3562189900673753677144645)
    ·
      refine ⟨667910606376328814464621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3562189900673753677144645 667910606376328814464621)
      ·
        refine ⟨250466477391123305424233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 667910606376328814464621 250466477391123305424233)
        ·
          refine ⟨187849858043342479068175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 250466477391123305424233 187849858043342479068175)
          ·
            refine ⟨281774787065013718602263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 187849858043342479068175 281774787065013718602263)
            ·
              refine ⟨422662180597520577903395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 281774787065013718602263 422662180597520577903395)
              ·
                refine ⟨633993270896280866855093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 422662180597520577903395 633993270896280866855093)
                ·
                  refine ⟨59436869146526331267665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 633993270896280866855093 59436869146526331267665)
                  ·
                    rfl

theorem cell21_260444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 2, 1, 1, 1, 5].length) (baseStart_260444 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_260444 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_260444 prefixEnd_260444 := by exact prefixLift 260444
  have htrace : WordTrace (prefixWord ++ tailWord_260444) baseStart_260444 baseEnd_260444 := by
    simpa [prefixWord, tailWord_260444, baseEnd_260444] using wordTrace_append hprefix tailTrace_260444
  have hstable : (prefixWord ++ tailWord_260444).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_260444).length < 2 ^ (prefixWord ++ tailWord_260444).sum := by decide
  have hdescent : baseEnd_260444 < baseStart_260444 := by decide
  rcases family_descends (prefixWord ++ tailWord_260444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_260458 : List Nat := [3, 1, 3, 3, 1, 3, 2, 1, 4]
def baseStart_260458 : Nat := 118140960795 + 260458 * 2 ^ 59
def prefixEnd_260458 : Nat := 4983230072969 + 3 ^ 40 * 260458 * 2
def baseEnd_260458 : Nat := 59440064137265418034303

theorem tailTrace_260458 : CollatzResearch.WordTrace tailWord_260458 prefixEnd_260458 59440064137265418034303 := by
  unfold tailWord_260458
  simp only [CollatzResearch.WordTrace]
  refine ⟨2374920922603155882515507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6333122460275082353374685 2374920922603155882515507)
  ·
    refine ⟨3562381383904733823773261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2374920922603155882515507 3562381383904733823773261)
    ·
      refine ⟨1335893018964275183914973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3562381383904733823773261 1335893018964275183914973)
      ·
        refine ⟨500959882111603193968115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1335893018964275183914973 500959882111603193968115)
        ·
          refine ⟨751439823167404790952173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 500959882111603193968115 751439823167404790952173)
          ·
            refine ⟨281789933687776796607065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 751439823167404790952173 281789933687776796607065)
            ·
              refine ⟨211342450265832597455299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 281789933687776796607065 211342450265832597455299)
              ·
                refine ⟨317013675398748896182949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 211342450265832597455299 317013675398748896182949)
                ·
                  refine ⟨59440064137265418034303, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 317013675398748896182949 59440064137265418034303)
                  ·
                    rfl

theorem cell21_260458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 3, 2, 1, 4].length) (baseStart_260458 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_260458 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_260458 prefixEnd_260458 := by exact prefixLift 260458
  have htrace : WordTrace (prefixWord ++ tailWord_260458) baseStart_260458 baseEnd_260458 := by
    simpa [prefixWord, tailWord_260458, baseEnd_260458] using wordTrace_append hprefix tailTrace_260458
  have hstable : (prefixWord ++ tailWord_260458).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_260458).length < 2 ^ (prefixWord ++ tailWord_260458).sum := by decide
  have hdescent : baseEnd_260458 < baseStart_260458 := by decide
  rcases family_descends (prefixWord ++ tailWord_260458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_260576 : List Nat := [2, 1, 1, 3, 1, 1, 7, 1, 4]
def baseStart_260576 : Nat := 118140960795 + 260576 * 2 ^ 59
def prefixEnd_260576 : Nat := 4983230072969 + 3 ^ 40 * 260576 * 2
def baseEnd_260576 : Nat := 59466993344923435067395

theorem tailTrace_260576 : CollatzResearch.WordTrace tailWord_260576 prefixEnd_260576 59466993344923435067395 := by
  unfold tailWord_260576
  simp only [CollatzResearch.WordTrace]
  refine ⟨4751993751992564841428791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6335991669323419788571721 4751993751992564841428791)
  ·
    refine ⟨7127990627988847262143187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4751993751992564841428791 7127990627988847262143187)
    ·
      refine ⟨10691985941983270893214781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7127990627988847262143187 10691985941983270893214781)
      ·
        refine ⟨4009494728243726584955543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10691985941983270893214781 4009494728243726584955543)
        ·
          refine ⟨6014242092365589877433315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4009494728243726584955543 6014242092365589877433315)
          ·
            refine ⟨9021363138548384816149973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6014242092365589877433315 9021363138548384816149973)
            ·
              refine ⟨211438198559727769128515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 9021363138548384816149973 211438198559727769128515)
              ·
                refine ⟨317157297839591653692773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 211438198559727769128515 317157297839591653692773)
                ·
                  refine ⟨59466993344923435067395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 317157297839591653692773 59466993344923435067395)
                  ·
                    rfl

theorem cell21_260576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 7, 1, 4].length) (baseStart_260576 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_260576 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_260576 prefixEnd_260576 := by exact prefixLift 260576
  have htrace : WordTrace (prefixWord ++ tailWord_260576) baseStart_260576 baseEnd_260576 := by
    simpa [prefixWord, tailWord_260576, baseEnd_260576] using wordTrace_append hprefix tailTrace_260576
  have hstable : (prefixWord ++ tailWord_260576).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_260576).length < 2 ^ (prefixWord ++ tailWord_260576).sum := by decide
  have hdescent : baseEnd_260576 < baseStart_260576 := by decide
  rcases family_descends (prefixWord ++ tailWord_260576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_260590 : List Nat := [4, 1, 2, 1, 2, 3, 1, 7]
def baseStart_260590 : Nat := 118140960795 + 260590 * 2 ^ 59
def prefixEnd_260590 : Nat := 4983230072969 + 3 ^ 40 * 260590 * 2
def baseEnd_260590 : Nat := 19823396111887507278011

theorem tailTrace_260590 : CollatzResearch.WordTrace tailWord_260590 prefixEnd_260590 19823396111887507278011 := by
  unfold tailWord_260590
  simp only [CollatzResearch.WordTrace]
  refine ⟨1188062265741801259233403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 6336332083956273382578149 1188062265741801259233403)
  ·
    refine ⟨1782093398612701888850105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1188062265741801259233403 1782093398612701888850105)
    ·
      refine ⟨1336570048959526416637579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1782093398612701888850105 1336570048959526416637579)
      ·
        refine ⟨2004855073439289624956369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1336570048959526416637579 2004855073439289624956369)
        ·
          refine ⟨1503641305079467218717277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2004855073439289624956369 1503641305079467218717277)
          ·
            refine ⟨563865489404800207018979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1503641305079467218717277 563865489404800207018979)
            ·
              refine ⟨845798234107200310528469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 563865489404800207018979 845798234107200310528469)
              ·
                refine ⟨19823396111887507278011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 845798234107200310528469 19823396111887507278011)
                ·
                  rfl

theorem cell21_260590_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 3, 1, 7].length) (baseStart_260590 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_260590 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_260590 prefixEnd_260590 := by exact prefixLift 260590
  have htrace : WordTrace (prefixWord ++ tailWord_260590) baseStart_260590 baseEnd_260590 := by
    simpa [prefixWord, tailWord_260590, baseEnd_260590] using wordTrace_append hprefix tailTrace_260590
  have hstable : (prefixWord ++ tailWord_260590).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_260590).length < 2 ^ (prefixWord ++ tailWord_260590).sum := by decide
  have hdescent : baseEnd_260590 < baseStart_260590 := by decide
  rcases family_descends (prefixWord ++ tailWord_260590) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_260714 : List Nat := [3, 1, 3, 2, 1, 1, 4, 3, 3]
def baseStart_260714 : Nat := 118140960795 + 260714 * 2 ^ 59
def prefixEnd_260714 : Nat := 4983230072969 + 3 ^ 40 * 260714 * 2
def baseEnd_260714 : Nat := 59498486825065861767113

theorem tailTrace_260714 : CollatzResearch.WordTrace tailWord_260714 prefixEnd_260714 59498486825065861767113 := by
  unfold tailWord_260714
  simp only [CollatzResearch.WordTrace]
  refine ⟨2377255194371294812845299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6339347184990119500920797 2377255194371294812845299)
  ·
    refine ⟨3565882791556942219267949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2377255194371294812845299 3565882791556942219267949)
    ·
      refine ⟨1337206046833853332225481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3565882791556942219267949 1337206046833853332225481)
      ·
        refine ⟨1002904535125389999169111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1337206046833853332225481 1002904535125389999169111)
        ·
          refine ⟨1504356802688084998753667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1002904535125389999169111 1504356802688084998753667)
          ·
            refine ⟨2256535204032127498130501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1504356802688084998753667 2256535204032127498130501)
            ·
              refine ⟨423100350756023905899469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2256535204032127498130501 423100350756023905899469)
              ·
                refine ⟨158662631533508964712301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 423100350756023905899469 158662631533508964712301)
                ·
                  refine ⟨59498486825065861767113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 158662631533508964712301 59498486825065861767113)
                  ·
                    rfl

theorem cell21_260714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 4, 3, 3].length) (baseStart_260714 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_260714 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_260714 prefixEnd_260714 := by exact prefixLift 260714
  have htrace : WordTrace (prefixWord ++ tailWord_260714) baseStart_260714 baseEnd_260714 := by
    simpa [prefixWord, tailWord_260714, baseEnd_260714] using wordTrace_append hprefix tailTrace_260714
  have hstable : (prefixWord ++ tailWord_260714).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_260714).length < 2 ^ (prefixWord ++ tailWord_260714).sum := by decide
  have hdescent : baseEnd_260714 < baseStart_260714 := by decide
  rcases family_descends (prefixWord ++ tailWord_260714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_260804 : List Nat := [2, 3, 3, 1, 1, 3, 1, 3, 4]
def baseStart_260804 : Nat := 118140960795 + 260804 * 2 ^ 59
def prefixEnd_260804 : Nat := 4983230072969 + 3 ^ 40 * 260804 * 2
def baseEnd_260804 : Nat := 59519026051245705266929

theorem tailTrace_260804 : CollatzResearch.WordTrace tailWord_260804 prefixEnd_260804 59519026051245705266929 := by
  unfold tailWord_260804
  simp only [CollatzResearch.WordTrace]
  refine ⟨4756151673579562311078733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6341535564772749748104977 4756151673579562311078733)
  ·
    refine ⟨1783556877592335866654525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4756151673579562311078733 1783556877592335866654525)
    ·
      refine ⟨668833829097125949995447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1783556877592335866654525 668833829097125949995447)
      ·
        refine ⟨1003250743645688924993171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 668833829097125949995447 1003250743645688924993171)
        ·
          refine ⟨1504876115468533387489757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1003250743645688924993171 1504876115468533387489757)
          ·
            refine ⟨564328543300700020308659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1504876115468533387489757 564328543300700020308659)
            ·
              refine ⟨846492814951050030462989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 564328543300700020308659 846492814951050030462989)
              ·
                refine ⟨317434805606643761423621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 846492814951050030462989 317434805606643761423621)
                ·
                  refine ⟨59519026051245705266929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 317434805606643761423621 59519026051245705266929)
                  ·
                    rfl

theorem cell21_260804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 3, 1, 3, 4].length) (baseStart_260804 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_260804 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_260804 prefixEnd_260804 := by exact prefixLift 260804
  have htrace : WordTrace (prefixWord ++ tailWord_260804) baseStart_260804 baseEnd_260804 := by
    simpa [prefixWord, tailWord_260804, baseEnd_260804] using wordTrace_append hprefix tailTrace_260804
  have hstable : (prefixWord ++ tailWord_260804).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_260804).length < 2 ^ (prefixWord ++ tailWord_260804).sum := by decide
  have hdescent : baseEnd_260804 < baseStart_260804 := by decide
  rcases family_descends (prefixWord ++ tailWord_260804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_260849 : List Nat := [1, 2, 2, 2, 2, 2, 3, 4, 3]
def baseStart_260849 : Nat := 118140960795 + 260849 * 2 ^ 59
def prefixEnd_260849 : Nat := 4983230072969 + 3 ^ 40 * 260849 * 2
def baseEnd_260849 : Nat := 59529295664335627016837

theorem tailTrace_260849 : CollatzResearch.WordTrace tailWord_260849 prefixEnd_260849 59529295664335627016837 := by
  unfold tailWord_260849
  simp only [CollatzResearch.WordTrace]
  refine ⟨9513944631996097307545601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6342629754664064871697067 9513944631996097307545601)
  ·
    refine ⟨7135458473997072980659201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9513944631996097307545601 7135458473997072980659201)
    ·
      refine ⟨5351593855497804735494401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7135458473997072980659201 5351593855497804735494401)
      ·
        refine ⟨4013695391623353551620801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5351593855497804735494401 4013695391623353551620801)
        ·
          refine ⟨3010271543717515163715601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4013695391623353551620801 3010271543717515163715601)
          ·
            refine ⟨2257703657788136372786701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3010271543717515163715601 2257703657788136372786701)
            ·
              refine ⟨846638871670551139795013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2257703657788136372786701 846638871670551139795013)
              ·
                refine ⟨158744788438228338711565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 846638871670551139795013 158744788438228338711565)
                ·
                  refine ⟨59529295664335627016837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 158744788438228338711565 59529295664335627016837)
                  ·
                    rfl

theorem cell21_260849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 3, 4, 3].length) (baseStart_260849 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_260849 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_260849 prefixEnd_260849 := by exact prefixLift 260849
  have htrace : WordTrace (prefixWord ++ tailWord_260849) baseStart_260849 baseEnd_260849 := by
    simpa [prefixWord, tailWord_260849, baseEnd_260849] using wordTrace_append hprefix tailTrace_260849
  have hstable : (prefixWord ++ tailWord_260849).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_260849).length < 2 ^ (prefixWord ++ tailWord_260849).sum := by decide
  have hdescent : baseEnd_260849 < baseStart_260849 := by decide
  rcases family_descends (prefixWord ++ tailWord_260849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_260908 : List Nat := [2, 2, 1, 1, 1, 4, 4, 1, 5]
def baseStart_260908 : Nat := 118140960795 + 260908 * 2 ^ 59
def prefixEnd_260908 : Nat := 4983230072969 + 3 ^ 40 * 260908 * 2
def baseEnd_260908 : Nat := 59542760268164635533383

theorem tailTrace_260908 : CollatzResearch.WordTrace tailWord_260908 prefixEnd_260908 59542760268164635533383 := by
  unfold tailWord_260908
  simp only [CollatzResearch.WordTrace]
  refine ⟨4758048269391175191971689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6344064359188233589295585 4758048269391175191971689)
  ·
    refine ⟨3568536202043381393978767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4758048269391175191971689 3568536202043381393978767)
    ·
      refine ⟨5352804303065072090968151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3568536202043381393978767 5352804303065072090968151)
      ·
        refine ⟨8029206454597608136452227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5352804303065072090968151 8029206454597608136452227)
        ·
          refine ⟨12043809681896412204678341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8029206454597608136452227 12043809681896412204678341)
          ·
            refine ⟨2258214315355577288377189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 12043809681896412204678341 2258214315355577288377189)
            ·
              refine ⟨423415184129170741570723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2258214315355577288377189 423415184129170741570723)
              ·
                refine ⟨635122776193756112356085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 423415184129170741570723 635122776193756112356085)
                ·
                  refine ⟨59542760268164635533383, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 635122776193756112356085 59542760268164635533383)
                  ·
                    rfl

theorem cell21_260908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 5].length) (baseStart_260908 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_260908 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_260908 prefixEnd_260908 := by exact prefixLift 260908
  have htrace : WordTrace (prefixWord ++ tailWord_260908) baseStart_260908 baseEnd_260908 := by
    simpa [prefixWord, tailWord_260908, baseEnd_260908] using wordTrace_append hprefix tailTrace_260908
  have hstable : (prefixWord ++ tailWord_260908).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_260908).length < 2 ^ (prefixWord ++ tailWord_260908).sum := by decide
  have hdescent : baseEnd_260908 < baseStart_260908 := by decide
  rcases family_descends (prefixWord ++ tailWord_260908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_260953 : List Nat := [1, 2, 1, 2, 2, 6, 7]
def baseStart_260953 : Nat := 118140960795 + 260953 * 2 ^ 59
def prefixEnd_260953 : Nat := 4983230072969 + 3 ^ 40 * 260953 * 2
def baseEnd_260953 : Nat := 6617003320139395253699

theorem tailTrace_260953 : CollatzResearch.WordTrace tailWord_260953 prefixEnd_260953 6617003320139395253699 := by
  unfold tailWord_260953
  simp only [CollatzResearch.WordTrace]
  refine ⟨9517737823619323069331513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6345158549079548712887675 9517737823619323069331513)
  ·
    refine ⟨7138303367714492301998635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9517737823619323069331513 7138303367714492301998635)
    ·
      refine ⟨10707455051571738452997953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7138303367714492301998635 10707455051571738452997953)
      ·
        refine ⟨8030591288678803839748465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10707455051571738452997953 8030591288678803839748465)
        ·
          refine ⟨6022943466509102879811349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8030591288678803839748465 6022943466509102879811349)
          ·
            refine ⟨282325474992614197491157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 6022943466509102879811349 282325474992614197491157)
            ·
              refine ⟨6617003320139395253699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 282325474992614197491157 6617003320139395253699)
              ·
                rfl

theorem cell21_260953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 6, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 6, 7].length) (baseStart_260953 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_260953 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_260953 prefixEnd_260953 := by exact prefixLift 260953
  have htrace : WordTrace (prefixWord ++ tailWord_260953) baseStart_260953 baseEnd_260953 := by
    simpa [prefixWord, tailWord_260953, baseEnd_260953] using wordTrace_append hprefix tailTrace_260953
  have hstable : (prefixWord ++ tailWord_260953).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_260953).length < 2 ^ (prefixWord ++ tailWord_260953).sum := by decide
  have hdescent : baseEnd_260953 < baseStart_260953 := by decide
  rcases family_descends (prefixWord ++ tailWord_260953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_261015 : List Nat := [1, 1, 3, 3, 1, 2, 4, 2, 4]
def baseStart_261015 : Nat := 118140960795 + 261015 * 2 ^ 59
def prefixEnd_261015 : Nat := 4983230072969 + 3 ^ 40 * 261015 * 2
def baseEnd_261015 : Nat := 59567179125956227249831

theorem tailTrace_261015 : CollatzResearch.WordTrace tailWord_261015 prefixEnd_261015 59567179125956227249831 := by
  unfold tailWord_261015
  simp only [CollatzResearch.WordTrace]
  refine ⟨9519999149394707658088499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6346666099596471772058999 9519999149394707658088499)
  ·
    refine ⟨14279998724092061487132749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9519999149394707658088499 14279998724092061487132749)
    ·
      refine ⟨5354999521534523057674781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14279998724092061487132749 5354999521534523057674781)
      ·
        refine ⟨2008124820575446146628043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5354999521534523057674781 2008124820575446146628043)
        ·
          refine ⟨3012187230863169219942065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2008124820575446146628043 3012187230863169219942065)
          ·
            refine ⟨2259140423147376914956549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3012187230863169219942065 2259140423147376914956549)
            ·
              refine ⟨423588829340133171554353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2259140423147376914956549 423588829340133171554353)
              ·
                refine ⟨317691622005099878665765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 423588829340133171554353 317691622005099878665765)
                ·
                  refine ⟨59567179125956227249831, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 317691622005099878665765 59567179125956227249831)
                  ·
                    rfl

theorem cell21_261015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 4, 2, 4].length) (baseStart_261015 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_261015 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_261015 prefixEnd_261015 := by exact prefixLift 261015
  have htrace : WordTrace (prefixWord ++ tailWord_261015) baseStart_261015 baseEnd_261015 := by
    simpa [prefixWord, tailWord_261015, baseEnd_261015] using wordTrace_append hprefix tailTrace_261015
  have hstable : (prefixWord ++ tailWord_261015).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_261015).length < 2 ^ (prefixWord ++ tailWord_261015).sum := by decide
  have hdescent : baseEnd_261015 < baseStart_261015 := by decide
  rcases family_descends (prefixWord ++ tailWord_261015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_261018 : List Nat := [3, 1, 1, 4, 3, 1, 1, 4, 3]
def baseStart_261018 : Nat := 118140960795 + 261018 * 2 ^ 59
def prefixEnd_261018 : Nat := 4983230072969 + 3 ^ 40 * 261018 * 2
def baseEnd_261018 : Nat := 59567863766828888699825

theorem tailTrace_261018 : CollatzResearch.WordTrace tailWord_261018 prefixEnd_261018 59567863766828888699825 := by
  unfold tailWord_261018
  simp only [CollatzResearch.WordTrace]
  refine ⟨2380027142095959792611927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6346739045589226113631805 2380027142095959792611927)
  ·
    refine ⟨3570040713143939688917891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2380027142095959792611927 3570040713143939688917891)
    ·
      refine ⟨5355061069715909533376837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3570040713143939688917891 5355061069715909533376837)
      ·
        refine ⟨1004073950571733037508157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5355061069715909533376837 1004073950571733037508157)
        ·
          refine ⟨376527731464399889065559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1004073950571733037508157 376527731464399889065559)
          ·
            refine ⟨564791597196599833598339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 376527731464399889065559 564791597196599833598339)
            ·
              refine ⟨847187395794899750397509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 564791597196599833598339 847187395794899750397509)
              ·
                refine ⟨158847636711543703199533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 847187395794899750397509 158847636711543703199533)
                ·
                  refine ⟨59567863766828888699825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 158847636711543703199533 59567863766828888699825)
                  ·
                    rfl

theorem cell21_261018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 3, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 3, 1, 1, 4, 3].length) (baseStart_261018 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_261018 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_261018 prefixEnd_261018 := by exact prefixLift 261018
  have htrace : WordTrace (prefixWord ++ tailWord_261018) baseStart_261018 baseEnd_261018 := by
    simpa [prefixWord, tailWord_261018, baseEnd_261018] using wordTrace_append hprefix tailTrace_261018
  have hstable : (prefixWord ++ tailWord_261018).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_261018).length < 2 ^ (prefixWord ++ tailWord_261018).sum := by decide
  have hdescent : baseEnd_261018 < baseStart_261018 := by decide
  rcases family_descends (prefixWord ++ tailWord_261018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_261077 : List Nat := [1, 3, 2, 3, 3, 1, 2, 1, 5]
def baseStart_261077 : Nat := 118140960795 + 261077 * 2 ^ 59
def prefixEnd_261077 : Nat := 4983230072969 + 3 ^ 40 * 261077 * 2
def baseEnd_261077 : Nat := 59581328370657897216371

theorem tailTrace_261077 : CollatzResearch.WordTrace tailWord_261077 prefixEnd_261077 59581328370657897216371 := by
  unfold tailWord_261077
  simp only [CollatzResearch.WordTrace]
  refine ⟨9522260475170092246845485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6348173650113394831230323 9522260475170092246845485)
  ·
    refine ⟨3570847678188784592567057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9522260475170092246845485 3570847678188784592567057)
    ·
      refine ⟨2678135758641588444425293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3570847678188784592567057 2678135758641588444425293)
      ·
        refine ⟨1004300909490595666659485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2678135758641588444425293 1004300909490595666659485)
        ·
          refine ⟨376612841058973374997307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1004300909490595666659485 376612841058973374997307)
          ·
            refine ⟨564919261588460062495961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 376612841058973374997307 564919261588460062495961)
            ·
              refine ⟨423689446191345046871971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 564919261588460062495961 423689446191345046871971)
              ·
                refine ⟨635534169287017570307957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 423689446191345046871971 635534169287017570307957)
                ·
                  refine ⟨59581328370657897216371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 635534169287017570307957 59581328370657897216371)
                  ·
                    rfl

theorem cell21_261077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 3, 1, 2, 1, 5].length) (baseStart_261077 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_261077 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_261077 prefixEnd_261077 := by exact prefixLift 261077
  have htrace : WordTrace (prefixWord ++ tailWord_261077) baseStart_261077 baseEnd_261077 := by
    simpa [prefixWord, tailWord_261077, baseEnd_261077] using wordTrace_append hprefix tailTrace_261077
  have hstable : (prefixWord ++ tailWord_261077).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_261077).length < 2 ^ (prefixWord ++ tailWord_261077).sum := by decide
  have hdescent : baseEnd_261077 < baseStart_261077 := by decide
  rcases family_descends (prefixWord ++ tailWord_261077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_261105 : List Nat := [1, 2, 2, 2, 4, 2, 1, 7]
def baseStart_261105 : Nat := 118140960795 + 261105 * 2 ^ 59
def prefixEnd_261105 : Nat := 4983230072969 + 3 ^ 40 * 261105 * 2
def baseEnd_261105 : Nat := 19862572784045356916549

theorem tailTrace_261105 : CollatzResearch.WordTrace tailWord_261105 prefixEnd_261105 19862572784045356916549 := by
  unfold tailWord_261105
  simp only [CollatzResearch.WordTrace]
  refine ⟨9523281719068653028864769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6348854479379102019243179 9523281719068653028864769)
  ·
    refine ⟨7142461289301489771648577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9523281719068653028864769 7142461289301489771648577)
    ·
      refine ⟨5356845966976117328736433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7142461289301489771648577 5356845966976117328736433)
      ·
        refine ⟨4017634475232087996552325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5356845966976117328736433 4017634475232087996552325)
        ·
          refine ⟨753306464106016499353561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4017634475232087996552325 753306464106016499353561)
          ·
            refine ⟨564979848079512374515171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 753306464106016499353561 564979848079512374515171)
            ·
              refine ⟨847469772119268561772757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 564979848079512374515171 847469772119268561772757)
              ·
                refine ⟨19862572784045356916549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 847469772119268561772757 19862572784045356916549)
                ·
                  rfl

theorem cell21_261105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 2, 1, 7].length) (baseStart_261105 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_261105 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_261105 prefixEnd_261105 := by exact prefixLift 261105
  have htrace : WordTrace (prefixWord ++ tailWord_261105) baseStart_261105 baseEnd_261105 := by
    simpa [prefixWord, tailWord_261105, baseEnd_261105] using wordTrace_append hprefix tailTrace_261105
  have hstable : (prefixWord ++ tailWord_261105).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_261105).length < 2 ^ (prefixWord ++ tailWord_261105).sum := by decide
  have hdescent : baseEnd_261105 < baseStart_261105 := by decide
  rcases family_descends (prefixWord ++ tailWord_261105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_261164 : List Nat := [2, 2, 1, 1, 1, 2, 3, 9]
def baseStart_261164 : Nat := 118140960795 + 261164 * 2 ^ 59
def prefixEnd_261164 : Nat := 4983230072969 + 3 ^ 40 * 261164 * 2
def baseEnd_261164 : Nat := 19867060985321693088731

theorem tailTrace_261164 : CollatzResearch.WordTrace tailWord_261164 prefixEnd_261164 19867060985321693088731 := by
  unfold tailWord_261164
  simp only [CollatzResearch.WordTrace]
  refine ⟨4762716812927453052631273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6350289083903270736841697 4762716812927453052631273)
  ·
    refine ⟨3572037609695589789473455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4762716812927453052631273 3572037609695589789473455)
    ·
      refine ⟨5358056414543384684210183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3572037609695589789473455 5358056414543384684210183)
      ·
        refine ⟨8037084621815077026315275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5358056414543384684210183 8037084621815077026315275)
        ·
          refine ⟨12055626932722615539472913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8037084621815077026315275 12055626932722615539472913)
          ·
            refine ⟨9041720199541961654604685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12055626932722615539472913 9041720199541961654604685)
            ·
              refine ⟨3390645074828235620476757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9041720199541961654604685 3390645074828235620476757)
              ·
                refine ⟨19867060985321693088731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 3390645074828235620476757 19867060985321693088731)
                ·
                  rfl

theorem cell21_261164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 3, 9].length) (baseStart_261164 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_261164 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_261164 prefixEnd_261164 := by exact prefixLift 261164
  have htrace : WordTrace (prefixWord ++ tailWord_261164) baseStart_261164 baseEnd_261164 := by
    simpa [prefixWord, tailWord_261164, baseEnd_261164] using wordTrace_append hprefix tailTrace_261164
  have hstable : (prefixWord ++ tailWord_261164).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_261164).length < 2 ^ (prefixWord ++ tailWord_261164).sum := by decide
  have hdescent : baseEnd_261164 < baseStart_261164 := by decide
  rcases family_descends (prefixWord ++ tailWord_261164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_261212 : List Nat := [2, 2, 4, 1, 1, 1, 3, 2, 5]
def baseStart_261212 : Nat := 118140960795 + 261212 * 2 ^ 59
def prefixEnd_261212 : Nat := 4983230072969 + 3 ^ 40 * 261212 * 2
def baseEnd_261212 : Nat := 59612137209927662466095

theorem tailTrace_261212 : CollatzResearch.WordTrace tailWord_261212 prefixEnd_261212 59612137209927662466095 := by
  unfold tailWord_261212
  simp only [CollatzResearch.WordTrace]
  refine ⟨4763592164840505151504945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6351456219787340202006593 4763592164840505151504945)
  ·
    refine ⟨3572694123630378863628709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4763592164840505151504945 3572694123630378863628709)
    ·
      refine ⟨669880148180696036930383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3572694123630378863628709 669880148180696036930383)
      ·
        refine ⟨1004820222271044055395575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 669880148180696036930383 1004820222271044055395575)
        ·
          refine ⟨1507230333406566083093363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1004820222271044055395575 1507230333406566083093363)
          ·
            refine ⟨2260845500109849124640045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1507230333406566083093363 2260845500109849124640045)
            ·
              refine ⟨847817062541193421740017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2260845500109849124640045 847817062541193421740017)
              ·
                refine ⟨635862796905895066305013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 847817062541193421740017 635862796905895066305013)
                ·
                  refine ⟨59612137209927662466095, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 635862796905895066305013 59612137209927662466095)
                  ·
                    rfl

theorem cell21_261212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 3, 2, 5].length) (baseStart_261212 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_261212 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_261212 prefixEnd_261212 := by exact prefixLift 261212
  have htrace : WordTrace (prefixWord ++ tailWord_261212) baseStart_261212 baseEnd_261212 := by
    simpa [prefixWord, tailWord_261212, baseEnd_261212] using wordTrace_append hprefix tailTrace_261212
  have hstable : (prefixWord ++ tailWord_261212).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_261212).length < 2 ^ (prefixWord ++ tailWord_261212).sum := by decide
  have hdescent : baseEnd_261212 < baseStart_261212 := by decide
  rcases family_descends (prefixWord ++ tailWord_261212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_261229 : List Nat := [1, 5, 1, 1, 2, 2, 1, 5, 3]
def baseStart_261229 : Nat := 118140960795 + 261229 * 2 ^ 59
def prefixEnd_261229 : Nat := 4983230072969 + 3 ^ 40 * 261229 * 2
def baseEnd_261229 : Nat := 59616016841539410682727

theorem tailTrace_261229 : CollatzResearch.WordTrace tailWord_261229 prefixEnd_261229 59616016841539410682727 := by
  unfold tailWord_261229
  simp only [CollatzResearch.WordTrace]
  refine ⟨9527804370619422206378741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6351869580412948137585827 9527804370619422206378741)
  ·
    refine ⟨893231659745570831848007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 9527804370619422206378741 893231659745570831848007)
    ·
      refine ⟨1339847489618356247772011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 893231659745570831848007 1339847489618356247772011)
      ·
        refine ⟨2009771234427534371658017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1339847489618356247772011 2009771234427534371658017)
        ·
          refine ⟨1507328425820650778743513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2009771234427534371658017 1507328425820650778743513)
          ·
            refine ⟨1130496319365488084057635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1507328425820650778743513 1130496319365488084057635)
            ·
              refine ⟨1695744479048232126086453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1130496319365488084057635 1695744479048232126086453)
              ·
                refine ⟨158976044910771761820605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1695744479048232126086453 158976044910771761820605)
                ·
                  refine ⟨59616016841539410682727, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 158976044910771761820605 59616016841539410682727)
                  ·
                    rfl

theorem cell21_261229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 1, 5, 3].length) (baseStart_261229 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_261229 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_261229 prefixEnd_261229 := by exact prefixLift 261229
  have htrace : WordTrace (prefixWord ++ tailWord_261229) baseStart_261229 baseEnd_261229 := by
    simpa [prefixWord, tailWord_261229, baseEnd_261229] using wordTrace_append hprefix tailTrace_261229
  have hstable : (prefixWord ++ tailWord_261229).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_261229).length < 2 ^ (prefixWord ++ tailWord_261229).sum := by decide
  have hdescent : baseEnd_261229 < baseStart_261229 := by decide
  rcases family_descends (prefixWord ++ tailWord_261229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_261274 : List Nat := [3, 1, 1, 5, 1, 1, 4, 5]
def baseStart_261274 : Nat := 118140960795 + 261274 * 2 ^ 59
def prefixEnd_261274 : Nat := 4983230072969 + 3 ^ 40 * 261274 * 2
def baseEnd_261274 : Nat := 19875428818209777477545

theorem tailTrace_261274 : CollatzResearch.WordTrace tailWord_261274 prefixEnd_261274 19875428818209777477545 := by
  unfold tailWord_261274
  simp only [CollatzResearch.WordTrace]
  refine ⟨2382361413864098722941719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6352963770304263261177917 2382361413864098722941719)
  ·
    refine ⟨3573542120796148084412579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2382361413864098722941719 3573542120796148084412579)
    ·
      refine ⟨5360313181194222126618869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3573542120796148084412579 5360313181194222126618869)
      ·
        refine ⟨502529360736958324370519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 5360313181194222126618869 502529360736958324370519)
        ·
          refine ⟨753794041105437486555779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 502529360736958324370519 753794041105437486555779)
          ·
            refine ⟨1130691061658156229833669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 753794041105437486555779 1130691061658156229833669)
            ·
              refine ⟨212004574060904293093813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1130691061658156229833669 212004574060904293093813)
              ·
                refine ⟨19875428818209777477545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 212004574060904293093813 19875428818209777477545)
                ·
                  rfl

theorem cell21_261274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 4, 5].length) (baseStart_261274 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_261274 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_261274 prefixEnd_261274 := by exact prefixLift 261274
  have htrace : WordTrace (prefixWord ++ tailWord_261274) baseStart_261274 baseEnd_261274 := by
    simpa [prefixWord, tailWord_261274, baseEnd_261274] using wordTrace_append hprefix tailTrace_261274
  have hstable : (prefixWord ++ tailWord_261274).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_261274).length < 2 ^ (prefixWord ++ tailWord_261274).sum := by decide
  have hdescent : baseEnd_261274 < baseStart_261274 := by decide
  rcases family_descends (prefixWord ++ tailWord_261274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_261333 : List Nat := [1, 3, 2, 4, 1, 1, 2, 7]
def baseStart_261333 : Nat := 118140960795 + 261333 * 2 ^ 59
def prefixEnd_261333 : Nat := 4983230072969 + 3 ^ 40 * 261333 * 2
def baseEnd_261333 : Nat := 19879917019486113649727

theorem tailTrace_261333 : CollatzResearch.WordTrace tailWord_261333 prefixEnd_261333 19879917019486113649727 := by
  unfold tailWord_261333
  simp only [CollatzResearch.WordTrace]
  refine ⟨9531597562242647968164653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6354398374828431978776435 9531597562242647968164653)
  ·
    refine ⟨3574349085840992988061745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9531597562242647968164653 3574349085840992988061745)
    ·
      refine ⟨2680761814380744741046309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3574349085840992988061745 2680761814380744741046309)
      ·
        refine ⟨502642840196389638946183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2680761814380744741046309 502642840196389638946183)
        ·
          refine ⟨753964260294584458419275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 502642840196389638946183 753964260294584458419275)
          ·
            refine ⟨1130946390441876687628913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 753964260294584458419275 1130946390441876687628913)
            ·
              refine ⟨848209792831407515721685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1130946390441876687628913 848209792831407515721685)
              ·
                refine ⟨19879917019486113649727, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 848209792831407515721685 19879917019486113649727)
                ·
                  rfl

theorem cell21_261333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 2, 7].length) (baseStart_261333 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_261333 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_261333 prefixEnd_261333 := by exact prefixLift 261333
  have htrace : WordTrace (prefixWord ++ tailWord_261333) baseStart_261333 baseEnd_261333 := by
    simpa [prefixWord, tailWord_261333, baseEnd_261333] using wordTrace_append hprefix tailTrace_261333
  have hstable : (prefixWord ++ tailWord_261333).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_261333).length < 2 ^ (prefixWord ++ tailWord_261333).sum := by decide
  have hdescent : baseEnd_261333 < baseStart_261333 := by decide
  rcases family_descends (prefixWord ++ tailWord_261333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_261474 : List Nat := [3, 3, 2, 1, 1, 1, 5, 2, 3]
def baseStart_261474 : Nat := 118140960795 + 261474 * 2 ^ 59
def prefixEnd_261474 : Nat := 4983230072969 + 3 ^ 40 * 261474 * 2
def baseEnd_261474 : Nat := 59671929179473429098893

theorem tailTrace_261474 : CollatzResearch.WordTrace tailWord_261474 prefixEnd_261474 59671929179473429098893 := by
  unfold tailWord_261474
  simp only [CollatzResearch.WordTrace]
  refine ⟨2384185063682957262261869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6357826836487886032698317 2384185063682957262261869)
  ·
    refine ⟨894069398881108973348201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2384185063682957262261869 894069398881108973348201)
    ·
      refine ⟨670552049160831730011151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 894069398881108973348201 670552049160831730011151)
      ·
        refine ⟨1005828073741247595016727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 670552049160831730011151 1005828073741247595016727)
        ·
          refine ⟨1508742110611871392525091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1005828073741247595016727 1508742110611871392525091)
          ·
            refine ⟨2263113165917807088787637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1508742110611871392525091 2263113165917807088787637)
            ·
              refine ⟨212166859304794414573841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 2263113165917807088787637 212166859304794414573841)
              ·
                refine ⟨159125144478595810930381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 212166859304794414573841 159125144478595810930381)
                ·
                  refine ⟨59671929179473429098893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 159125144478595810930381 59671929179473429098893)
                  ·
                    rfl

theorem cell21_261474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 5, 2, 3].length) (baseStart_261474 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_261474 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_261474 prefixEnd_261474 := by exact prefixLift 261474
  have htrace : WordTrace (prefixWord ++ tailWord_261474) baseStart_261474 baseEnd_261474 := by
    simpa [prefixWord, tailWord_261474, baseEnd_261474] using wordTrace_append hprefix tailTrace_261474
  have hstable : (prefixWord ++ tailWord_261474).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_261474).length < 2 ^ (prefixWord ++ tailWord_261474).sum := by decide
  have hdescent : baseEnd_261474 < baseStart_261474 := by decide
  rcases family_descends (prefixWord ++ tailWord_261474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_261485 : List Nat := [1, 5, 1, 1, 1, 4, 2, 6]
def baseStart_261485 : Nat := 118140960795 + 261485 * 2 ^ 59
def prefixEnd_261485 : Nat := 4983230072969 + 3 ^ 40 * 261485 * 2
def baseEnd_261485 : Nat := 19891479843113284805179

theorem tailTrace_261485 : CollatzResearch.WordTrace tailWord_261485 prefixEnd_261485 19891479843113284805179 := by
  unfold tailWord_261485
  simp only [CollatzResearch.WordTrace]
  refine ⟨9537141457691977927697909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6358094305127985285131939 9537141457691977927697909)
  ·
    refine ⟨894107011658622930721679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 9537141457691977927697909 894107011658622930721679)
    ·
      refine ⟨1341160517487934396082519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 894107011658622930721679 1341160517487934396082519)
      ·
        refine ⟨2011740776231901594123779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1341160517487934396082519 2011740776231901594123779)
        ·
          refine ⟨3017611164347852391185669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2011740776231901594123779 3017611164347852391185669)
          ·
            refine ⟨565802093315222323347313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3017611164347852391185669 565802093315222323347313)
            ·
              refine ⟨424351569986416742510485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 565802093315222323347313 424351569986416742510485)
              ·
                refine ⟨19891479843113284805179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 424351569986416742510485 19891479843113284805179)
                ·
                  rfl

theorem cell21_261485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 4, 2, 6].length) (baseStart_261485 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_261485 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_261485 prefixEnd_261485 := by exact prefixLift 261485
  have htrace : WordTrace (prefixWord ++ tailWord_261485) baseStart_261485 baseEnd_261485 := by
    simpa [prefixWord, tailWord_261485, baseEnd_261485] using wordTrace_append hprefix tailTrace_261485
  have hstable : (prefixWord ++ tailWord_261485).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_261485).length < 2 ^ (prefixWord ++ tailWord_261485).sum := by decide
  have hdescent : baseEnd_261485 < baseStart_261485 := by decide
  rcases family_descends (prefixWord ++ tailWord_261485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_261516 : List Nat := [2, 2, 1, 2, 1, 3, 2, 5, 3]
def baseStart_261516 : Nat := 118140960795 + 261516 * 2 ^ 59
def prefixEnd_261516 : Nat := 4983230072969 + 3 ^ 40 * 261516 * 2
def baseEnd_261516 : Nat := 59681514151690689398807

theorem tailTrace_261516 : CollatzResearch.WordTrace tailWord_261516 prefixEnd_261516 59681514151690689398807 := by
  unfold tailWord_261516
  simp only [CollatzResearch.WordTrace]
  refine ⟨4769136060289835111038201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6358848080386446814717601 4769136060289835111038201)
  ·
    refine ⟨3576852045217376333278651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4769136060289835111038201 3576852045217376333278651)
    ·
      refine ⟨5365278067826064499917977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3576852045217376333278651 5365278067826064499917977)
      ·
        refine ⟨4023958550869548374938483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5365278067826064499917977 4023958550869548374938483)
        ·
          refine ⟨6035937826304322562407725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4023958550869548374938483 6035937826304322562407725)
          ·
            refine ⟨2263476684864120960902897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6035937826304322562407725 2263476684864120960902897)
            ·
              refine ⟨1697607513648090720677173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2263476684864120960902897 1697607513648090720677173)
              ·
                refine ⟨159150704404508505063485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1697607513648090720677173 159150704404508505063485)
                ·
                  refine ⟨59681514151690689398807, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 159150704404508505063485 59681514151690689398807)
                  ·
                    rfl

theorem cell21_261516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 2, 5, 3].length) (baseStart_261516 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_261516 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_261516 prefixEnd_261516 := by exact prefixLift 261516
  have htrace : WordTrace (prefixWord ++ tailWord_261516) baseStart_261516 baseEnd_261516 := by
    simpa [prefixWord, tailWord_261516, baseEnd_261516] using wordTrace_append hprefix tailTrace_261516
  have hstable : (prefixWord ++ tailWord_261516).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_261516).length < 2 ^ (prefixWord ++ tailWord_261516).sum := by decide
  have hdescent : baseEnd_261516 < baseStart_261516 := by decide
  rcases family_descends (prefixWord ++ tailWord_261516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_261533 : List Nat := [1, 4, 2, 1, 3, 2, 1, 4, 3]
def baseStart_261533 : Nat := 118140960795 + 261533 * 2 ^ 59
def prefixEnd_261533 : Nat := 4983230072969 + 3 ^ 40 * 261533 * 2
def baseEnd_261533 : Nat := 59685393783302437615439

theorem tailTrace_261533 : CollatzResearch.WordTrace tailWord_261533 prefixEnd_261533 59685393783302437615439 := by
  unfold tailWord_261533
  simp only [CollatzResearch.WordTrace]
  refine ⟨9538892161518082125445253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6359261441012054750296835 9538892161518082125445253)
  ·
    refine ⟨1788542280284640398520985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 9538892161518082125445253 1788542280284640398520985)
    ·
      refine ⟨1341406710213480298890739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1788542280284640398520985 1341406710213480298890739)
      ·
        refine ⟨2012110065320220448336109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1341406710213480298890739 2012110065320220448336109)
        ·
          refine ⟨754541274495082668126041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2012110065320220448336109 754541274495082668126041)
          ·
            refine ⟨565905955871312001094531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 754541274495082668126041 565905955871312001094531)
            ·
              refine ⟨848858933806968001641797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 565905955871312001094531 848858933806968001641797)
              ·
                refine ⟨159161050088806500307837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 848858933806968001641797 159161050088806500307837)
                ·
                  refine ⟨59685393783302437615439, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 159161050088806500307837 59685393783302437615439)
                  ·
                    rfl

theorem cell21_261533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 2, 1, 4, 3].length) (baseStart_261533 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_261533 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_261533 prefixEnd_261533 := by exact prefixLift 261533
  have htrace : WordTrace (prefixWord ++ tailWord_261533) baseStart_261533 baseEnd_261533 := by
    simpa [prefixWord, tailWord_261533, baseEnd_261533] using wordTrace_append hprefix tailTrace_261533
  have hstable : (prefixWord ++ tailWord_261533).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_261533).length < 2 ^ (prefixWord ++ tailWord_261533).sum := by decide
  have hdescent : baseEnd_261533 < baseStart_261533 := by decide
  rcases family_descends (prefixWord ++ tailWord_261533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_261592 : List Nat := [2, 1, 2, 2, 2, 1, 4, 4, 3]
def baseStart_261592 : Nat := 118140960795 + 261592 * 2 ^ 59
def prefixEnd_261592 : Nat := 4983230072969 + 3 ^ 40 * 261592 * 2
def baseEnd_261592 : Nat := 59698858387131446131985

theorem tailTrace_261592 : CollatzResearch.WordTrace tailWord_261592 prefixEnd_261592 59698858387131446131985 := by
  unfold tailWord_261592
  simp only [CollatzResearch.WordTrace]
  refine ⟨4770522034152167600921515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6360696045536223467895353 4770522034152167600921515)
  ·
    refine ⟨7155783051228251401382273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4770522034152167600921515 7155783051228251401382273)
    ·
      refine ⟨5366837288421188551036705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7155783051228251401382273 5366837288421188551036705)
      ·
        refine ⟨4025127966315891413277529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5366837288421188551036705 4025127966315891413277529)
        ·
          refine ⟨3018845974736918559958147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4025127966315891413277529 3018845974736918559958147)
          ·
            refine ⟨4528268962105377839937221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3018845974736918559958147 4528268962105377839937221)
            ·
              refine ⟨849050430394758344988229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4528268962105377839937221 849050430394758344988229)
              ·
                refine ⟨159196955699017189685293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 849050430394758344988229 159196955699017189685293)
                ·
                  refine ⟨59698858387131446131985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 159196955699017189685293 59698858387131446131985)
                  ·
                    rfl

theorem cell21_261592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 4, 4, 3].length) (baseStart_261592 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_261592 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_261592 prefixEnd_261592 := by exact prefixLift 261592
  have htrace : WordTrace (prefixWord ++ tailWord_261592) baseStart_261592 baseEnd_261592 := by
    simpa [prefixWord, tailWord_261592, baseEnd_261592] using wordTrace_append hprefix tailTrace_261592
  have hstable : (prefixWord ++ tailWord_261592).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_261592).length < 2 ^ (prefixWord ++ tailWord_261592).sum := by decide
  have hdescent : baseEnd_261592 < baseStart_261592 := by decide
  rcases family_descends (prefixWord ++ tailWord_261592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_261651 : List Nat := [1, 1, 1, 2, 1, 6, 3, 1, 5]
def baseStart_261651 : Nat := 118140960795 + 261651 * 2 ^ 59
def prefixEnd_261651 : Nat := 4983230072969 + 3 ^ 40 * 261651 * 2
def baseEnd_261651 : Nat := 59712322990960454648531

theorem tailTrace_261651 : CollatzResearch.WordTrace tailWord_261651 prefixEnd_261651 59712322990960454648531 := by
  unfold tailWord_261651
  simp only [CollatzResearch.WordTrace]
  refine ⟨9543195975090588278240807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6362130650060392185493871 9543195975090588278240807)
  ·
    refine ⟨14314793962635882417361211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9543195975090588278240807 14314793962635882417361211)
    ·
      refine ⟨21472190943953823626041817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14314793962635882417361211 21472190943953823626041817)
      ·
        refine ⟨16104143207965367719531363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21472190943953823626041817 16104143207965367719531363)
        ·
          refine ⟨24156214811948051579297045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16104143207965367719531363 24156214811948051579297045)
          ·
            refine ⟨1132322569310064917779549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 24156214811948051579297045 1132322569310064917779549)
            ·
              refine ⟨424620963491274344167331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1132322569310064917779549 424620963491274344167331)
              ·
                refine ⟨636931445236911516250997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 424620963491274344167331 636931445236911516250997)
                ·
                  refine ⟨59712322990960454648531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 636931445236911516250997 59712322990960454648531)
                  ·
                    rfl

theorem cell21_261651_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 3, 1, 5].length) (baseStart_261651 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_261651 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_261651 prefixEnd_261651 := by exact prefixLift 261651
  have htrace : WordTrace (prefixWord ++ tailWord_261651) baseStart_261651 baseEnd_261651 := by
    simpa [prefixWord, tailWord_261651, baseEnd_261651] using wordTrace_append hprefix tailTrace_261651
  have hstable : (prefixWord ++ tailWord_261651).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_261651).length < 2 ^ (prefixWord ++ tailWord_261651).sum := by decide
  have hdescent : baseEnd_261651 < baseStart_261651 := by decide
  rcases family_descends (prefixWord ++ tailWord_261651) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_261744 : List Nat := [2, 1, 1, 1, 6, 1, 1, 5, 3]
def baseStart_261744 : Nat := 118140960795 + 261744 * 2 ^ 59
def prefixEnd_261744 : Nat := 4983230072969 + 3 ^ 40 * 261744 * 2
def baseEnd_261744 : Nat := 59733546858012959598341

theorem tailTrace_261744 : CollatzResearch.WordTrace tailWord_261744 prefixEnd_261744 59733546858012959598341 := by
  unfold tailWord_261744
  simp only [CollatzResearch.WordTrace]
  refine ⟨4773293981876832580688143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6364391975835776774250857 4773293981876832580688143)
  ·
    refine ⟨7159940972815248871032215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4773293981876832580688143 7159940972815248871032215)
    ·
      refine ⟨10739911459222873306548323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7159940972815248871032215 10739911459222873306548323)
      ·
        refine ⟨16109867188834309959822485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10739911459222873306548323 16109867188834309959822485)
        ·
          refine ⟨755150024476608279366679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 16109867188834309959822485 755150024476608279366679)
          ·
            refine ⟨1132725036714912419050019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 755150024476608279366679 1132725036714912419050019)
            ·
              refine ⟨1699087555072368628575029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1132725036714912419050019 1699087555072368628575029)
              ·
                refine ⟨159289458288034558928909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1699087555072368628575029 159289458288034558928909)
                ·
                  refine ⟨59733546858012959598341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 159289458288034558928909 59733546858012959598341)
                  ·
                    rfl

theorem cell21_261744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 1, 5, 3].length) (baseStart_261744 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_261744 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_261744 prefixEnd_261744 := by exact prefixLift 261744
  have htrace : WordTrace (prefixWord ++ tailWord_261744) baseStart_261744 baseEnd_261744 := by
    simpa [prefixWord, tailWord_261744, baseEnd_261744] using wordTrace_append hprefix tailTrace_261744
  have hstable : (prefixWord ++ tailWord_261744).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_261744).length < 2 ^ (prefixWord ++ tailWord_261744).sum := by decide
  have hdescent : baseEnd_261744 < baseStart_261744 := by decide
  rcases family_descends (prefixWord ++ tailWord_261744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_261755 : List Nat := [1, 1, 1, 1, 1, 4, 12]
def baseStart_261755 : Nat := 118140960795 + 261755 * 2 ^ 59
def prefixEnd_261755 : Nat := 4983230072969 + 3 ^ 40 * 261755 * 2
def baseEnd_261755 : Nat := 6637339689764376101665

theorem tailTrace_261755 : CollatzResearch.WordTrace tailWord_261755 prefixEnd_261755 6637339689764376101665 := by
  unfold tailWord_261755
  simp only [CollatzResearch.WordTrace]
  refine ⟨9546989166713814040026719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6364659444475876026684479 9546989166713814040026719)
  ·
    refine ⟨14320483750070721060040079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9546989166713814040026719 14320483750070721060040079)
    ·
      refine ⟨21480725625106081590060119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14320483750070721060040079 21480725625106081590060119)
      ·
        refine ⟨32221088437659122385090179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21480725625106081590060119 32221088437659122385090179)
        ·
          refine ⟨48331632656488683577635269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32221088437659122385090179 48331632656488683577635269)
          ·
            refine ⟨9062181123091628170806613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 48331632656488683577635269 9062181123091628170806613)
            ·
              refine ⟨6637339689764376101665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 12 9062181123091628170806613 6637339689764376101665)
              ·
                rfl

theorem cell21_261755_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 12].length) (baseStart_261755 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_261755 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_261755 prefixEnd_261755 := by exact prefixLift 261755
  have htrace : WordTrace (prefixWord ++ tailWord_261755) baseStart_261755 baseEnd_261755 := by
    simpa [prefixWord, tailWord_261755, baseEnd_261755] using wordTrace_append hprefix tailTrace_261755
  have hstable : (prefixWord ++ tailWord_261755).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_261755).length < 2 ^ (prefixWord ++ tailWord_261755).sum := by decide
  have hdescent : baseEnd_261755 < baseStart_261755 := by decide
  rcases family_descends (prefixWord ++ tailWord_261755) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_261806 : List Nat := [4, 1, 4, 1, 2, 2, 7]
def baseStart_261806 : Nat := 118140960795 + 261806 * 2 ^ 59
def prefixEnd_261806 : Nat := 4983230072969 + 3 ^ 40 * 261806 * 2
def baseEnd_261806 : Nat := 6638632900301625507209

theorem tailTrace_261806 : CollatzResearch.WordTrace tailWord_261806 prefixEnd_261806 6638632900301625507209 := by
  unfold tailWord_261806
  simp only [CollatzResearch.WordTrace]
  refine ⟨1193606161191131218766659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 6365899526352699833422181 1193606161191131218766659)
  ·
    refine ⟨1790409241786696828149989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1193606161191131218766659 1790409241786696828149989)
    ·
      refine ⟨335701732835005655278123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1790409241786696828149989 335701732835005655278123)
      ·
        refine ⟨503552599252508482917185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 335701732835005655278123 503552599252508482917185)
        ·
          refine ⟨377664449439381362187889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 503552599252508482917185 377664449439381362187889)
          ·
            refine ⟨283248337079536021640917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 377664449439381362187889 283248337079536021640917)
            ·
              refine ⟨6638632900301625507209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 283248337079536021640917 6638632900301625507209)
              ·
                rfl

theorem cell21_261806_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 2, 2, 7].length) (baseStart_261806 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_261806 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_261806 prefixEnd_261806 := by exact prefixLift 261806
  have htrace : WordTrace (prefixWord ++ tailWord_261806) baseStart_261806 baseEnd_261806 := by
    simpa [prefixWord, tailWord_261806, baseEnd_261806] using wordTrace_append hprefix tailTrace_261806
  have hstable : (prefixWord ++ tailWord_261806).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_261806).length < 2 ^ (prefixWord ++ tailWord_261806).sum := by decide
  have hdescent : baseEnd_261806 < baseStart_261806 := by decide
  rcases family_descends (prefixWord ++ tailWord_261806) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_261817 : List Nat := [1, 2, 1, 4, 1, 1, 4, 1, 6]
def baseStart_261817 : Nat := 118140960795 + 261817 * 2 ^ 59
def prefixEnd_261817 : Nat := 4983230072969 + 3 ^ 40 * 261817 * 2
def baseEnd_261817 : Nat := 59750206452581054881525

theorem tailTrace_261817 : CollatzResearch.WordTrace tailWord_261817 prefixEnd_261817 59750206452581054881525 := by
  unfold tailWord_261817
  simp only [CollatzResearch.WordTrace]
  refine ⟨9549250492489198628783705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6366166994992799085855803 9549250492489198628783705)
  ·
    refine ⟨7161937869366898971587779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9549250492489198628783705 7161937869366898971587779)
    ·
      refine ⟨10742906804050348457381669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7161937869366898971587779 10742906804050348457381669)
      ·
        refine ⟨2014295025759440335759063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10742906804050348457381669 2014295025759440335759063)
        ·
          refine ⟨3021442538639160503638595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2014295025759440335759063 3021442538639160503638595)
          ·
            refine ⟨4532163807958740755457893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3021442538639160503638595 4532163807958740755457893)
            ·
              refine ⟨849780713992263891648355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4532163807958740755457893 849780713992263891648355)
              ·
                refine ⟨1274671070988395837472533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 849780713992263891648355 1274671070988395837472533)
                ·
                  refine ⟨59750206452581054881525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1274671070988395837472533 59750206452581054881525)
                  ·
                    rfl

theorem cell21_261817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 4, 1, 6].length) (baseStart_261817 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_261817 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_261817 prefixEnd_261817 := by exact prefixLift 261817
  have htrace : WordTrace (prefixWord ++ tailWord_261817) baseStart_261817 baseEnd_261817 := by
    simpa [prefixWord, tailWord_261817, baseEnd_261817] using wordTrace_append hprefix tailTrace_261817
  have hstable : (prefixWord ++ tailWord_261817).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_261817).length < 2 ^ (prefixWord ++ tailWord_261817).sum := by decide
  have hdescent : baseEnd_261817 < baseStart_261817 := by decide
  rcases family_descends (prefixWord ++ tailWord_261817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_261820 : List Nat := [2, 2, 2, 3, 1, 4, 1, 1, 5]
def baseStart_261820 : Nat := 118140960795 + 261820 * 2 ^ 59
def prefixEnd_261820 : Nat := 4983230072969 + 3 ^ 40 * 261820 * 2
def baseEnd_261820 : Nat := 59750891093453716331519

theorem tailTrace_261820 : CollatzResearch.WordTrace tailWord_261820 prefixEnd_261820 59750891093453716331519 := by
  unfold tailWord_261820
  simp only [CollatzResearch.WordTrace]
  refine ⟨4774679955739165070571457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6366239940985553427428609 4774679955739165070571457)
  ·
    refine ⟨3581009966804373802928593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4774679955739165070571457 3581009966804373802928593)
    ·
      refine ⟨2685757475103280352196445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3581009966804373802928593 2685757475103280352196445)
      ·
        refine ⟨1007159053163730132073667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2685757475103280352196445 1007159053163730132073667)
        ·
          refine ⟨1510738579745595198110501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1007159053163730132073667 1510738579745595198110501)
          ·
            refine ⟨283263483702299099645719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1510738579745595198110501 283263483702299099645719)
            ·
              refine ⟨424895225553448649468579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 283263483702299099645719 424895225553448649468579)
              ·
                refine ⟨637342838330172974202869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 424895225553448649468579 637342838330172974202869)
                ·
                  refine ⟨59750891093453716331519, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 637342838330172974202869 59750891093453716331519)
                  ·
                    rfl

theorem cell21_261820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 4, 1, 1, 5].length) (baseStart_261820 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_261820 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_261820 prefixEnd_261820 := by exact prefixLift 261820
  have htrace : WordTrace (prefixWord ++ tailWord_261820) baseStart_261820 baseEnd_261820 := by
    simpa [prefixWord, tailWord_261820, baseEnd_261820] using wordTrace_append hprefix tailTrace_261820
  have hstable : (prefixWord ++ tailWord_261820).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_261820).length < 2 ^ (prefixWord ++ tailWord_261820).sum := by decide
  have hdescent : baseEnd_261820 < baseStart_261820 := by decide
  rcases family_descends (prefixWord ++ tailWord_261820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_261924 : List Nat := [2, 3, 1, 3, 2, 2, 8]
def baseStart_261924 : Nat := 118140960795 + 261924 * 2 ^ 59
def prefixEnd_261924 : Nat := 4983230072969 + 3 ^ 40 * 261924 * 2
def baseEnd_261924 : Nat := 6641625034485849621997

theorem tailTrace_261924 : CollatzResearch.WordTrace tailWord_261924 prefixEnd_261924 6641625034485849621997 := by
  unfold tailWord_261924
  simp only [CollatzResearch.WordTrace]
  refine ⟨4776576551550777951464413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6368768735401037268619217 4776576551550777951464413)
  ·
    refine ⟨1791216206831541731799155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4776576551550777951464413 1791216206831541731799155)
    ·
      refine ⟨2686824310247312597698733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1791216206831541731799155 2686824310247312597698733)
      ·
        refine ⟨1007559116342742224137025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2686824310247312597698733 1007559116342742224137025)
        ·
          refine ⟨755669337257056668102769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1007559116342742224137025 755669337257056668102769)
          ·
            refine ⟨566752002942792501077077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 755669337257056668102769 566752002942792501077077)
            ·
              refine ⟨6641625034485849621997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 566752002942792501077077 6641625034485849621997)
              ·
                rfl

theorem cell21_261924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 2, 8].length) (baseStart_261924 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_261924 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_261924 prefixEnd_261924 := by exact prefixLift 261924
  have htrace : WordTrace (prefixWord ++ tailWord_261924) baseStart_261924 baseEnd_261924 := by
    simpa [prefixWord, tailWord_261924, baseEnd_261924] using wordTrace_append hprefix tailTrace_261924
  have hstable : (prefixWord ++ tailWord_261924).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_261924).length < 2 ^ (prefixWord ++ tailWord_261924).sum := by decide
  have hdescent : baseEnd_261924 < baseStart_261924 := by decide
  rcases family_descends (prefixWord ++ tailWord_261924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_261958 : List Nat := [6, 1, 1, 2, 1, 2, 1, 7]
def baseStart_261958 : Nat := 118140960795 + 261958 * 2 ^ 59
def prefixEnd_261958 : Nat := 4983230072969 + 3 ^ 40 * 261958 * 2
def baseEnd_261958 : Nat := 19927461524532047677079

theorem tailTrace_261958 : CollatzResearch.WordTrace tailWord_261958 prefixEnd_261958 19927461524532047677079 := by
  unfold tailWord_261958
  simp only [CollatzResearch.WordTrace]
  refine ⟨298574787030574365927079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 6369595456652253139777685 298574787030574365927079)
  ·
    refine ⟨447862180545861548890619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 298574787030574365927079 447862180545861548890619)
    ·
      refine ⟨671793270818792323335929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 447862180545861548890619 671793270818792323335929)
      ·
        refine ⟨503844953114094242501947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 671793270818792323335929 503844953114094242501947)
        ·
          refine ⟨755767429671141363752921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 503844953114094242501947 755767429671141363752921)
          ·
            refine ⟨566825572253356022814691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 755767429671141363752921 566825572253356022814691)
            ·
              refine ⟨850238358380034034222037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 566825572253356022814691 850238358380034034222037)
              ·
                refine ⟨19927461524532047677079, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 850238358380034034222037 19927461524532047677079)
                ·
                  rfl

theorem cell21_261958_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 2, 1, 7].length) (baseStart_261958 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_261958 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_261958 prefixEnd_261958 := by exact prefixLift 261958
  have htrace : WordTrace (prefixWord ++ tailWord_261958) baseStart_261958 baseEnd_261958 := by
    simpa [prefixWord, tailWord_261958, baseEnd_261958] using wordTrace_append hprefix tailTrace_261958
  have hstable : (prefixWord ++ tailWord_261958).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_261958).length < 2 ^ (prefixWord ++ tailWord_261958).sum := by decide
  have hdescent : baseEnd_261958 < baseStart_261958 := by decide
  rcases family_descends (prefixWord ++ tailWord_261958) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_261969 : List Nat := [1, 2, 2, 1, 5, 1, 1, 2, 6]
def baseStart_261969 : Nat := 118140960795 + 261969 * 2 ^ 59
def prefixEnd_261969 : Nat := 4983230072969 + 3 ^ 40 * 261969 * 2
def baseEnd_261969 : Nat := 59784894923462568347881

theorem tailTrace_261969 : CollatzResearch.WordTrace tailWord_261969 prefixEnd_261969 59784894923462568347881 := by
  unfold tailWord_261969
  simp only [CollatzResearch.WordTrace]
  refine ⟨9554794387938528588316961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6369862925292352392211307 9554794387938528588316961)
  ·
    refine ⟨7166095790953896441237721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9554794387938528588316961 7166095790953896441237721)
    ·
      refine ⟨5374571843215422330928291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7166095790953896441237721 5374571843215422330928291)
      ·
        refine ⟨8061857764823133496392437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5374571843215422330928291 8061857764823133496392437)
        ·
          refine ⟨755799165452168765286791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 8061857764823133496392437 755799165452168765286791)
          ·
            refine ⟨1133698748178253147930187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 755799165452168765286791 1133698748178253147930187)
            ·
              refine ⟨1700548122267379721895281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1133698748178253147930187 1700548122267379721895281)
              ·
                refine ⟨1275411091700534791421461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1700548122267379721895281 1275411091700534791421461)
                ·
                  refine ⟨59784894923462568347881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1275411091700534791421461 59784894923462568347881)
                  ·
                    rfl

theorem cell21_261969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 1, 2, 6].length) (baseStart_261969 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_261969 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_261969 prefixEnd_261969 := by exact prefixLift 261969
  have htrace : WordTrace (prefixWord ++ tailWord_261969) baseStart_261969 baseEnd_261969 := by
    simpa [prefixWord, tailWord_261969, baseEnd_261969] using wordTrace_append hprefix tailTrace_261969
  have hstable : (prefixWord ++ tailWord_261969).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_261969).length < 2 ^ (prefixWord ++ tailWord_261969).sum := by decide
  have hdescent : baseEnd_261969 < baseStart_261969 := by decide
  rcases family_descends (prefixWord ++ tailWord_261969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_261983 : List Nat := [1, 1, 2, 3, 1, 4, 9]
def baseStart_261983 : Nat := 118140960795 + 261983 * 2 ^ 59
def prefixEnd_261983 : Nat := 4983230072969 + 3 ^ 40 * 261983 * 2
def baseEnd_261983 : Nat := 6643121101577961679391

theorem tailTrace_261983 : CollatzResearch.WordTrace tailWord_261983 prefixEnd_261983 6643121101577961679391 := by
  unfold tailWord_261983
  simp only [CollatzResearch.WordTrace]
  refine ⟨9555305009887808979326603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6370203339925205986217735 9555305009887808979326603)
  ·
    refine ⟨14332957514831713468989905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9555305009887808979326603 14332957514831713468989905)
    ·
      refine ⟨10749718136123785101742429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14332957514831713468989905 10749718136123785101742429)
      ·
        refine ⟨4031144301046419413153411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10749718136123785101742429 4031144301046419413153411)
        ·
          refine ⟨6046716451569629119730117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4031144301046419413153411 6046716451569629119730117)
          ·
            refine ⟨1133759334669305459949397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6046716451569629119730117 1133759334669305459949397)
            ·
              refine ⟨6643121101577961679391, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 1133759334669305459949397 6643121101577961679391)
              ·
                rfl

theorem cell21_261983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 9].length) (baseStart_261983 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_261983 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_261983 prefixEnd_261983 := by exact prefixLift 261983
  have htrace : WordTrace (prefixWord ++ tailWord_261983) baseStart_261983 baseEnd_261983 := by
    simpa [prefixWord, tailWord_261983, baseEnd_261983] using wordTrace_append hprefix tailTrace_261983
  have hstable : (prefixWord ++ tailWord_261983).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_261983).length < 2 ^ (prefixWord ++ tailWord_261983).sum := by decide
  have hdescent : baseEnd_261983 < baseStart_261983 := by decide
  rcases family_descends (prefixWord ++ tailWord_261983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_261986 : List Nat := [3, 3, 2, 1, 2, 1, 2, 1, 6]
def baseStart_261986 : Nat := 118140960795 + 261986 * 2 ^ 59
def prefixEnd_261986 : Nat := 4983230072969 + 3 ^ 40 * 261986 * 2
def baseEnd_261986 : Nat := 59788774555074316564513

theorem tailTrace_261986 : CollatzResearch.WordTrace tailWord_261986 prefixEnd_261986 59788774555074316564513 := by
  unfold tailWord_261986
  simp only [CollatzResearch.WordTrace]
  refine ⟨2388853607219235122921453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6370276285917960327790541 2388853607219235122921453)
  ·
    refine ⟨895820102707213171095545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2388853607219235122921453 895820102707213171095545)
    ·
      refine ⟨671865077030409878321659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 895820102707213171095545 671865077030409878321659)
      ·
        refine ⟨1007797615545614817482489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 671865077030409878321659 1007797615545614817482489)
        ·
          refine ⟨755848211659211113111867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1007797615545614817482489 755848211659211113111867)
          ·
            refine ⟨1133772317488816669667801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 755848211659211113111867 1133772317488816669667801)
            ·
              refine ⟨850329238116612502250851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1133772317488816669667801 850329238116612502250851)
              ·
                refine ⟨1275493857174918753376277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 850329238116612502250851 1275493857174918753376277)
                ·
                  refine ⟨59788774555074316564513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1275493857174918753376277 59788774555074316564513)
                  ·
                    rfl

theorem cell21_261986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 2, 1, 6].length) (baseStart_261986 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_261986 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_261986 prefixEnd_261986 := by exact prefixLift 261986
  have htrace : WordTrace (prefixWord ++ tailWord_261986) baseStart_261986 baseEnd_261986 := by
    simpa [prefixWord, tailWord_261986, baseEnd_261986] using wordTrace_append hprefix tailTrace_261986
  have hstable : (prefixWord ++ tailWord_261986).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_261986).length < 2 ^ (prefixWord ++ tailWord_261986).sum := by decide
  have hdescent : baseEnd_261986 < baseStart_261986 := by decide
  rcases family_descends (prefixWord ++ tailWord_261986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_262304 : List Nat := [2, 1, 1, 4, 2, 2, 4, 5]
def baseStart_262304 : Nat := 118140960795 + 262304 * 2 ^ 59
def prefixEnd_262304 : Nat := 4983230072969 + 3 ^ 40 * 262304 * 2
def baseEnd_262304 : Nat := 19953782162525476754621

theorem tailTrace_262304 : CollatzResearch.WordTrace tailWord_262304 prefixEnd_262304 19953782162525476754621 := by
  unfold tailWord_262304
  simp only [CollatzResearch.WordTrace]
  refine ⟨4783506420862440400880983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6378008561149920534507977 4783506420862440400880983)
  ·
    refine ⟨7175259631293660601321475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4783506420862440400880983 7175259631293660601321475)
    ·
      refine ⟨10762889446940490901982213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7175259631293660601321475 10762889446940490901982213)
      ·
        refine ⟨2018041771301342044121665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10762889446940490901982213 2018041771301342044121665)
        ·
          refine ⟨1513531328476006533091249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2018041771301342044121665 1513531328476006533091249)
          ·
            refine ⟨1135148496357004899818437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1513531328476006533091249 1135148496357004899818437)
            ·
              refine ⟨212840343066938418715957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1135148496357004899818437 212840343066938418715957)
              ·
                refine ⟨19953782162525476754621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 212840343066938418715957 19953782162525476754621)
                ·
                  rfl

theorem cell21_262304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 4, 5].length) (baseStart_262304 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_262304 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_262304 prefixEnd_262304 := by exact prefixLift 262304
  have htrace : WordTrace (prefixWord ++ tailWord_262304) baseStart_262304 baseEnd_262304 := by
    simpa [prefixWord, tailWord_262304, baseEnd_262304] using wordTrace_append hprefix tailTrace_262304
  have hstable : (prefixWord ++ tailWord_262304).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_262304).length < 2 ^ (prefixWord ++ tailWord_262304).sum := by decide
  have hdescent : baseEnd_262304 < baseStart_262304 := by decide
  rcases family_descends (prefixWord ++ tailWord_262304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_262321 : List Nat := [1, 2, 2, 5, 3, 1, 7]
def baseStart_262321 : Nat := 118140960795 + 262321 * 2 ^ 59
def prefixEnd_262321 : Nat := 4983230072969 + 3 ^ 40 * 262321 * 2
def baseEnd_262321 : Nat := 6651691791020908720055

theorem tailTrace_262321 : CollatzResearch.WordTrace tailWord_262321 prefixEnd_262321 6651691791020908720055 := by
  unfold tailWord_262321
  simp only [CollatzResearch.WordTrace]
  refine ⟨9567632882663292705130817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6378421921775528470087211 9567632882663292705130817)
  ·
    refine ⟨7175724661997469528848113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9567632882663292705130817 7175724661997469528848113)
    ·
      refine ⟨5381793496498102146636085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7175724661997469528848113 5381793496498102146636085)
      ·
        refine ⟨504543140296697076247133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 5381793496498102146636085 504543140296697076247133)
        ·
          refine ⟨189203677611261403592675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 504543140296697076247133 189203677611261403592675)
          ·
            refine ⟨283805516416892105389013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 189203677611261403592675 283805516416892105389013)
            ·
              refine ⟨6651691791020908720055, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 283805516416892105389013 6651691791020908720055)
              ·
                rfl

theorem cell21_262321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 3, 1, 7].length) (baseStart_262321 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_262321 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_262321 prefixEnd_262321 := by exact prefixLift 262321
  have htrace : WordTrace (prefixWord ++ tailWord_262321) baseStart_262321 baseEnd_262321 := by
    simpa [prefixWord, tailWord_262321, baseEnd_262321] using wordTrace_append hprefix tailTrace_262321
  have hstable : (prefixWord ++ tailWord_262321).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_262321).length < 2 ^ (prefixWord ++ tailWord_262321).sum := by decide
  have hdescent : baseEnd_262321 < baseStart_262321 := by decide
  rcases family_descends (prefixWord ++ tailWord_262321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_262338 : List Nat := [3, 5, 1, 1, 1, 2, 2, 6]
def baseStart_262338 : Nat := 118140960795 + 262338 * 2 ^ 59
def prefixEnd_262338 : Nat := 4983230072969 + 3 ^ 40 * 262338 * 2
def baseEnd_262338 : Nat := 19956368583599975565709

theorem tailTrace_262338 : CollatzResearch.WordTrace tailWord_262338 prefixEnd_262338 19956368583599975565709 := by
  unfold tailWord_262338
  simp only [CollatzResearch.WordTrace]
  refine ⟨2392063230900426152124917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6378835282401136405666445 2392063230900426152124917)
  ·
    refine ⟨224255927896914951761711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 2392063230900426152124917 224255927896914951761711)
    ·
      refine ⟨336383891845372427642567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 224255927896914951761711 336383891845372427642567)
      ·
        refine ⟨504575837768058641463851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 336383891845372427642567 504575837768058641463851)
        ·
          refine ⟨756863756652087962195777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 504575837768058641463851 756863756652087962195777)
          ·
            refine ⟨567647817489065971646833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 756863756652087962195777 567647817489065971646833)
            ·
              refine ⟨425735863116799478735125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 567647817489065971646833 425735863116799478735125)
              ·
                refine ⟨19956368583599975565709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 425735863116799478735125 19956368583599975565709)
                ·
                  rfl

theorem cell21_262338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 2, 2, 6].length) (baseStart_262338 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_262338 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_262338 prefixEnd_262338 := by exact prefixLift 262338
  have htrace : WordTrace (prefixWord ++ tailWord_262338) baseStart_262338 baseEnd_262338 := by
    simpa [prefixWord, tailWord_262338, baseEnd_262338] using wordTrace_append hprefix tailTrace_262338
  have hstable : (prefixWord ++ tailWord_262338).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_262338).length < 2 ^ (prefixWord ++ tailWord_262338).sum := by decide
  have hdescent : baseEnd_262338 < baseStart_262338 := by decide
  rcases family_descends (prefixWord ++ tailWord_262338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_262377 : List Nat := [1, 2, 1, 1, 1, 2, 2, 4, 7]
def baseStart_262377 : Nat := 118140960795 + 262377 * 2 ^ 59
def prefixEnd_262377 : Nat := 4983230072969 + 3 ^ 40 * 262377 * 2
def baseEnd_262377 : Nat := 59878006082144525547047

theorem tailTrace_262377 : CollatzResearch.WordTrace tailWord_262377 prefixEnd_262377 59878006082144525547047 := by
  unfold tailWord_262377
  simp only [CollatzResearch.WordTrace]
  refine ⟨9569675370460414269169385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6379783580306942846112923 9569675370460414269169385)
  ·
    refine ⟨7177256527845310701877039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9569675370460414269169385 7177256527845310701877039)
    ·
      refine ⟨10765884791767966052815559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7177256527845310701877039 10765884791767966052815559)
      ·
        refine ⟨16148827187651949079223339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10765884791767966052815559 16148827187651949079223339)
        ·
          refine ⟨24223240781477923618835009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16148827187651949079223339 24223240781477923618835009)
          ·
            refine ⟨18167430586108442714126257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24223240781477923618835009 18167430586108442714126257)
            ·
              refine ⟨13625572939581332035594693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18167430586108442714126257 13625572939581332035594693)
              ·
                refine ⟨2554794926171499756674005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13625572939581332035594693 2554794926171499756674005)
                ·
                  refine ⟨59878006082144525547047, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2554794926171499756674005 59878006082144525547047)
                  ·
                    rfl

theorem cell21_262377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 4, 7].length) (baseStart_262377 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_262377 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_262377 prefixEnd_262377 := by exact prefixLift 262377
  have htrace : WordTrace (prefixWord ++ tailWord_262377) baseStart_262377 baseEnd_262377 := by
    simpa [prefixWord, tailWord_262377, baseEnd_262377] using wordTrace_append hprefix tailTrace_262377
  have hstable : (prefixWord ++ tailWord_262377).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_262377).length < 2 ^ (prefixWord ++ tailWord_262377).sum := by decide
  have hdescent : baseEnd_262377 < baseStart_262377 := by decide
  rcases family_descends (prefixWord ++ tailWord_262377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_262442 : List Nat := [3, 1, 4, 2, 2, 1, 1, 1, 6]
def baseStart_262442 : Nat := 118140960795 + 262442 * 2 ^ 59
def prefixEnd_262442 : Nat := 4983230072969 + 3 ^ 40 * 262442 * 2
def baseEnd_262442 : Nat := 59892839967718856963581

theorem tailTrace_262442 : CollatzResearch.WordTrace tailWord_262442 prefixEnd_262442 59892839967718856963581 := by
  unfold tailWord_262442
  simp only [CollatzResearch.WordTrace]
  refine ⟨2393011528806232592571395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6381364076816620246857053 2393011528806232592571395)
  ·
    refine ⟨3589517293209348888857093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2393011528806232592571395 3589517293209348888857093)
    ·
      refine ⟨673034492476752916660705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3589517293209348888857093 673034492476752916660705)
      ·
        refine ⟨504775869357564687495529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 673034492476752916660705 504775869357564687495529)
        ·
          refine ⟨378581902018173515621647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 504775869357564687495529 378581902018173515621647)
          ·
            refine ⟨567872853027260273432471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 378581902018173515621647 567872853027260273432471)
            ·
              refine ⟨851809279540890410148707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 567872853027260273432471 851809279540890410148707)
              ·
                refine ⟨1277713919311335615223061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 851809279540890410148707 1277713919311335615223061)
                ·
                  refine ⟨59892839967718856963581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1277713919311335615223061 59892839967718856963581)
                  ·
                    rfl

theorem cell21_262442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 2, 1, 1, 1, 6].length) (baseStart_262442 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_262442 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_262442 prefixEnd_262442 := by exact prefixLift 262442
  have htrace : WordTrace (prefixWord ++ tailWord_262442) baseStart_262442 baseEnd_262442 := by
    simpa [prefixWord, tailWord_262442, baseEnd_262442] using wordTrace_append hprefix tailTrace_262442
  have hstable : (prefixWord ++ tailWord_262442).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_262442).length < 2 ^ (prefixWord ++ tailWord_262442).sum := by decide
  have hdescent : baseEnd_262442 < baseStart_262442 := by decide
  rcases family_descends (prefixWord ++ tailWord_262442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_262563 : List Nat := [1, 1, 1, 4, 1, 5, 1, 4, 3]
def baseStart_262563 : Nat := 118140960795 + 262563 * 2 ^ 59
def prefixEnd_262563 : Nat := 4983230072969 + 3 ^ 40 * 262563 * 2
def baseEnd_262563 : Nat := 59920453816249535446667

theorem tailTrace_262563 : CollatzResearch.WordTrace tailWord_262563 prefixEnd_262563 59920453816249535446667 := by
  unfold tailWord_262563
  simp only [CollatzResearch.WordTrace]
  refine ⟨9576459347786568035440343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6384306231857712023626895 9576459347786568035440343)
  ·
    refine ⟨14364689021679852053160515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9576459347786568035440343 14364689021679852053160515)
    ·
      refine ⟨21547033532519778079740773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14364689021679852053160515 21547033532519778079740773)
      ·
        refine ⟨4040068787347458389951395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 21547033532519778079740773 4040068787347458389951395)
        ·
          refine ⟨6060103181021187584927093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4040068787347458389951395 6060103181021187584927093)
          ·
            refine ⟨568134673220736336086915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 6060103181021187584927093 568134673220736336086915)
            ·
              refine ⟨852202009831104504130373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 568134673220736336086915 852202009831104504130373)
              ·
                refine ⟨159787876843332094524445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 852202009831104504130373 159787876843332094524445)
                ·
                  refine ⟨59920453816249535446667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 159787876843332094524445 59920453816249535446667)
                  ·
                    rfl

theorem cell21_262563_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 5, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 5, 1, 4, 3].length) (baseStart_262563 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_262563 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_262563 prefixEnd_262563 := by exact prefixLift 262563
  have htrace : WordTrace (prefixWord ++ tailWord_262563) baseStart_262563 baseEnd_262563 := by
    simpa [prefixWord, tailWord_262563, baseEnd_262563] using wordTrace_append hprefix tailTrace_262563
  have hstable : (prefixWord ++ tailWord_262563).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_262563).length < 2 ^ (prefixWord ++ tailWord_262563).sum := by decide
  have hdescent : baseEnd_262563 < baseStart_262563 := by decide
  rcases family_descends (prefixWord ++ tailWord_262563) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_262577 : List Nat := [1, 2, 2, 4, 1, 2, 2, 3, 4]
def baseStart_262577 : Nat := 118140960795 + 262577 * 2 ^ 59
def prefixEnd_262577 : Nat := 4983230072969 + 3 ^ 40 * 262577 * 2
def baseEnd_262577 : Nat := 59923648806988622213305

theorem tailTrace_262577 : CollatzResearch.WordTrace tailWord_262577 prefixEnd_262577 59923648806988622213305 := by
  unfold tailWord_262577
  simp only [CollatzResearch.WordTrace]
  refine ⟨9576969969735848426449985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6384646646490565617633323 9576969969735848426449985)
  ·
    refine ⟨7182727477301886319837489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9576969969735848426449985 7182727477301886319837489)
    ·
      refine ⟨5387045607976414739878117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7182727477301886319837489 5387045607976414739878117)
      ·
        refine ⟨1010071051495577763727147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5387045607976414739878117 1010071051495577763727147)
        ·
          refine ⟨1515106577243366645590721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1010071051495577763727147 1515106577243366645590721)
          ·
            refine ⟨1136329932932524984193041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1515106577243366645590721 1136329932932524984193041)
            ·
              refine ⟨852247449699393738144781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1136329932932524984193041 852247449699393738144781)
              ·
                refine ⟨319592793637272651804293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 852247449699393738144781 319592793637272651804293)
                ·
                  refine ⟨59923648806988622213305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 319592793637272651804293 59923648806988622213305)
                  ·
                    rfl

theorem cell21_262577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 2, 3, 4].length) (baseStart_262577 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_262577 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_262577 prefixEnd_262577 := by exact prefixLift 262577
  have htrace : WordTrace (prefixWord ++ tailWord_262577) baseStart_262577 baseEnd_262577 := by
    simpa [prefixWord, tailWord_262577, baseEnd_262577] using wordTrace_append hprefix tailTrace_262577
  have hstable : (prefixWord ++ tailWord_262577).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_262577).length < 2 ^ (prefixWord ++ tailWord_262577).sum := by decide
  have hdescent : baseEnd_262577 < baseStart_262577 := by decide
  rcases family_descends (prefixWord ++ tailWord_262577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_262642 : List Nat := [3, 2, 1, 4, 3, 1, 2, 5]
def baseStart_262642 : Nat := 118140960795 + 262642 * 2 ^ 59
def prefixEnd_262642 : Nat := 4983230072969 + 3 ^ 40 * 262642 * 2
def baseEnd_262642 : Nat := 19979494230854317876613

theorem tailTrace_262642 : CollatzResearch.WordTrace tailWord_262642 prefixEnd_262642 19979494230854317876613 := by
  unfold tailWord_262642
  simp only [CollatzResearch.WordTrace]
  refine ⟨2394835178625091131891545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6386227143000243018377453 2394835178625091131891545)
  ·
    refine ⟨1796126383968818348918659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2394835178625091131891545 1796126383968818348918659)
    ·
      refine ⟨2694189575953227523377989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1796126383968818348918659 2694189575953227523377989)
      ·
        refine ⟨505160545491230160633373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2694189575953227523377989 505160545491230160633373)
        ·
          refine ⟨189435204559211310237515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 505160545491230160633373 189435204559211310237515)
          ·
            refine ⟨284152806838816965356273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 189435204559211310237515 284152806838816965356273)
            ·
              refine ⟨213114605129112724017205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 284152806838816965356273 213114605129112724017205)
              ·
                refine ⟨19979494230854317876613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 213114605129112724017205 19979494230854317876613)
                ·
                  rfl

theorem cell21_262642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 3, 1, 2, 5].length) (baseStart_262642 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_262642 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_262642 prefixEnd_262642 := by exact prefixLift 262642
  have htrace : WordTrace (prefixWord ++ tailWord_262642) baseStart_262642 baseEnd_262642 := by
    simpa [prefixWord, tailWord_262642, baseEnd_262642] using wordTrace_append hprefix tailTrace_262642
  have hstable : (prefixWord ++ tailWord_262642).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_262642).length < 2 ^ (prefixWord ++ tailWord_262642).sum := by decide
  have hdescent : baseEnd_262642 < baseStart_262642 := by decide
  rcases family_descends (prefixWord ++ tailWord_262642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_262667 : List Nat := [1, 1, 1, 1, 7, 3, 7]
def baseStart_262667 : Nat := 118140960795 + 262667 * 2 ^ 59
def prefixEnd_262667 : Nat := 4983230072969 + 3 ^ 40 * 262667 * 2
def baseEnd_262667 : Nat := 6660465337018718412569

theorem tailTrace_262667 : CollatzResearch.WordTrace tailWord_262667 prefixEnd_262667 6660465337018718412569 := by
  unfold tailWord_262667
  simp only [CollatzResearch.WordTrace]
  refine ⟨9580252539409793797226255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6386835026273195864817503 9580252539409793797226255)
  ·
    refine ⟨14370378809114690695839383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9580252539409793797226255 14370378809114690695839383)
    ·
      refine ⟨21555568213672036043759075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14370378809114690695839383 21555568213672036043759075)
      ·
        refine ⟨32333352320508054065638613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21555568213672036043759075 32333352320508054065638613)
        ·
          refine ⟨757812945011907517163405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 32333352320508054065638613 757812945011907517163405)
          ·
            refine ⟨284179854379465318936277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 757812945011907517163405 284179854379465318936277)
            ·
              refine ⟨6660465337018718412569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 284179854379465318936277 6660465337018718412569)
              ·
                rfl

theorem cell21_262667_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 3, 7].length) (baseStart_262667 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_262667 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_262667 prefixEnd_262667 := by exact prefixLift 262667
  have htrace : WordTrace (prefixWord ++ tailWord_262667) baseStart_262667 baseEnd_262667 := by
    simpa [prefixWord, tailWord_262667, baseEnd_262667] using wordTrace_append hprefix tailTrace_262667
  have hstable : (prefixWord ++ tailWord_262667).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_262667).length < 2 ^ (prefixWord ++ tailWord_262667).sum := by decide
  have hdescent : baseEnd_262667 < baseStart_262667 := by decide
  rcases family_descends (prefixWord ++ tailWord_262667) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_262724 : List Nat := [2, 3, 5, 1, 2, 1, 2, 2, 3]
def baseStart_262724 : Nat := 118140960795 + 262724 * 2 ^ 59
def prefixEnd_262724 : Nat := 4983230072969 + 3 ^ 40 * 262724 * 2
def baseEnd_262724 : Nat := 59957196209749033263005

theorem tailTrace_262724 : CollatzResearch.WordTrace tailWord_262724 prefixEnd_262724 59957196209749033263005 := by
  unfold tailWord_262724
  simp only [CollatzResearch.WordTrace]
  refine ⟨4791165750101646266025613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6388221000135528354700817 4791165750101646266025613)
  ·
    refine ⟨1796687156288117349759605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4791165750101646266025613 1796687156288117349759605)
    ·
      refine ⟨168439420902011001539963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 1796687156288117349759605 168439420902011001539963)
      ·
        refine ⟨252659131353016502309945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 168439420902011001539963 252659131353016502309945)
        ·
          refine ⟨189494348514762376732459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 252659131353016502309945 189494348514762376732459)
          ·
            refine ⟨284241522772143565098689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 189494348514762376732459 284241522772143565098689)
            ·
              refine ⟨213181142079107673824017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 284241522772143565098689 213181142079107673824017)
              ·
                refine ⟨159885856559330755368013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 213181142079107673824017 159885856559330755368013)
                ·
                  refine ⟨59957196209749033263005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 159885856559330755368013 59957196209749033263005)
                  ·
                    rfl

theorem cell21_262724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 2, 1, 2, 2, 3].length) (baseStart_262724 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_262724 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_262724 prefixEnd_262724 := by exact prefixLift 262724
  have htrace : WordTrace (prefixWord ++ tailWord_262724) baseStart_262724 baseEnd_262724 := by
    simpa [prefixWord, tailWord_262724, baseEnd_262724] using wordTrace_append hprefix tailTrace_262724
  have hstable : (prefixWord ++ tailWord_262724).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_262724).length < 2 ^ (prefixWord ++ tailWord_262724).sum := by decide
  have hdescent : baseEnd_262724 < baseStart_262724 := by decide
  rcases family_descends (prefixWord ++ tailWord_262724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_262909 : List Nat := [1, 4, 1, 1, 1, 1, 4, 3, 5]
def baseStart_262909 : Nat := 118140960795 + 262909 * 2 ^ 59
def prefixEnd_262909 : Nat := 4983230072969 + 3 ^ 40 * 262909 * 2
def baseEnd_262909 : Nat := 59999415730229822679293

theorem tailTrace_262909 : CollatzResearch.WordTrace tailWord_262909 prefixEnd_262909 59999415730229822679293 := by
  unfold tailWord_262909
  simp only [CollatzResearch.WordTrace]
  refine ⟨9589079004533069127535781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6392719336355379418357187 9589079004533069127535781)
  ·
    refine ⟨1797952313349950461412959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 9589079004533069127535781 1797952313349950461412959)
    ·
      refine ⟨2696928470024925692119439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1797952313349950461412959 2696928470024925692119439)
      ·
        refine ⟨4045392705037388538179159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2696928470024925692119439 4045392705037388538179159)
        ·
          refine ⟨6068089057556082807268739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4045392705037388538179159 6068089057556082807268739)
          ·
            refine ⟨9102133586334124210903109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6068089057556082807268739 9102133586334124210903109)
            ·
              refine ⟨1706650047437648289544333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9102133586334124210903109 1706650047437648289544333)
              ·
                refine ⟨639993767789118108579125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1706650047437648289544333 639993767789118108579125)
                ·
                  refine ⟨59999415730229822679293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 639993767789118108579125 59999415730229822679293)
                  ·
                    rfl

theorem cell21_262909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 4, 3, 5].length) (baseStart_262909 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_262909 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_262909 prefixEnd_262909 := by exact prefixLift 262909
  have htrace : WordTrace (prefixWord ++ tailWord_262909) baseStart_262909 baseEnd_262909 := by
    simpa [prefixWord, tailWord_262909, baseEnd_262909] using wordTrace_append hprefix tailTrace_262909
  have hstable : (prefixWord ++ tailWord_262909).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_262909).length < 2 ^ (prefixWord ++ tailWord_262909).sum := by decide
  have hdescent : baseEnd_262909 < baseStart_262909 := by decide
  rcases family_descends (prefixWord ++ tailWord_262909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_262923 : List Nat := [1, 1, 1, 1, 5, 1, 1, 2, 8]
def baseStart_262923 : Nat := 118140960795 + 262923 * 2 ^ 59
def prefixEnd_262923 : Nat := 4983230072969 + 3 ^ 40 * 262923 * 2
def baseEnd_262923 : Nat := 60002610720968909445931

theorem tailTrace_262923 : CollatzResearch.WordTrace tailWord_262923 prefixEnd_262923 60002610720968909445931 := by
  unfold tailWord_262923
  simp only [CollatzResearch.WordTrace]
  refine ⟨9589589626482349518545423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6393059750988233012363615 9589589626482349518545423)
  ·
    refine ⟨14384384439723524277818135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9589589626482349518545423 14384384439723524277818135)
    ·
      refine ⟨21576576659585286416727203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14384384439723524277818135 21576576659585286416727203)
      ·
        refine ⟨32364864989377929625090805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21576576659585286416727203 32364864989377929625090805)
        ·
          refine ⟨3034206092754180902352263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 32364864989377929625090805 3034206092754180902352263)
          ·
            refine ⟨4551309139131271353528395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3034206092754180902352263 4551309139131271353528395)
            ·
              refine ⟨6826963708696907030292593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4551309139131271353528395 6826963708696907030292593)
              ·
                refine ⟨5120222781522680272719445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6826963708696907030292593 5120222781522680272719445)
                ·
                  refine ⟨60002610720968909445931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 5120222781522680272719445 60002610720968909445931)
                  ·
                    rfl

theorem cell21_262923_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 1, 2, 8].length) (baseStart_262923 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_262923 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_262923 prefixEnd_262923 := by exact prefixLift 262923
  have htrace : WordTrace (prefixWord ++ tailWord_262923) baseStart_262923 baseEnd_262923 := by
    simpa [prefixWord, tailWord_262923, baseEnd_262923] using wordTrace_append hprefix tailTrace_262923
  have hstable : (prefixWord ++ tailWord_262923).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_262923).length < 2 ^ (prefixWord ++ tailWord_262923).sum := by decide
  have hdescent : baseEnd_262923 < baseStart_262923 := by decide
  rcases family_descends (prefixWord ++ tailWord_262923) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_262943 : List Nat := [1, 1, 2, 4, 2, 3, 2, 3, 3]
def baseStart_262943 : Nat := 118140960795 + 262943 * 2 ^ 59
def prefixEnd_262943 : Nat := 4983230072969 + 3 ^ 40 * 262943 * 2
def baseEnd_262943 : Nat := 60007174993453319112557

theorem tailTrace_262943 : CollatzResearch.WordTrace tailWord_262943 prefixEnd_262943 60007174993453319112557 := by
  unfold tailWord_262943
  simp only [CollatzResearch.WordTrace]
  refine ⟨9590319086409892934273483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6393546057606595289515655 9590319086409892934273483)
  ·
    refine ⟨14385478629614839401410225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9590319086409892934273483 14385478629614839401410225)
    ·
      refine ⟨10789108972211129551057669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14385478629614839401410225 10789108972211129551057669)
      ·
        refine ⟨2022957932289586790823313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10789108972211129551057669 2022957932289586790823313)
        ·
          refine ⟨1517218449217190093117485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2022957932289586790823313 1517218449217190093117485)
          ·
            refine ⟨568956918456446284919057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1517218449217190093117485 568956918456446284919057)
            ·
              refine ⟨426717688842334713689293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 568956918456446284919057 426717688842334713689293)
              ·
                refine ⟨160019133315875517633485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 426717688842334713689293 160019133315875517633485)
                ·
                  refine ⟨60007174993453319112557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 160019133315875517633485 60007174993453319112557)
                  ·
                    rfl

theorem cell21_262943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 3, 2, 3, 3].length) (baseStart_262943 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_262943 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_262943 prefixEnd_262943 := by exact prefixLift 262943
  have htrace : WordTrace (prefixWord ++ tailWord_262943) baseStart_262943 baseEnd_262943 := by
    simpa [prefixWord, tailWord_262943, baseEnd_262943] using wordTrace_append hprefix tailTrace_262943
  have hstable : (prefixWord ++ tailWord_262943).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_262943).length < 2 ^ (prefixWord ++ tailWord_262943).sum := by decide
  have hdescent : baseEnd_262943 < baseStart_262943 := by decide
  rcases family_descends (prefixWord ++ tailWord_262943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_262985 : List Nat := [1, 2, 1, 1, 2, 5, 2, 2, 5]
def baseStart_262985 : Nat := 118140960795 + 262985 * 2 ^ 59
def prefixEnd_262985 : Nat := 4983230072969 + 3 ^ 40 * 262985 * 2
def baseEnd_262985 : Nat := 60016759965670579412471

theorem tailTrace_262985 : CollatzResearch.WordTrace tailWord_262985 prefixEnd_262985 60016759965670579412471 := by
  unfold tailWord_262985
  simp only [CollatzResearch.WordTrace]
  refine ⟨9591850952257734107302409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6394567301505156071534939 9591850952257734107302409)
  ·
    refine ⟨7193888214193300580476807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9591850952257734107302409 7193888214193300580476807)
    ·
      refine ⟨10790832321289950870715211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7193888214193300580476807 10790832321289950870715211)
      ·
        refine ⟨16186248481934926306072817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10790832321289950870715211 16186248481934926306072817)
        ·
          refine ⟨12139686361451194729554613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16186248481934926306072817 12139686361451194729554613)
          ·
            refine ⟨1138095596386049505895745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 12139686361451194729554613 1138095596386049505895745)
            ·
              refine ⟨853571697289537129421809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1138095596386049505895745 853571697289537129421809)
              ·
                refine ⟨640178772967152847066357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 853571697289537129421809 640178772967152847066357)
                ·
                  refine ⟨60016759965670579412471, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 640178772967152847066357 60016759965670579412471)
                  ·
                    rfl

theorem cell21_262985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 2, 2, 5].length) (baseStart_262985 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_262985 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_262985 prefixEnd_262985 := by exact prefixLift 262985
  have htrace : WordTrace (prefixWord ++ tailWord_262985) baseStart_262985 baseEnd_262985 := by
    simpa [prefixWord, tailWord_262985, baseEnd_262985] using wordTrace_append hprefix tailTrace_262985
  have hstable : (prefixWord ++ tailWord_262985).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_262985).length < 2 ^ (prefixWord ++ tailWord_262985).sum := by decide
  have hdescent : baseEnd_262985 < baseStart_262985 := by decide
  rcases family_descends (prefixWord ++ tailWord_262985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_262988 : List Nat := [2, 2, 1, 3, 3, 3, 2, 5]
def baseStart_262988 : Nat := 118140960795 + 262988 * 2 ^ 59
def prefixEnd_262988 : Nat := 4983230072969 + 3 ^ 40 * 262988 * 2
def baseEnd_262988 : Nat := 20005814868847746954155

theorem tailTrace_262988 : CollatzResearch.WordTrace tailWord_262988 prefixEnd_262988 20005814868847746954155 := by
  unfold tailWord_262988
  simp only [CollatzResearch.WordTrace]
  refine ⟨4795980185623432809830809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6394640247497910413107745 4795980185623432809830809)
  ·
    refine ⟨3596985139217574607373107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4795980185623432809830809 3596985139217574607373107)
    ·
      refine ⟨5395477708826361911059661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3596985139217574607373107 5395477708826361911059661)
      ·
        refine ⟨2023304140809885716647373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5395477708826361911059661 2023304140809885716647373)
        ·
          refine ⟨758739052803707143742765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2023304140809885716647373 758739052803707143742765)
          ·
            refine ⟨284527144801390178903537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 758739052803707143742765 284527144801390178903537)
            ·
              refine ⟨213395358601042634177653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 284527144801390178903537 213395358601042634177653)
              ·
                refine ⟨20005814868847746954155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 213395358601042634177653 20005814868847746954155)
                ·
                  rfl

theorem cell21_262988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 3, 2, 5].length) (baseStart_262988 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_262988 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_262988 prefixEnd_262988 := by exact prefixLift 262988
  have htrace : WordTrace (prefixWord ++ tailWord_262988) baseStart_262988 baseEnd_262988 := by
    simpa [prefixWord, tailWord_262988, baseEnd_262988] using wordTrace_append hprefix tailTrace_262988
  have hstable : (prefixWord ++ tailWord_262988).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_262988).length < 2 ^ (prefixWord ++ tailWord_262988).sum := by decide
  have hdescent : baseEnd_262988 < baseStart_262988 := by decide
  rcases family_descends (prefixWord ++ tailWord_262988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_263016 : List Nat := [2, 1, 4, 2, 1, 2, 2, 1, 6]
def baseStart_263016 : Nat := 118140960795 + 263016 * 2 ^ 59
def prefixEnd_263016 : Nat := 4983230072969 + 3 ^ 40 * 263016 * 2
def baseEnd_263016 : Nat := 60023834588021414395741

theorem tailTrace_263016 : CollatzResearch.WordTrace tailWord_263016 prefixEnd_263016 60023834588021414395741 := by
  unfold tailWord_263016
  simp only [CollatzResearch.WordTrace]
  refine ⟨4796490807572713200840451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6395321076763617601120601 4796490807572713200840451)
  ·
    refine ⟨7194736211359069801260677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4796490807572713200840451 7194736211359069801260677)
    ·
      refine ⟨1349013039629825587736377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7194736211359069801260677 1349013039629825587736377)
      ·
        refine ⟨1011759779722369190802283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1349013039629825587736377 1011759779722369190802283)
        ·
          refine ⟨1517639669583553786203425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1011759779722369190802283 1517639669583553786203425)
          ·
            refine ⟨1138229752187665339652569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1517639669583553786203425 1138229752187665339652569)
            ·
              refine ⟨853672314140749004739427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1138229752187665339652569 853672314140749004739427)
              ·
                refine ⟨1280508471211123507109141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 853672314140749004739427 1280508471211123507109141)
                ·
                  refine ⟨60023834588021414395741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1280508471211123507109141 60023834588021414395741)
                  ·
                    rfl

theorem cell21_263016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 2, 1, 6].length) (baseStart_263016 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_263016 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_263016 prefixEnd_263016 := by exact prefixLift 263016
  have htrace : WordTrace (prefixWord ++ tailWord_263016) baseStart_263016 baseEnd_263016 := by
    simpa [prefixWord, tailWord_263016, baseEnd_263016] using wordTrace_append hprefix tailTrace_263016
  have hstable : (prefixWord ++ tailWord_263016).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_263016).length < 2 ^ (prefixWord ++ tailWord_263016).sum := by decide
  have hdescent : baseEnd_263016 < baseStart_263016 := by decide
  rcases family_descends (prefixWord ++ tailWord_263016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_263033 : List Nat := [1, 2, 1, 3, 2, 3, 4, 1, 4]
def baseStart_263033 : Nat := 118140960795 + 263033 * 2 ^ 59
def prefixEnd_263033 : Nat := 4983230072969 + 3 ^ 40 * 263033 * 2
def baseEnd_263033 : Nat := 60027714219633162612373

theorem tailTrace_263033 : CollatzResearch.WordTrace tailWord_263033 prefixEnd_263033 60027714219633162612373 := by
  unfold tailWord_263033
  simp only [CollatzResearch.WordTrace]
  refine ⟨9593601656083838305049753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6395734437389225536699835 9593601656083838305049753)
  ·
    refine ⟨7195201242062878728787315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9593601656083838305049753 7195201242062878728787315)
    ·
      refine ⟨10792801863094318093180973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7195201242062878728787315 10792801863094318093180973)
      ·
        refine ⟨4047300698660369284942865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10792801863094318093180973 4047300698660369284942865)
        ·
          refine ⟨3035475523995276963707149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4047300698660369284942865 3035475523995276963707149)
          ·
            refine ⟨1138303321498228861390181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3035475523995276963707149 1138303321498228861390181)
            ·
              refine ⟨213431872780917911510659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1138303321498228861390181 213431872780917911510659)
              ·
                refine ⟨320147809171376867265989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 213431872780917911510659 320147809171376867265989)
                ·
                  refine ⟨60027714219633162612373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 320147809171376867265989 60027714219633162612373)
                  ·
                    rfl

theorem cell21_263033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 4, 1, 4].length) (baseStart_263033 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_263033 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_263033 prefixEnd_263033 := by exact prefixLift 263033
  have htrace : WordTrace (prefixWord ++ tailWord_263033) baseStart_263033 baseEnd_263033 := by
    simpa [prefixWord, tailWord_263033, baseEnd_263033] using wordTrace_append hprefix tailTrace_263033
  have hstable : (prefixWord ++ tailWord_263033).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_263033).length < 2 ^ (prefixWord ++ tailWord_263033).sum := by decide
  have hdescent : baseEnd_263033 < baseStart_263033 := by decide
  rcases family_descends (prefixWord ++ tailWord_263033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_263075 : List Nat := [1, 1, 1, 4, 1, 2, 2, 3, 6]
def baseStart_263075 : Nat := 118140960795 + 263075 * 2 ^ 59
def prefixEnd_263075 : Nat := 4983230072969 + 3 ^ 40 * 263075 * 2
def baseEnd_263075 : Nat := 60037299191850422912287

theorem tailTrace_263075 : CollatzResearch.WordTrace tailWord_263075 prefixEnd_263075 60037299191850422912287 := by
  unfold tailWord_263075
  simp only [CollatzResearch.WordTrace]
  refine ⟨9595133521931679478078679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6396755681287786318719119 9595133521931679478078679)
  ·
    refine ⟨14392700282897519217118019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9595133521931679478078679 14392700282897519217118019)
    ·
      refine ⟨21589050424346278825677029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14392700282897519217118019 21589050424346278825677029)
      ·
        refine ⟨4047946954564927279814443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 21589050424346278825677029 4047946954564927279814443)
        ·
          refine ⟨6071920431847390919721665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4047946954564927279814443 6071920431847390919721665)
          ·
            refine ⟨4553940323885543189791249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6071920431847390919721665 4553940323885543189791249)
            ·
              refine ⟨3415455242914157392343437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4553940323885543189791249 3415455242914157392343437)
              ·
                refine ⟨1280795716092809022128789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3415455242914157392343437 1280795716092809022128789)
                ·
                  refine ⟨60037299191850422912287, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1280795716092809022128789 60037299191850422912287)
                  ·
                    rfl

theorem cell21_263075_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 2, 3, 6].length) (baseStart_263075 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_263075 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_263075 prefixEnd_263075 := by exact prefixLift 263075
  have htrace : WordTrace (prefixWord ++ tailWord_263075) baseStart_263075 baseEnd_263075 := by
    simpa [prefixWord, tailWord_263075, baseEnd_263075] using wordTrace_append hprefix tailTrace_263075
  have hstable : (prefixWord ++ tailWord_263075).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_263075).length < 2 ^ (prefixWord ++ tailWord_263075).sum := by decide
  have hdescent : baseEnd_263075 < baseStart_263075 := by decide
  rcases family_descends (prefixWord ++ tailWord_263075) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_263120 : List Nat := [2, 1, 1, 1, 1, 2, 3, 1, 9]
def baseStart_263120 : Nat := 118140960795 + 263120 * 2 ^ 59
def prefixEnd_263120 : Nat := 4983230072969 + 3 ^ 40 * 263120 * 2
def baseEnd_263120 : Nat := 60047568804940344662195

theorem tailTrace_263120 : CollatzResearch.WordTrace tailWord_263120 prefixEnd_263120 60047568804940344662195 := by
  unfold tailWord_263120
  simp only [CollatzResearch.WordTrace]
  refine ⟨4798387403384326081733407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6397849871179101442311209 4798387403384326081733407)
  ·
    refine ⟨7197581105076489122600111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4798387403384326081733407 7197581105076489122600111)
    ·
      refine ⟨10796371657614733683900167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7197581105076489122600111 10796371657614733683900167)
      ·
        refine ⟨16194557486422100525850251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10796371657614733683900167 16194557486422100525850251)
        ·
          refine ⟨24291836229633150788775377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16194557486422100525850251 24291836229633150788775377)
          ·
            refine ⟨18218877172224863091581533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24291836229633150788775377 18218877172224863091581533)
            ·
              refine ⟨6832078939584323659343075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18218877172224863091581533 6832078939584323659343075)
              ·
                refine ⟨10248118409376485489014613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6832078939584323659343075 10248118409376485489014613)
                ·
                  refine ⟨60047568804940344662195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 10248118409376485489014613 60047568804940344662195)
                  ·
                    rfl

theorem cell21_263120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 3, 1, 9].length) (baseStart_263120 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_263120 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_263120 prefixEnd_263120 := by exact prefixLift 263120
  have htrace : WordTrace (prefixWord ++ tailWord_263120) baseStart_263120 baseEnd_263120 := by
    simpa [prefixWord, tailWord_263120, baseEnd_263120] using wordTrace_append hprefix tailTrace_263120
  have hstable : (prefixWord ++ tailWord_263120).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_263120).length < 2 ^ (prefixWord ++ tailWord_263120).sum := by decide
  have hdescent : baseEnd_263120 < baseStart_263120 := by decide
  rcases family_descends (prefixWord ++ tailWord_263120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_263126 : List Nat := [5, 2, 1, 1, 2, 1, 3, 2, 4]
def baseStart_263126 : Nat := 118140960795 + 263126 * 2 ^ 59
def prefixEnd_263126 : Nat := 4983230072969 + 3 ^ 40 * 263126 * 2
def baseEnd_263126 : Nat := 60048938086685667562183

theorem tailTrace_263126 : CollatzResearch.WordTrace tailWord_263126 prefixEnd_263126 60048938086685667562183 := by
  unfold tailWord_263126
  simp only [CollatzResearch.WordTrace]
  refine ⟨599812102796682199261577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 6397995763164610125456821 599812102796682199261577)
  ·
    refine ⟨449859077097511649446183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 599812102796682199261577 449859077097511649446183)
    ·
      refine ⟨674788615646267474169275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 449859077097511649446183 674788615646267474169275)
      ·
        refine ⟨1012182923469401211253913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 674788615646267474169275 1012182923469401211253913)
        ·
          refine ⟨759137192602050908440435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1012182923469401211253913 759137192602050908440435)
          ·
            refine ⟨1138705788903076362660653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 759137192602050908440435 1138705788903076362660653)
            ·
              refine ⟨427014670838653635997745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1138705788903076362660653 427014670838653635997745)
              ·
                refine ⟨320261003128990226998309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 427014670838653635997745 320261003128990226998309)
                ·
                  refine ⟨60048938086685667562183, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 320261003128990226998309 60048938086685667562183)
                  ·
                    rfl

theorem cell21_263126_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 3, 2, 4].length) (baseStart_263126 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_263126 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_263126 prefixEnd_263126 := by exact prefixLift 263126
  have htrace : WordTrace (prefixWord ++ tailWord_263126) baseStart_263126 baseEnd_263126 := by
    simpa [prefixWord, tailWord_263126, baseEnd_263126] using wordTrace_append hprefix tailTrace_263126
  have hstable : (prefixWord ++ tailWord_263126).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_263126).length < 2 ^ (prefixWord ++ tailWord_263126).sum := by decide
  have hdescent : baseEnd_263126 < baseStart_263126 := by decide
  rcases family_descends (prefixWord ++ tailWord_263126) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_263182 : List Nat := [4, 1, 1, 2, 2, 2, 9]
def baseStart_263182 : Nat := 118140960795 + 263182 * 2 ^ 59
def prefixEnd_263182 : Nat := 4983230072969 + 3 ^ 40 * 263182 * 2
def baseEnd_263182 : Nat := 6673524227738001625415

theorem tailTrace_263182 : CollatzResearch.WordTrace tailWord_263182 prefixEnd_263182 6673524227738001625415 := by
  unfold tailWord_263182
  simp only [CollatzResearch.WordTrace]
  refine ⟨1199879516568004594027975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 6399357421696024501482533 1199879516568004594027975)
  ·
    refine ⟨1799819274852006891041963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1199879516568004594027975 1799819274852006891041963)
    ·
      refine ⟨2699728912278010336562945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1799819274852006891041963 2699728912278010336562945)
      ·
        refine ⟨2024796684208507752422209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2699728912278010336562945 2024796684208507752422209)
        ·
          refine ⟨1518597513156380814316657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2024796684208507752422209 1518597513156380814316657)
          ·
            refine ⟨1138948134867285610737493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1518597513156380814316657 1138948134867285610737493)
            ·
              refine ⟨6673524227738001625415, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 1138948134867285610737493 6673524227738001625415)
              ·
                rfl

theorem cell21_263182_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 9].length) (baseStart_263182 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_263182 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_263182 prefixEnd_263182 := by exact prefixLift 263182
  have htrace : WordTrace (prefixWord ++ tailWord_263182) baseStart_263182 baseEnd_263182 := by
    simpa [prefixWord, tailWord_263182, baseEnd_263182] using wordTrace_append hprefix tailTrace_263182
  have hstable : (prefixWord ++ tailWord_263182).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_263182).length < 2 ^ (prefixWord ++ tailWord_263182).sum := by decide
  have hdescent : baseEnd_263182 < baseStart_263182 := by decide
  rcases family_descends (prefixWord ++ tailWord_263182) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_263202 : List Nat := [3, 3, 1, 1, 1, 5, 2, 1, 4]
def baseStart_263202 : Nat := 118140960795 + 263202 * 2 ^ 59
def prefixEnd_263202 : Nat := 4983230072969 + 3 ^ 40 * 263202 * 2
def baseEnd_263202 : Nat := 60066282322126424295361

theorem tailTrace_263202 : CollatzResearch.WordTrace tailWord_263202 prefixEnd_263202 60066282322126424295361 := by
  unfold tailWord_263202
  simp only [CollatzResearch.WordTrace]
  refine ⟨2399941398117895041987965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6399843728314386778634573 2399941398117895041987965)
  ·
    refine ⟨899978024294210640745487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2399941398117895041987965 899978024294210640745487)
    ·
      refine ⟨1349967036441315961118231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 899978024294210640745487 1349967036441315961118231)
      ·
        refine ⟨2024950554661973941677347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1349967036441315961118231 2024950554661973941677347)
        ·
          refine ⟨3037425831992960912516021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2024950554661973941677347 3037425831992960912516021)
          ·
            refine ⟨284758671749340085548377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 3037425831992960912516021 284758671749340085548377)
            ·
              refine ⟨213569003812005064161283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 284758671749340085548377 213569003812005064161283)
              ·
                refine ⟨320353505718007596241925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 213569003812005064161283 320353505718007596241925)
                ·
                  refine ⟨60066282322126424295361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 320353505718007596241925 60066282322126424295361)
                  ·
                    rfl

theorem cell21_263202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 5, 2, 1, 4].length) (baseStart_263202 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_263202 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_263202 prefixEnd_263202 := by exact prefixLift 263202
  have htrace : WordTrace (prefixWord ++ tailWord_263202) baseStart_263202 baseEnd_263202 := by
    simpa [prefixWord, tailWord_263202, baseEnd_263202] using wordTrace_append hprefix tailTrace_263202
  have hstable : (prefixWord ++ tailWord_263202).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_263202).length < 2 ^ (prefixWord ++ tailWord_263202).sum := by decide
  have hdescent : baseEnd_263202 < baseStart_263202 := by decide
  rcases family_descends (prefixWord ++ tailWord_263202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_263306 : List Nat := [3, 1, 2, 3, 1, 1, 1, 6, 3]
def baseStart_263306 : Nat := 118140960795 + 263306 * 2 ^ 59
def prefixEnd_263306 : Nat := 4983230072969 + 3 ^ 40 * 263306 * 2
def baseEnd_263306 : Nat := 60090016539045354561815

theorem tailTrace_263306 : CollatzResearch.WordTrace tailWord_263306 prefixEnd_263306 60090016539045354561815 := by
  unfold tailWord_263306
  simp only [CollatzResearch.WordTrace]
  refine ⟨2400889696023701482434443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6402372522729870619825181 2400889696023701482434443)
  ·
    refine ⟨3601334544035552223651665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2400889696023701482434443 3601334544035552223651665)
    ·
      refine ⟨2701000908026664167738749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3601334544035552223651665 2701000908026664167738749)
      ·
        refine ⟨1012875340509999062902031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2701000908026664167738749 1012875340509999062902031)
        ·
          refine ⟨1519313010764998594353047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1012875340509999062902031 1519313010764998594353047)
          ·
            refine ⟨2278969516147497891529571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1519313010764998594353047 2278969516147497891529571)
            ·
              refine ⟨3418454274221246837294357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2278969516147497891529571 3418454274221246837294357)
              ·
                refine ⟨160240044104120945498173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3418454274221246837294357 160240044104120945498173)
                ·
                  refine ⟨60090016539045354561815, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 160240044104120945498173 60090016539045354561815)
                  ·
                    rfl

theorem cell21_263306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 1, 6, 3].length) (baseStart_263306 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_263306 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_263306 prefixEnd_263306 := by exact prefixLift 263306
  have htrace : WordTrace (prefixWord ++ tailWord_263306) baseStart_263306 baseEnd_263306 := by
    simpa [prefixWord, tailWord_263306, baseEnd_263306] using wordTrace_append hprefix tailTrace_263306
  have hstable : (prefixWord ++ tailWord_263306).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_263306).length < 2 ^ (prefixWord ++ tailWord_263306).sum := by decide
  have hdescent : baseEnd_263306 < baseStart_263306 := by decide
  rcases family_descends (prefixWord ++ tailWord_263306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_263379 : List Nat := [1, 1, 1, 2, 1, 1, 1, 9, 4]
def baseStart_263379 : Nat := 118140960795 + 263379 * 2 ^ 59
def prefixEnd_263379 : Nat := 4983230072969 + 3 ^ 40 * 263379 * 2
def baseEnd_263379 : Nat := 60106676133613449844999

theorem tailTrace_263379 : CollatzResearch.WordTrace tailWord_263379 prefixEnd_263379 60106676133613449844999 := by
  unfold tailWord_263379
  simp only [CollatzResearch.WordTrace]
  refine ⟨9606221312830339397145191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6404147541886892931430127 9606221312830339397145191)
  ·
    refine ⟨14409331969245509095717787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9606221312830339397145191 14409331969245509095717787)
    ·
      refine ⟨21613997953868263643576681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14409331969245509095717787 21613997953868263643576681)
      ·
        refine ⟨16210498465401197732682511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21613997953868263643576681 16210498465401197732682511)
        ·
          refine ⟨24315747698101796599023767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16210498465401197732682511 24315747698101796599023767)
          ·
            refine ⟨36473621547152694898535651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24315747698101796599023767 36473621547152694898535651)
            ·
              refine ⟨54710432320729042347803477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36473621547152694898535651 54710432320729042347803477)
              ·
                refine ⟨320568939379271732506661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 54710432320729042347803477 320568939379271732506661)
                ·
                  refine ⟨60106676133613449844999, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 320568939379271732506661 60106676133613449844999)
                  ·
                    rfl

theorem cell21_263379_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 9, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 9, 4].length) (baseStart_263379 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_263379 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_263379 prefixEnd_263379 := by exact prefixLift 263379
  have htrace : WordTrace (prefixWord ++ tailWord_263379) baseStart_263379 baseEnd_263379 := by
    simpa [prefixWord, tailWord_263379, baseEnd_263379] using wordTrace_append hprefix tailTrace_263379
  have hstable : (prefixWord ++ tailWord_263379).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_263379).length < 2 ^ (prefixWord ++ tailWord_263379).sum := by decide
  have hdescent : baseEnd_263379 < baseStart_263379 := by decide
  rcases family_descends (prefixWord ++ tailWord_263379) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_263410 : List Nat := [3, 2, 1, 3, 3, 9]
def baseStart_263410 : Nat := 118140960795 + 263410 * 2 ^ 59
def prefixEnd_263410 : Nat := 4983230072969 + 3 ^ 40 * 263410 * 2
def baseEnd_263410 : Nat := 2226435213183862401047

theorem tailTrace_263410 : CollatzResearch.WordTrace tailWord_263410 prefixEnd_263410 2226435213183862401047 := by
  unfold tailWord_263410
  simp only [CollatzResearch.WordTrace]
  refine ⟨2401837993929507922880921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6404901317145354461015789 2401837993929507922880921)
  ·
    refine ⟨1801378495447130942160691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2401837993929507922880921 1801378495447130942160691)
    ·
      refine ⟨2702067743170696413241037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1801378495447130942160691 2702067743170696413241037)
      ·
        refine ⟨1013275403689011154965389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2702067743170696413241037 1013275403689011154965389)
        ·
          refine ⟨379978276383379183112021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1013275403689011154965389 379978276383379183112021)
          ·
            refine ⟨2226435213183862401047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 379978276383379183112021 2226435213183862401047)
            ·
              rfl

theorem cell21_263410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 3, 9].length) (baseStart_263410 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_263410 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_263410 prefixEnd_263410 := by exact prefixLift 263410
  have htrace : WordTrace (prefixWord ++ tailWord_263410) baseStart_263410 baseEnd_263410 := by
    simpa [prefixWord, tailWord_263410, baseEnd_263410] using wordTrace_append hprefix tailTrace_263410
  have hstable : (prefixWord ++ tailWord_263410).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_263410).length < 2 ^ (prefixWord ++ tailWord_263410).sum := by decide
  have hdescent : baseEnd_263410 < baseStart_263410 := by decide
  rcases family_descends (prefixWord ++ tailWord_263410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_263424 : List Nat := [2, 1, 1, 2, 1, 1, 3, 5, 5]
def baseStart_263424 : Nat := 118140960795 + 263424 * 2 ^ 59
def prefixEnd_263424 : Nat := 4983230072969 + 3 ^ 40 * 263424 * 2
def baseEnd_263424 : Nat := 60116945746703371594907

theorem tailTrace_263424 : CollatzResearch.WordTrace tailWord_263424 prefixEnd_263424 60116945746703371594907 := by
  unfold tailWord_263424
  simp only [CollatzResearch.WordTrace]
  refine ⟨4803931298833656041266663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6405241731778208055022217 4803931298833656041266663)
  ·
    refine ⟨7205896948250484061899995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4803931298833656041266663 7205896948250484061899995)
    ·
      refine ⟨10808845422375726092849993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7205896948250484061899995 10808845422375726092849993)
      ·
        refine ⟨8106634066781794569637495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10808845422375726092849993 8106634066781794569637495)
        ·
          refine ⟨12159951100172691854456243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8106634066781794569637495 12159951100172691854456243)
          ·
            refine ⟨18239926650259037781684365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12159951100172691854456243 18239926650259037781684365)
            ·
              refine ⟨6839972493847139168131637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18239926650259037781684365 6839972493847139168131637)
              ·
                refine ⟨641247421298169297012341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 6839972493847139168131637 641247421298169297012341)
                ·
                  refine ⟨60116945746703371594907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 641247421298169297012341 60116945746703371594907)
                  ·
                    rfl

theorem cell21_263424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 3, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 3, 5, 5].length) (baseStart_263424 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_263424 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_263424 prefixEnd_263424 := by exact prefixLift 263424
  have htrace : WordTrace (prefixWord ++ tailWord_263424) baseStart_263424 baseEnd_263424 := by
    simpa [prefixWord, tailWord_263424, baseEnd_263424] using wordTrace_append hprefix tailTrace_263424
  have hstable : (prefixWord ++ tailWord_263424).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_263424).length < 2 ^ (prefixWord ++ tailWord_263424).sum := by decide
  have hdescent : baseEnd_263424 < baseStart_263424 := by decide
  rcases family_descends (prefixWord ++ tailWord_263424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_263486 : List Nat := [4, 2, 1, 2, 1, 1, 2, 8]
def baseStart_263486 : Nat := 118140960795 + 263486 * 2 ^ 59
def prefixEnd_263486 : Nat := 4983230072969 + 3 ^ 40 * 263486 * 2
def baseEnd_263486 : Nat := 20043698330468347187149

theorem tailTrace_263486 : CollatzResearch.WordTrace tailWord_263486 prefixEnd_263486 20043698330468347187149 := by
  unfold tailWord_263486
  simp only [CollatzResearch.WordTrace]
  refine ⟨1201265490430337083911289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 6406749282295131114193541 1201265490430337083911289)
  ·
    refine ⟨900949117822752812933467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1201265490430337083911289 900949117822752812933467)
    ·
      refine ⟨1351423676734129219400201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 900949117822752812933467 1351423676734129219400201)
      ·
        refine ⟨1013567757550596914550151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1351423676734129219400201 1013567757550596914550151)
        ·
          refine ⟨1520351636325895371825227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1013567757550596914550151 1520351636325895371825227)
          ·
            refine ⟨2280527454488843057737841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1520351636325895371825227 2280527454488843057737841)
            ·
              refine ⟨1710395590866632293303381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2280527454488843057737841 1710395590866632293303381)
              ·
                refine ⟨20043698330468347187149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1710395590866632293303381 20043698330468347187149)
                ·
                  rfl

theorem cell21_263486_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 2, 8].length) (baseStart_263486 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_263486 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_263486 prefixEnd_263486 := by exact prefixLift 263486
  have htrace : WordTrace (prefixWord ++ tailWord_263486) baseStart_263486 baseEnd_263486 := by
    simpa [prefixWord, tailWord_263486, baseEnd_263486] using wordTrace_append hprefix tailTrace_263486
  have hstable : (prefixWord ++ tailWord_263486).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_263486).length < 2 ^ (prefixWord ++ tailWord_263486).sum := by decide
  have hdescent : baseEnd_263486 < baseStart_263486 := by decide
  rcases family_descends (prefixWord ++ tailWord_263486) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_263545 : List Nat := [1, 2, 1, 3, 2, 1, 3, 8]
def baseStart_263545 : Nat := 118140960795 + 263545 * 2 ^ 59
def prefixEnd_263545 : Nat := 4983230072969 + 3 ^ 40 * 263545 * 2
def baseEnd_263545 : Nat := 20048186531744683359331

theorem tailTrace_263545 : CollatzResearch.WordTrace tailWord_263545 prefixEnd_263545 20048186531744683359331 := by
  unfold tailWord_263545
  simp only [CollatzResearch.WordTrace]
  refine ⟨9612275830228949747688089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6408183886819299831792059 9612275830228949747688089)
  ·
    refine ⟨7209206872671712310766067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9612275830228949747688089 7209206872671712310766067)
    ·
      refine ⟨10813810309007568466149101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7209206872671712310766067 10813810309007568466149101)
      ·
        refine ⟨4055178865877838174805913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10813810309007568466149101 4055178865877838174805913)
        ·
          refine ⟨3041384149408378631104435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4055178865877838174805913 3041384149408378631104435)
          ·
            refine ⟨4562076224112567946656653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3041384149408378631104435 4562076224112567946656653)
            ·
              refine ⟨1710778584042212979996245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4562076224112567946656653 1710778584042212979996245)
              ·
                refine ⟨20048186531744683359331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1710778584042212979996245 20048186531744683359331)
                ·
                  rfl

theorem cell21_263545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 3, 8].length) (baseStart_263545 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_263545 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_263545 prefixEnd_263545 := by exact prefixLift 263545
  have htrace : WordTrace (prefixWord ++ tailWord_263545) baseStart_263545 baseEnd_263545 := by
    simpa [prefixWord, tailWord_263545, baseEnd_263545] using wordTrace_append hprefix tailTrace_263545
  have hstable : (prefixWord ++ tailWord_263545).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_263545).length < 2 ^ (prefixWord ++ tailWord_263545).sum := by decide
  have hdescent : baseEnd_263545 < baseStart_263545 := by decide
  rcases family_descends (prefixWord ++ tailWord_263545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_263582 : List Nat := [4, 3, 1, 2, 2, 1, 2, 2, 4]
def baseStart_263582 : Nat := 118140960795 + 263582 * 2 ^ 59
def prefixEnd_263582 : Nat := 4983230072969 + 3 ^ 40 * 263582 * 2
def baseEnd_263582 : Nat := 60153003499330207961251

theorem tailTrace_263582 : CollatzResearch.WordTrace tailWord_263582 prefixEnd_263582 60153003499330207961251 := by
  unfold tailWord_263582
  simp only [CollatzResearch.WordTrace]
  refine ⟨1201703166386863133348125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 6409083554063270044523333 1201703166386863133348125)
  ·
    refine ⟨450638687395073675005547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1201703166386863133348125 450638687395073675005547)
    ·
      refine ⟨675958031092610512508321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 450638687395073675005547 675958031092610512508321)
      ·
        refine ⟨506968523319457884381241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 675958031092610512508321 506968523319457884381241)
        ·
          refine ⟨380226392489593413285931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 506968523319457884381241 380226392489593413285931)
          ·
            refine ⟨570339588734390119928897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 380226392489593413285931 570339588734390119928897)
            ·
              refine ⟨427754691550792589946673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 570339588734390119928897 427754691550792589946673)
              ·
                refine ⟨320816018663094442460005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 427754691550792589946673 320816018663094442460005)
                ·
                  refine ⟨60153003499330207961251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 320816018663094442460005 60153003499330207961251)
                  ·
                    rfl

theorem cell21_263582_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 2, 1, 2, 2, 4].length) (baseStart_263582 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_263582 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_263582 prefixEnd_263582 := by exact prefixLift 263582
  have htrace : WordTrace (prefixWord ++ tailWord_263582) baseStart_263582 baseEnd_263582 := by
    simpa [prefixWord, tailWord_263582, baseEnd_263582] using wordTrace_append hprefix tailTrace_263582
  have hstable : (prefixWord ++ tailWord_263582).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_263582).length < 2 ^ (prefixWord ++ tailWord_263582).sum := by decide
  have hdescent : baseEnd_263582 < baseStart_263582 := by decide
  rcases family_descends (prefixWord ++ tailWord_263582) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_263607 : List Nat := [1, 1, 3, 1, 3, 2, 1, 5, 4]
def baseStart_263607 : Nat := 118140960795 + 263607 * 2 ^ 59
def prefixEnd_263607 : Nat := 4983230072969 + 3 ^ 40 * 263607 * 2
def baseEnd_263607 : Nat := 60158708839935720044533

theorem tailTrace_263607 : CollatzResearch.WordTrace tailWord_263607 prefixEnd_263607 60158708839935720044533 := by
  unfold tailWord_263607
  simp only [CollatzResearch.WordTrace]
  refine ⟨9614537156004334336445075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6409691437336222890963383 9614537156004334336445075)
  ·
    refine ⟨14421805734006501504667613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9614537156004334336445075 14421805734006501504667613)
    ·
      refine ⟨5408177150252438064250355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14421805734006501504667613 5408177150252438064250355)
      ·
        refine ⟨8112265725378657096375533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5408177150252438064250355 8112265725378657096375533)
        ·
          refine ⟨3042099647016996411140825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8112265725378657096375533 3042099647016996411140825)
          ·
            refine ⟨2281574735262747308355619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3042099647016996411140825 2281574735262747308355619)
            ·
              refine ⟨3422362102894120962533429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2281574735262747308355619 3422362102894120962533429)
              ·
                refine ⟨320846447146323840237509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3422362102894120962533429 320846447146323840237509)
                ·
                  refine ⟨60158708839935720044533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 320846447146323840237509 60158708839935720044533)
                  ·
                    rfl

theorem cell21_263607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 1, 5, 4].length) (baseStart_263607 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_263607 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_263607 prefixEnd_263607 := by exact prefixLift 263607
  have htrace : WordTrace (prefixWord ++ tailWord_263607) baseStart_263607 baseEnd_263607 := by
    simpa [prefixWord, tailWord_263607, baseEnd_263607] using wordTrace_append hprefix tailTrace_263607
  have hstable : (prefixWord ++ tailWord_263607).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_263607).length < 2 ^ (prefixWord ++ tailWord_263607).sum := by decide
  have hdescent : baseEnd_263607 < baseStart_263607 := by decide
  rcases family_descends (prefixWord ++ tailWord_263607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_263762 : List Nat := [3, 2, 2, 1, 2, 3, 1, 4, 3]
def baseStart_263762 : Nat := 118140960795 + 263762 * 2 ^ 59
def prefixEnd_263762 : Nat := 4983230072969 + 3 ^ 40 * 263762 * 2
def baseEnd_263762 : Nat := 60194081951689894960883

theorem tailTrace_263762 : CollatzResearch.WordTrace tailWord_263762 prefixEnd_263762 60194081951689894960883 := by
  unfold tailWord_263762
  simp only [CollatzResearch.WordTrace]
  refine ⟨2405047617610698952084385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6413460313628530538891693 2405047617610698952084385)
  ·
    refine ⟨1803785713208024214063289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2405047617610698952084385 1803785713208024214063289)
    ·
      refine ⟨1352839284906018160547467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1803785713208024214063289 1352839284906018160547467)
      ·
        refine ⟨2029258927359027240821201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1352839284906018160547467 2029258927359027240821201)
        ·
          refine ⟨1521944195519270430615901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2029258927359027240821201 1521944195519270430615901)
          ·
            refine ⟨570729073319726411480963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1521944195519270430615901 570729073319726411480963)
            ·
              refine ⟨856093609979589617221445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 570729073319726411480963 856093609979589617221445)
              ·
                refine ⟨160517551871173053229021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 856093609979589617221445 160517551871173053229021)
                ·
                  refine ⟨60194081951689894960883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 160517551871173053229021 60194081951689894960883)
                  ·
                    rfl

theorem cell21_263762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 3, 1, 4, 3].length) (baseStart_263762 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_263762 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_263762 prefixEnd_263762 := by exact prefixLift 263762
  have htrace : WordTrace (prefixWord ++ tailWord_263762) baseStart_263762 baseEnd_263762 := by
    simpa [prefixWord, tailWord_263762, baseEnd_263762] using wordTrace_append hprefix tailTrace_263762
  have hstable : (prefixWord ++ tailWord_263762).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_263762).length < 2 ^ (prefixWord ++ tailWord_263762).sum := by decide
  have hdescent : baseEnd_263762 < baseStart_263762 := by decide
  rcases family_descends (prefixWord ++ tailWord_263762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_263973 : List Nat := [1, 3, 1, 2, 3, 2, 1, 5, 3]
def baseStart_263973 : Nat := 118140960795 + 263973 * 2 ^ 59
def prefixEnd_263973 : Nat := 4983230072969 + 3 ^ 40 * 263973 * 2
def baseEnd_263973 : Nat := 60242235026400416943785

theorem tailTrace_263973 : CollatzResearch.WordTrace tailWord_263973 prefixEnd_263973 60242235026400416943785 := by
  unfold tailWord_263973
  simp only [CollatzResearch.WordTrace]
  refine ⟨9627886272678378844268573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6418590848452252562845715 9627886272678378844268573)
  ·
    refine ⟨3610457352254392066600715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9627886272678378844268573 3610457352254392066600715)
    ·
      refine ⟨5415686028381588099901073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3610457352254392066600715 5415686028381588099901073)
      ·
        refine ⟨4061764521286191074925805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5415686028381588099901073 4061764521286191074925805)
        ·
          refine ⟨1523161695482321653097177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4061764521286191074925805 1523161695482321653097177)
          ·
            refine ⟨1142371271611741239822883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1523161695482321653097177 1142371271611741239822883)
            ·
              refine ⟨1713556907417611859734325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1142371271611741239822883 1713556907417611859734325)
              ·
                refine ⟨160645960070401111850093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1713556907417611859734325 160645960070401111850093)
                ·
                  refine ⟨60242235026400416943785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 160645960070401111850093 60242235026400416943785)
                  ·
                    rfl

theorem cell21_263973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 1, 5, 3].length) (baseStart_263973 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_263973 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_263973 prefixEnd_263973 := by exact prefixLift 263973
  have htrace : WordTrace (prefixWord ++ tailWord_263973) baseStart_263973 baseEnd_263973 := by
    simpa [prefixWord, tailWord_263973, baseEnd_263973] using wordTrace_append hprefix tailTrace_263973
  have hstable : (prefixWord ++ tailWord_263973).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_263973).length < 2 ^ (prefixWord ++ tailWord_263973).sum := by decide
  have hdescent : baseEnd_263973 < baseStart_263973 := by decide
  rcases family_descends (prefixWord ++ tailWord_263973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_263987 : List Nat := [1, 1, 1, 2, 7, 1, 1, 1, 6]
def baseStart_263987 : Nat := 118140960795 + 263987 * 2 ^ 59
def prefixEnd_263987 : Nat := 4983230072969 + 3 ^ 40 * 263987 * 2
def baseEnd_263987 : Nat := 60245430017139503710423

theorem tailTrace_263987 : CollatzResearch.WordTrace tailWord_263987 prefixEnd_263987 60245430017139503710423 := by
  unfold tailWord_263987
  simp only [CollatzResearch.WordTrace]
  refine ⟨9628396894627659235278215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6418931263085106156852143 9628396894627659235278215)
  ·
    refine ⟨14442595341941488852917323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9628396894627659235278215 14442595341941488852917323)
    ·
      refine ⟨21663893012912233279375985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14442595341941488852917323 21663893012912233279375985)
      ·
        refine ⟨16247919759684174959531989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21663893012912233279375985 16247919759684174959531989)
        ·
          refine ⟨380810619367597850614031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 16247919759684174959531989 380810619367597850614031)
          ·
            refine ⟨571215929051396775921047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 380810619367597850614031 571215929051396775921047)
            ·
              refine ⟨856823893577095163881571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 571215929051396775921047 856823893577095163881571)
              ·
                refine ⟨1285235840365642745822357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 856823893577095163881571 1285235840365642745822357)
                ·
                  refine ⟨60245430017139503710423, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1285235840365642745822357 60245430017139503710423)
                  ·
                    rfl

theorem cell21_263987_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 7, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 7, 1, 1, 1, 6].length) (baseStart_263987 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_263987 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_263987 prefixEnd_263987 := by exact prefixLift 263987
  have htrace : WordTrace (prefixWord ++ tailWord_263987) baseStart_263987 baseEnd_263987 := by
    simpa [prefixWord, tailWord_263987, baseEnd_263987] using wordTrace_append hprefix tailTrace_263987
  have hstable : (prefixWord ++ tailWord_263987).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_263987).length < 2 ^ (prefixWord ++ tailWord_263987).sum := by decide
  have hdescent : baseEnd_263987 < baseStart_263987 := by decide
  rcases family_descends (prefixWord ++ tailWord_263987) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_263990 : List Nat := [5, 1, 2, 2, 1, 2, 2, 1, 5]
def baseStart_263990 : Nat := 118140960795 + 263990 * 2 ^ 59
def prefixEnd_263990 : Nat := 4983230072969 + 3 ^ 40 * 263990 * 2
def baseEnd_263990 : Nat := 60246114658012165160417

theorem tailTrace_263990 : CollatzResearch.WordTrace tailWord_263990 prefixEnd_263990 60246114658012165160417 := by
  unfold tailWord_263990
  simp only [CollatzResearch.WordTrace]
  refine ⟨601781644601049421727339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 6419004209077860498424949 601781644601049421727339)
  ·
    refine ⟨902672466901574132591009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 601781644601049421727339 902672466901574132591009)
    ·
      refine ⟨677004350176180599443257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 902672466901574132591009 677004350176180599443257)
      ·
        refine ⟨507753262632135449582443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 677004350176180599443257 507753262632135449582443)
        ·
          refine ⟨761629893948203174373665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 507753262632135449582443 761629893948203174373665)
          ·
            refine ⟨571222420461152380780249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 761629893948203174373665 571222420461152380780249)
            ·
              refine ⟨428416815345864285585187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 571222420461152380780249 428416815345864285585187)
              ·
                refine ⟨642625223018796428377781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 428416815345864285585187 642625223018796428377781)
                ·
                  refine ⟨60246114658012165160417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 642625223018796428377781 60246114658012165160417)
                  ·
                    rfl

theorem cell21_263990_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 2, 2, 1, 5].length) (baseStart_263990 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_263990 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_263990 prefixEnd_263990 := by exact prefixLift 263990
  have htrace : WordTrace (prefixWord ++ tailWord_263990) baseStart_263990 baseEnd_263990 := by
    simpa [prefixWord, tailWord_263990, baseEnd_263990] using wordTrace_append hprefix tailTrace_263990
  have hstable : (prefixWord ++ tailWord_263990).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_263990).length < 2 ^ (prefixWord ++ tailWord_263990).sum := by decide
  have hdescent : baseEnd_263990 < baseStart_263990 := by decide
  rcases family_descends (prefixWord ++ tailWord_263990) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_264018 : List Nat := [3, 2, 2, 1, 1, 3, 4, 5]
def baseStart_264018 : Nat := 118140960795 + 264018 * 2 ^ 59
def prefixEnd_264018 : Nat := 4983230072969 + 3 ^ 40 * 264018 * 2
def baseEnd_264018 : Nat := 20084168213163446231231

theorem tailTrace_264018 : CollatzResearch.WordTrace tailWord_264018 prefixEnd_264018 20084168213163446231231 := by
  unfold tailWord_264018
  simp only [CollatzResearch.WordTrace]
  refine ⟨2407381889378837882414177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6419685038343567686437805 2407381889378837882414177)
  ·
    refine ⟨1805536417034128411810633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2407381889378837882414177 1805536417034128411810633)
    ·
      refine ⟨1354152312775596308857975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1805536417034128411810633 1354152312775596308857975)
      ·
        refine ⟨2031228469163394463286963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1354152312775596308857975 2031228469163394463286963)
        ·
          refine ⟨3046842703745091694930445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2031228469163394463286963 3046842703745091694930445)
          ·
            refine ⟨1142566013904409385598917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3046842703745091694930445 1142566013904409385598917)
            ·
              refine ⟨214231127607076759799797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1142566013904409385598917 214231127607076759799797)
              ·
                refine ⟨20084168213163446231231, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 214231127607076759799797 20084168213163446231231)
                ·
                  rfl

theorem cell21_264018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 4, 5].length) (baseStart_264018 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_264018 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_264018 prefixEnd_264018 := by exact prefixLift 264018
  have htrace : WordTrace (prefixWord ++ tailWord_264018) baseStart_264018 baseEnd_264018 := by
    simpa [prefixWord, tailWord_264018, baseEnd_264018] using wordTrace_append hprefix tailTrace_264018
  have hstable : (prefixWord ++ tailWord_264018).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_264018).length < 2 ^ (prefixWord ++ tailWord_264018).sum := by decide
  have hdescent : baseEnd_264018 < baseStart_264018 := by decide
  rcases family_descends (prefixWord ++ tailWord_264018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_264094 : List Nat := [4, 3, 1, 3, 10]
def baseStart_264094 : Nat := 118140960795 + 264094 * 2 ^ 59
def prefixEnd_264094 : Nat := 4983230072969 + 3 ^ 40 * 264094 * 2
def baseEnd_264094 : Nat := 744072208332482659591

theorem tailTrace_264094 : CollatzResearch.WordTrace tailWord_264094 prefixEnd_264094 744072208332482659591 := by
  unfold tailWord_264094
  simp only [CollatzResearch.WordTrace]
  refine ⟨1204037438155002063677917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 6421533003493344339615557 1204037438155002063677917)
  ·
    refine ⟨451514039308125773879219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1204037438155002063677917 451514039308125773879219)
    ·
      refine ⟨677271058962188660818829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 451514039308125773879219 677271058962188660818829)
      ·
        refine ⟨253976647110820747807061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 677271058962188660818829 253976647110820747807061)
        ·
          refine ⟨744072208332482659591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 10 253976647110820747807061 744072208332482659591)
          ·
            rfl

theorem cell21_264094_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 10].length) (baseStart_264094 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_264094 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_264094 prefixEnd_264094 := by exact prefixLift 264094
  have htrace : WordTrace (prefixWord ++ tailWord_264094) baseStart_264094 baseEnd_264094 := by
    simpa [prefixWord, tailWord_264094, baseEnd_264094] using wordTrace_append hprefix tailTrace_264094
  have hstable : (prefixWord ++ tailWord_264094).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_264094).length < 2 ^ (prefixWord ++ tailWord_264094).sum := by decide
  have hdescent : baseEnd_264094 < baseStart_264094 := by decide
  rcases family_descends (prefixWord ++ tailWord_264094) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_264153 : List Nat := [1, 2, 1, 2, 6, 1, 8]
def baseStart_264153 : Nat := 118140960795 + 264153 * 2 ^ 59
def prefixEnd_264153 : Nat := 4983230072969 + 3 ^ 40 * 264153 * 2
def baseEnd_264153 : Nat := 6698145942084455993713

theorem tailTrace_264153 : CollatzResearch.WordTrace tailWord_264153 prefixEnd_264153 6698145942084455993713 := by
  unfold tailWord_264153
  simp only [CollatzResearch.WordTrace]
  refine ⟨9634451412026269585821113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6422967608017513057214075 9634451412026269585821113)
  ·
    refine ⟨7225838559019702189365835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9634451412026269585821113 7225838559019702189365835)
    ·
      refine ⟨10838757838529553284048753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7225838559019702189365835 10838757838529553284048753)
      ·
        refine ⟨8129068378897164963036565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10838757838529553284048753 8129068378897164963036565)
        ·
          refine ⟨381050080260804607642339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 8129068378897164963036565 381050080260804607642339)
          ·
            refine ⟨571575120391206911463509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 381050080260804607642339 571575120391206911463509)
            ·
              refine ⟨6698145942084455993713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 571575120391206911463509 6698145942084455993713)
              ·
                rfl

theorem cell21_264153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 6, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 6, 1, 8].length) (baseStart_264153 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_264153 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_264153 prefixEnd_264153 := by exact prefixLift 264153
  have htrace : WordTrace (prefixWord ++ tailWord_264153) baseStart_264153 baseEnd_264153 := by
    simpa [prefixWord, tailWord_264153, baseEnd_264153] using wordTrace_append hprefix tailTrace_264153
  have hstable : (prefixWord ++ tailWord_264153).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_264153).length < 2 ^ (prefixWord ++ tailWord_264153).sum := by decide
  have hdescent : baseEnd_264153 < baseStart_264153 := by decide
  rcases family_descends (prefixWord ++ tailWord_264153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_264218 : List Nat := [3, 1, 1, 3, 1, 4, 3, 2, 3]
def baseStart_264218 : Nat := 118140960795 + 264218 * 2 ^ 59
def prefixEnd_264218 : Nat := 4983230072969 + 3 ^ 40 * 264218 * 2
def baseEnd_264218 : Nat := 60298147364334435359951

theorem tailTrace_264218 : CollatzResearch.WordTrace tailWord_264218 prefixEnd_264218 60298147364334435359951 := by
  unfold tailWord_264218
  simp only [CollatzResearch.WordTrace]
  refine ⟨2409205539197696421734327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6424548104527190457958205 2409205539197696421734327)
  ·
    refine ⟨3613808308796544632601491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2409205539197696421734327 3613808308796544632601491)
    ·
      refine ⟨5420712463194816948902237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3613808308796544632601491 5420712463194816948902237)
      ·
        refine ⟨2032767173698056355838339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5420712463194816948902237 2032767173698056355838339)
        ·
          refine ⟨3049150760547084533757509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2032767173698056355838339 3049150760547084533757509)
          ·
            refine ⟨571715767602578350079533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3049150760547084533757509 571715767602578350079533)
            ·
              refine ⟨214393412850966881279825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 571715767602578350079533 214393412850966881279825)
              ·
                refine ⟨160795059638225160959869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 214393412850966881279825 160795059638225160959869)
                ·
                  refine ⟨60298147364334435359951, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 160795059638225160959869 60298147364334435359951)
                  ·
                    rfl

theorem cell21_264218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 4, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 4, 3, 2, 3].length) (baseStart_264218 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_264218 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_264218 prefixEnd_264218 := by exact prefixLift 264218
  have htrace : WordTrace (prefixWord ++ tailWord_264218) baseStart_264218 baseEnd_264218 := by
    simpa [prefixWord, tailWord_264218, baseEnd_264218] using wordTrace_append hprefix tailTrace_264218
  have hstable : (prefixWord ++ tailWord_264218).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_264218).length < 2 ^ (prefixWord ++ tailWord_264218).sum := by decide
  have hdescent : baseEnd_264218 < baseStart_264218 := by decide
  rcases family_descends (prefixWord ++ tailWord_264218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_264229 : List Nat := [1, 3, 1, 2, 2, 4, 2, 6]
def baseStart_264229 : Nat := 118140960795 + 264229 * 2 ^ 59
def prefixEnd_264229 : Nat := 4983230072969 + 3 ^ 40 * 264229 * 2
def baseEnd_264229 : Nat := 20100219238066953558865

theorem tailTrace_264229 : CollatzResearch.WordTrace tailWord_264229 prefixEnd_264229 20100219238066953558865 := by
  unfold tailWord_264229
  simp only [CollatzResearch.WordTrace]
  refine ⟨9637223359750934565587741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6424815573167289710391827 9637223359750934565587741)
  ·
    refine ⟨3613958759906600462095403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9637223359750934565587741 3613958759906600462095403)
    ·
      refine ⟨5420938139859900693143105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3613958759906600462095403 5420938139859900693143105)
      ·
        refine ⟨4065703604894925519857329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5420938139859900693143105 4065703604894925519857329)
        ·
          refine ⟨3049277703671194139892997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4065703604894925519857329 3049277703671194139892997)
          ·
            refine ⟨571739569438348901229937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3049277703671194139892997 571739569438348901229937)
            ·
              refine ⟨428804677078761675922453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 571739569438348901229937 428804677078761675922453)
              ·
                refine ⟨20100219238066953558865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 428804677078761675922453 20100219238066953558865)
                ·
                  rfl

theorem cell21_264229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 4, 2, 6].length) (baseStart_264229 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_264229 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_264229 prefixEnd_264229 := by exact prefixLift 264229
  have htrace : WordTrace (prefixWord ++ tailWord_264229) baseStart_264229 baseEnd_264229 := by
    simpa [prefixWord, tailWord_264229, baseEnd_264229] using wordTrace_append hprefix tailTrace_264229
  have hstable : (prefixWord ++ tailWord_264229).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_264229).length < 2 ^ (prefixWord ++ tailWord_264229).sum := by decide
  have hdescent : baseEnd_264229 < baseStart_264229 := by decide
  rcases family_descends (prefixWord ++ tailWord_264229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_264243 : List Nat := [1, 1, 1, 2, 4, 1, 2, 4, 5]
def baseStart_264243 : Nat := 118140960795 + 264243 * 2 ^ 59
def prefixEnd_264243 : Nat := 4983230072969 + 3 ^ 40 * 264243 * 2
def baseEnd_264243 : Nat := 60303852704939947443233

theorem tailTrace_264243 : CollatzResearch.WordTrace tailWord_264243 prefixEnd_264243 60303852704939947443233 := by
  unfold tailWord_264243
  simp only [CollatzResearch.WordTrace]
  refine ⟨9637733981700214956597383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6425155987800143304398255 9637733981700214956597383)
  ·
    refine ⟨14456600972550322434896075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9637733981700214956597383 14456600972550322434896075)
    ·
      refine ⟨21684901458825483652344113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14456600972550322434896075 21684901458825483652344113)
      ·
        refine ⟨16263676094119112739258085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21684901458825483652344113 16263676094119112739258085)
        ·
          refine ⟨3049439267647333638610891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 16263676094119112739258085 3049439267647333638610891)
          ·
            refine ⟨4574158901471000457916337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3049439267647333638610891 4574158901471000457916337)
            ·
              refine ⟨3430619176103250343437253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4574158901471000457916337 3430619176103250343437253)
              ·
                refine ⟨643241095519359439394485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3430619176103250343437253 643241095519359439394485)
                ·
                  refine ⟨60303852704939947443233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 643241095519359439394485 60303852704939947443233)
                  ·
                    rfl

theorem cell21_264243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 2, 4, 5].length) (baseStart_264243 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_264243 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_264243 prefixEnd_264243 := by exact prefixLift 264243
  have htrace : WordTrace (prefixWord ++ tailWord_264243) baseStart_264243 baseEnd_264243 := by
    simpa [prefixWord, tailWord_264243, baseEnd_264243] using wordTrace_append hprefix tailTrace_264243
  have hstable : (prefixWord ++ tailWord_264243).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_264243).length < 2 ^ (prefixWord ++ tailWord_264243).sum := by decide
  have hdescent : baseEnd_264243 < baseStart_264243 := by decide
  rcases family_descends (prefixWord ++ tailWord_264243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_264277 : List Nat := [1, 3, 2, 2, 1, 4, 1, 4, 3]
def baseStart_264277 : Nat := 118140960795 + 264277 * 2 ^ 59
def prefixEnd_264277 : Nat := 4983230072969 + 3 ^ 40 * 264277 * 2
def baseEnd_264277 : Nat := 60311611968163443876497

theorem tailTrace_264277 : CollatzResearch.WordTrace tailWord_264277 prefixEnd_264277 60311611968163443876497 := by
  unfold tailWord_264277
  simp only [CollatzResearch.WordTrace]
  refine ⟨9638974063577038763335085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6425982709051359175556723 9638974063577038763335085)
  ·
    refine ⟨3614615273841389536250657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9638974063577038763335085 3614615273841389536250657)
    ·
      refine ⟨2710961455381042152187993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3614615273841389536250657 2710961455381042152187993)
      ·
        refine ⟨2033221091535781614140995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2710961455381042152187993 2033221091535781614140995)
        ·
          refine ⟨3049831637303672421211493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2033221091535781614140995 3049831637303672421211493)
          ·
            refine ⟨571843431994438578977155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3049831637303672421211493 571843431994438578977155)
            ·
              refine ⟨857765147991657868465733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 571843431994438578977155 857765147991657868465733)
              ·
                refine ⟨160830965248435850337325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 857765147991657868465733 160830965248435850337325)
                ·
                  refine ⟨60311611968163443876497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 160830965248435850337325 60311611968163443876497)
                  ·
                    rfl

theorem cell21_264277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 4, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 4, 1, 4, 3].length) (baseStart_264277 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_264277 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_264277 prefixEnd_264277 := by exact prefixLift 264277
  have htrace : WordTrace (prefixWord ++ tailWord_264277) baseStart_264277 baseEnd_264277 := by
    simpa [prefixWord, tailWord_264277, baseEnd_264277] using wordTrace_append hprefix tailTrace_264277
  have hstable : (prefixWord ++ tailWord_264277).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_264277).length < 2 ^ (prefixWord ++ tailWord_264277).sum := by decide
  have hdescent : baseEnd_264277 < baseStart_264277 := by decide
  rcases family_descends (prefixWord ++ tailWord_264277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_264305 : List Nat := [1, 2, 2, 2, 1, 1, 7, 5]
def baseStart_264305 : Nat := 118140960795 + 264305 * 2 ^ 59
def prefixEnd_264305 : Nat := 4983230072969 + 3 ^ 40 * 264305 * 2
def baseEnd_264305 : Nat := 20106000649880539136591

theorem tailTrace_264305 : CollatzResearch.WordTrace tailWord_264305 prefixEnd_264305 20106000649880539136591 := by
  unfold tailWord_264305
  simp only [CollatzResearch.WordTrace]
  refine ⟨9639995307475599545354369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6426663538317066363569579 9639995307475599545354369)
  ·
    refine ⟨7229996480606699659015777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9639995307475599545354369 7229996480606699659015777)
    ·
      refine ⟨5422497360455024744261833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7229996480606699659015777 5422497360455024744261833)
      ·
        refine ⟨4066873020341268558196375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5422497360455024744261833 4066873020341268558196375)
        ·
          refine ⟨6100309530511902837294563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4066873020341268558196375 6100309530511902837294563)
          ·
            refine ⟨9150464295767854255941845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6100309530511902837294563 9150464295767854255941845)
            ·
              refine ⟨214464006932059084123637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 9150464295767854255941845 214464006932059084123637)
              ·
                refine ⟨20106000649880539136591, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 214464006932059084123637 20106000649880539136591)
                ·
                  rfl

theorem cell21_264305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 7, 5].length) (baseStart_264305 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_264305 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_264305 prefixEnd_264305 := by exact prefixLift 264305
  have htrace : WordTrace (prefixWord ++ tailWord_264305) baseStart_264305 baseEnd_264305 := by
    simpa [prefixWord, tailWord_264305, baseEnd_264305] using wordTrace_append hprefix tailTrace_264305
  have hstable : (prefixWord ++ tailWord_264305).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_264305).length < 2 ^ (prefixWord ++ tailWord_264305).sum := by decide
  have hdescent : baseEnd_264305 < baseStart_264305 := by decide
  rcases family_descends (prefixWord ++ tailWord_264305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_264336 : List Nat := [2, 1, 1, 1, 1, 1, 5, 6, 3]
def baseStart_264336 : Nat := 118140960795 + 264336 * 2 ^ 59
def prefixEnd_264336 : Nat := 4983230072969 + 3 ^ 40 * 264336 * 2
def baseEnd_264336 : Nat := 60325076571992452393043

theorem tailTrace_264336 : CollatzResearch.WordTrace tailWord_264336 prefixEnd_264336 60325076571992452393043 := by
  unfold tailWord_264336
  simp only [CollatzResearch.WordTrace]
  refine ⟨4820562985181645919866431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6427417313575527893155241 4820562985181645919866431)
  ·
    refine ⟨7230844477772468879799647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4820562985181645919866431 7230844477772468879799647)
    ·
      refine ⟨10846266716658703319699471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7230844477772468879799647 10846266716658703319699471)
      ·
        refine ⟨16269400074988054979549207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10846266716658703319699471 16269400074988054979549207)
        ·
          refine ⟨24404100112482082469323811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16269400074988054979549207 24404100112482082469323811)
          ·
            refine ⟨36606150168723123703985717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24404100112482082469323811 36606150168723123703985717)
            ·
              refine ⟨3431826578317792847248661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 36606150168723123703985717 3431826578317792847248661)
              ·
                refine ⟨160866870858646539714781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3431826578317792847248661 160866870858646539714781)
                ·
                  refine ⟨60325076571992452393043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 160866870858646539714781 60325076571992452393043)
                  ·
                    rfl

theorem cell21_264336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 5, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 5, 6, 3].length) (baseStart_264336 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_264336 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_264336 prefixEnd_264336 := by exact prefixLift 264336
  have htrace : WordTrace (prefixWord ++ tailWord_264336) baseStart_264336 baseEnd_264336 := by
    simpa [prefixWord, tailWord_264336, baseEnd_264336] using wordTrace_append hprefix tailTrace_264336
  have hstable : (prefixWord ++ tailWord_264336).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_264336).length < 2 ^ (prefixWord ++ tailWord_264336).sum := by decide
  have hdescent : baseEnd_264336 < baseStart_264336 := by decide
  rcases family_descends (prefixWord ++ tailWord_264336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_264457 : List Nat := [1, 2, 1, 1, 3, 6, 1, 6]
def baseStart_264457 : Nat := 118140960795 + 264457 * 2 ^ 59
def prefixEnd_264457 : Nat := 4983230072969 + 3 ^ 40 * 264457 * 2
def baseEnd_264457 : Nat := 20117563473507710292043

theorem tailTrace_264457 : CollatzResearch.WordTrace tailWord_264457 prefixEnd_264457 20117563473507710292043 := by
  unfold tailWord_264457
  simp only [CollatzResearch.WordTrace]
  refine ⟨9645539202924929504887625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6430359468616619669925083 9645539202924929504887625)
  ·
    refine ⟨7234154402193697128665719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9645539202924929504887625 7234154402193697128665719)
    ·
      refine ⟨10851231603290545692998579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7234154402193697128665719 10851231603290545692998579)
      ·
        refine ⟨16276847404935818539497869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10851231603290545692998579 16276847404935818539497869)
        ·
          refine ⟨6103817776850931952311701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16276847404935818539497869 6103817776850931952311701)
          ·
            refine ⟨286116458289887435264611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 6103817776850931952311701 286116458289887435264611)
            ·
              refine ⟨429174687434831152896917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 286116458289887435264611 429174687434831152896917)
              ·
                refine ⟨20117563473507710292043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 429174687434831152896917 20117563473507710292043)
                ·
                  rfl

theorem cell21_264457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 6, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 6, 1, 6].length) (baseStart_264457 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_264457 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_264457 prefixEnd_264457 := by exact prefixLift 264457
  have htrace : WordTrace (prefixWord ++ tailWord_264457) baseStart_264457 baseEnd_264457 := by
    simpa [prefixWord, tailWord_264457, baseEnd_264457] using wordTrace_append hprefix tailTrace_264457
  have hstable : (prefixWord ++ tailWord_264457).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_264457).length < 2 ^ (prefixWord ++ tailWord_264457).sum := by decide
  have hdescent : baseEnd_264457 < baseStart_264457 := by decide
  rcases family_descends (prefixWord ++ tailWord_264457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_264471 : List Nat := [1, 1, 3, 4, 1, 2, 1, 1, 7]
def baseStart_264471 : Nat := 118140960795 + 264471 * 2 ^ 59
def prefixEnd_264471 : Nat := 4983230072969 + 3 ^ 40 * 264471 * 2
def baseEnd_264471 : Nat := 60355885411262217642767

theorem tailTrace_264471 : CollatzResearch.WordTrace tailWord_264471 prefixEnd_264471 60355885411262217642767 := by
  unfold tailWord_264471
  simp only [CollatzResearch.WordTrace]
  refine ⟨9646049824874209895897267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6430699883249473263931511 9646049824874209895897267)
  ·
    refine ⟨14469074737311314843845901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9646049824874209895897267 14469074737311314843845901)
    ·
      refine ⟨5425903026491743066442213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14469074737311314843845901 5425903026491743066442213)
      ·
        refine ⟨1017356817467201824957915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5425903026491743066442213 1017356817467201824957915)
        ·
          refine ⟨1526035226200802737436873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1017356817467201824957915 1526035226200802737436873)
          ·
            refine ⟨1144526419650602053077655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1526035226200802737436873 1144526419650602053077655)
            ·
              refine ⟨1716789629475903079616483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1144526419650602053077655 1716789629475903079616483)
              ·
                refine ⟨2575184444213854619424725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1716789629475903079616483 2575184444213854619424725)
                ·
                  refine ⟨60355885411262217642767, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2575184444213854619424725 60355885411262217642767)
                  ·
                    rfl

theorem cell21_264471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 1, 1, 7].length) (baseStart_264471 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_264471 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_264471 prefixEnd_264471 := by exact prefixLift 264471
  have htrace : WordTrace (prefixWord ++ tailWord_264471) baseStart_264471 baseEnd_264471 := by
    simpa [prefixWord, tailWord_264471, baseEnd_264471] using wordTrace_append hprefix tailTrace_264471
  have hstable : (prefixWord ++ tailWord_264471).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_264471).length < 2 ^ (prefixWord ++ tailWord_264471).sum := by decide
  have hdescent : baseEnd_264471 < baseStart_264471 := by decide
  rcases family_descends (prefixWord ++ tailWord_264471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_264474 : List Nat := [3, 1, 1, 3, 4, 1, 3, 5]
def baseStart_264474 : Nat := 118140960795 + 264474 * 2 ^ 59
def prefixEnd_264474 : Nat := 4983230072969 + 3 ^ 40 * 264474 * 2
def baseEnd_264474 : Nat := 20118856684044959697587

theorem tailTrace_264474 : CollatzResearch.WordTrace tailWord_264474 prefixEnd_264474 20118856684044959697587 := by
  unfold tailWord_264474
  simp only [CollatzResearch.WordTrace]
  refine ⟨2411539810965835352064119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6430772829242227605504317 2411539810965835352064119)
  ·
    refine ⟨3617309716448753028096179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2411539810965835352064119 3617309716448753028096179)
    ·
      refine ⟨5425964574673129542144269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3617309716448753028096179 5425964574673129542144269)
      ·
        refine ⟨2034736715502423578304101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5425964574673129542144269 2034736715502423578304101)
        ·
          refine ⟨381513134156704420932019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2034736715502423578304101 381513134156704420932019)
          ·
            refine ⟨572269701235056631398029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 381513134156704420932019 572269701235056631398029)
            ·
              refine ⟨214601137963146236774261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 572269701235056631398029 214601137963146236774261)
              ·
                refine ⟨20118856684044959697587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 214601137963146236774261 20118856684044959697587)
                ·
                  rfl

theorem cell21_264474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 4, 1, 3, 5].length) (baseStart_264474 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_264474 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_264474 prefixEnd_264474 := by exact prefixLift 264474
  have htrace : WordTrace (prefixWord ++ tailWord_264474) baseStart_264474 baseEnd_264474 := by
    simpa [prefixWord, tailWord_264474, baseEnd_264474] using wordTrace_append hprefix tailTrace_264474
  have hstable : (prefixWord ++ tailWord_264474).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_264474).length < 2 ^ (prefixWord ++ tailWord_264474).sum := by decide
  have hdescent : baseEnd_264474 < baseStart_264474 := by decide
  rcases family_descends (prefixWord ++ tailWord_264474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_264494 : List Nat := [4, 1, 3, 3, 2, 1, 1, 2, 4]
def baseStart_264494 : Nat := 118140960795 + 264494 * 2 ^ 59
def prefixEnd_264494 : Nat := 4983230072969 + 3 ^ 40 * 264494 * 2
def baseEnd_264494 : Nat := 60361134324619288759387

theorem tailTrace_264494 : CollatzResearch.WordTrace tailWord_264494 prefixEnd_264494 60361134324619288759387 := by
  unfold tailWord_264494
  simp only [CollatzResearch.WordTrace]
  refine ⟨1205861087973860602998067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 6431259135860589882656357 1205861087973860602998067)
  ·
    refine ⟨1808791631960790904497101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1205861087973860602998067 1808791631960790904497101)
    ·
      refine ⟨678296861985296589186413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1808791631960790904497101 678296861985296589186413)
      ·
        refine ⟨254361323244486220944905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 678296861985296589186413 254361323244486220944905)
        ·
          refine ⟨190770992433364665708679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 254361323244486220944905 190770992433364665708679)
          ·
            refine ⟨286156488650046998563019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 190770992433364665708679 286156488650046998563019)
            ·
              refine ⟨429234732975070497844529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 286156488650046998563019 429234732975070497844529)
              ·
                refine ⟨321926049731302873383397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 429234732975070497844529 321926049731302873383397)
                ·
                  refine ⟨60361134324619288759387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 321926049731302873383397 60361134324619288759387)
                  ·
                    rfl

theorem cell21_264494_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 2, 1, 1, 2, 4].length) (baseStart_264494 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_264494 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_264494 prefixEnd_264494 := by exact prefixLift 264494
  have htrace : WordTrace (prefixWord ++ tailWord_264494) baseStart_264494 baseEnd_264494 := by
    simpa [prefixWord, tailWord_264494, baseEnd_264494] using wordTrace_append hprefix tailTrace_264494
  have hstable : (prefixWord ++ tailWord_264494).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_264494).length < 2 ^ (prefixWord ++ tailWord_264494).sum := by decide
  have hdescent : baseEnd_264494 < baseStart_264494 := by decide
  rcases family_descends (prefixWord ++ tailWord_264494) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_264505 : List Nat := [1, 2, 1, 6, 1, 1, 2, 4, 3]
def baseStart_264505 : Nat := 118140960795 + 264505 * 2 ^ 59
def prefixEnd_264505 : Nat := 4983230072969 + 3 ^ 40 * 264505 * 2
def baseEnd_264505 : Nat := 60363644674485714076031

theorem tailTrace_264505 : CollatzResearch.WordTrace tailWord_264505 prefixEnd_264505 60363644674485714076031 := by
  unfold tailWord_264505
  simp only [CollatzResearch.WordTrace]
  refine ⟨9647289906751033702634969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6431526604500689135089979 9647289906751033702634969)
  ·
    refine ⟨7235467430063275276976227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9647289906751033702634969 7235467430063275276976227)
    ·
      refine ⟨10853201145094912915464341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7235467430063275276976227 10853201145094912915464341)
      ·
        refine ⟨508743803676324042912391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 10853201145094912915464341 508743803676324042912391)
        ·
          refine ⟨763115705514486064368587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 508743803676324042912391 763115705514486064368587)
          ·
            refine ⟨1144673558271729096552881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 763115705514486064368587 1144673558271729096552881)
            ·
              refine ⟨858505168703796822414661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1144673558271729096552881 858505168703796822414661)
              ·
                refine ⟨160969719131961904202749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 858505168703796822414661 160969719131961904202749)
                ·
                  refine ⟨60363644674485714076031, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 160969719131961904202749 60363644674485714076031)
                  ·
                    rfl

theorem cell21_264505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 2, 4, 3].length) (baseStart_264505 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_264505 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_264505 prefixEnd_264505 := by exact prefixLift 264505
  have htrace : WordTrace (prefixWord ++ tailWord_264505) baseStart_264505 baseEnd_264505 := by
    simpa [prefixWord, tailWord_264505, baseEnd_264505] using wordTrace_append hprefix tailTrace_264505
  have hstable : (prefixWord ++ tailWord_264505).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_264505).length < 2 ^ (prefixWord ++ tailWord_264505).sum := by decide
  have hdescent : baseEnd_264505 < baseStart_264505 := by decide
  rcases family_descends (prefixWord ++ tailWord_264505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_264519 : List Nat := [1, 1, 4, 1, 2, 2, 5, 1, 4]
def baseStart_264519 : Nat := 118140960795 + 264519 * 2 ^ 59
def prefixEnd_264519 : Nat := 4983230072969 + 3 ^ 40 * 264519 * 2
def baseEnd_264519 : Nat := 60366839665224800842669

theorem tailTrace_264519 : CollatzResearch.WordTrace tailWord_264519 prefixEnd_264519 60366839665224800842669 := by
  unfold tailWord_264519
  simp only [CollatzResearch.WordTrace]
  refine ⟨9647800528700314093644611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6431867019133542729096407 9647800528700314093644611)
  ·
    refine ⟨14471700793050471140466917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9647800528700314093644611 14471700793050471140466917)
    ·
      refine ⟨2713443898696963338837547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 14471700793050471140466917 2713443898696963338837547)
      ·
        refine ⟨4070165848045445008256321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2713443898696963338837547 4070165848045445008256321)
        ·
          refine ⟨3052624386034083756192241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4070165848045445008256321 3052624386034083756192241)
          ·
            refine ⟨2289468289525562817144181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3052624386034083756192241 2289468289525562817144181)
            ·
              refine ⟨214637652143021514107267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 2289468289525562817144181 214637652143021514107267)
              ·
                refine ⟨321956478214532271160901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 214637652143021514107267 321956478214532271160901)
                ·
                  refine ⟨60366839665224800842669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 321956478214532271160901 60366839665224800842669)
                  ·
                    rfl

theorem cell21_264519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 5, 1, 4].length) (baseStart_264519 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_264519 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_264519 prefixEnd_264519 := by exact prefixLift 264519
  have htrace : WordTrace (prefixWord ++ tailWord_264519) baseStart_264519 baseEnd_264519 := by
    simpa [prefixWord, tailWord_264519, baseEnd_264519] using wordTrace_append hprefix tailTrace_264519
  have hstable : (prefixWord ++ tailWord_264519).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_264519).length < 2 ^ (prefixWord ++ tailWord_264519).sum := by decide
  have hdescent : baseEnd_264519 < baseStart_264519 := by decide
  rcases family_descends (prefixWord ++ tailWord_264519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_264533 : List Nat := [1, 3, 2, 2, 4, 1, 1, 7]
def baseStart_264533 : Nat := 118140960795 + 264533 * 2 ^ 59
def prefixEnd_264533 : Nat := 4983230072969 + 3 ^ 40 * 264533 * 2
def baseEnd_264533 : Nat := 20123344885321295869769

theorem tailTrace_264533 : CollatzResearch.WordTrace tailWord_264533 prefixEnd_264533 20123344885321295869769 := by
  unfold tailWord_264533
  simp only [CollatzResearch.WordTrace]
  refine ⟨9648311150649594484654253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6432207433766396323102835 9648311150649594484654253)
  ·
    refine ⟨3618116681493597931745345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9648311150649594484654253 3618116681493597931745345)
    ·
      refine ⟨2713587511120198448809009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3618116681493597931745345 2713587511120198448809009)
      ·
        refine ⟨2035190633340148836606757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2713587511120198448809009 2035190633340148836606757)
        ·
          refine ⟨381598243751277906863767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2035190633340148836606757 381598243751277906863767)
          ·
            refine ⟨572397365626916860295651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 381598243751277906863767 572397365626916860295651)
            ·
              refine ⟨858596048440375290443477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 572397365626916860295651 858596048440375290443477)
              ·
                refine ⟨20123344885321295869769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 858596048440375290443477 20123344885321295869769)
                ·
                  rfl

theorem cell21_264533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 4, 1, 1, 7].length) (baseStart_264533 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_264533 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_264533 prefixEnd_264533 := by exact prefixLift 264533
  have htrace : WordTrace (prefixWord ++ tailWord_264533) baseStart_264533 baseEnd_264533 := by
    simpa [prefixWord, tailWord_264533, baseEnd_264533] using wordTrace_append hprefix tailTrace_264533
  have hstable : (prefixWord ++ tailWord_264533).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_264533).length < 2 ^ (prefixWord ++ tailWord_264533).sum := by decide
  have hdescent : baseEnd_264533 < baseStart_264533 := by decide
  rcases family_descends (prefixWord ++ tailWord_264533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_264609 : List Nat := [1, 2, 3, 5, 1, 9]
def baseStart_264609 : Nat := 118140960795 + 264609 * 2 ^ 59
def prefixEnd_264609 : Nat := 4983230072969 + 3 ^ 40 * 264609 * 2
def baseEnd_264609 : Nat := 2236569588570542383055

theorem tailTrace_264609 : CollatzResearch.WordTrace tailWord_264609 prefixEnd_264609 2236569588570542383055 := by
  unfold tailWord_264609
  simp only [CollatzResearch.WordTrace]
  refine ⟨9651083098374259464420881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6434055398916172976280587 9651083098374259464420881)
  ·
    refine ⟨7238312323780694598315661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9651083098374259464420881 7238312323780694598315661)
    ·
      refine ⟨2714367121417760474368373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7238312323780694598315661 2714367121417760474368373)
      ·
        refine ⟨254471917632915044472035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 2714367121417760474368373 254471917632915044472035)
        ·
          refine ⟨381707876449372566708053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 254471917632915044472035 381707876449372566708053)
          ·
            refine ⟨2236569588570542383055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 381707876449372566708053 2236569588570542383055)
            ·
              rfl

theorem cell21_264609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 1, 9].length) (baseStart_264609 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_264609 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_264609 prefixEnd_264609 := by exact prefixLift 264609
  have htrace : WordTrace (prefixWord ++ tailWord_264609) baseStart_264609 baseEnd_264609 := by
    simpa [prefixWord, tailWord_264609, baseEnd_264609] using wordTrace_append hprefix tailTrace_264609
  have hstable : (prefixWord ++ tailWord_264609).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_264609).length < 2 ^ (prefixWord ++ tailWord_264609).sum := by decide
  have hdescent : baseEnd_264609 < baseStart_264609 := by decide
  rcases family_descends (prefixWord ++ tailWord_264609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_264671 : List Nat := [1, 1, 2, 3, 3, 4, 1, 2, 4]
def baseStart_264671 : Nat := 118140960795 + 264671 * 2 ^ 59
def prefixEnd_264671 : Nat := 4983230072969 + 3 ^ 40 * 264671 * 2
def baseEnd_264671 : Nat := 60401528136106314309025

theorem tailTrace_264671 : CollatzResearch.WordTrace tailWord_264671 prefixEnd_264671 60401528136106314309025 := by
  unfold tailWord_264671
  simp only [CollatzResearch.WordTrace]
  refine ⟨9653344424149644053177867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6435562949433096035451911 9653344424149644053177867)
  ·
    refine ⟨14480016636224466079766801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9653344424149644053177867 14480016636224466079766801)
    ·
      refine ⟨10860012477168349559825101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14480016636224466079766801 10860012477168349559825101)
      ·
        refine ⟨4072504678938131084934413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10860012477168349559825101 4072504678938131084934413)
        ·
          refine ⟨1527189254601799156850405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4072504678938131084934413 1527189254601799156850405)
          ·
            refine ⟨286347985237837341909451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1527189254601799156850405 286347985237837341909451)
            ·
              refine ⟨429521977856756012864177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 286347985237837341909451 429521977856756012864177)
              ·
                refine ⟨322141483392567009648133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 429521977856756012864177 322141483392567009648133)
                ·
                  refine ⟨60401528136106314309025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 322141483392567009648133 60401528136106314309025)
                  ·
                    rfl

theorem cell21_264671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 4, 1, 2, 4].length) (baseStart_264671 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_264671 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_264671 prefixEnd_264671 := by exact prefixLift 264671
  have htrace : WordTrace (prefixWord ++ tailWord_264671) baseStart_264671 baseEnd_264671 := by
    simpa [prefixWord, tailWord_264671, baseEnd_264671] using wordTrace_append hprefix tailTrace_264671
  have hstable : (prefixWord ++ tailWord_264671).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_264671).length < 2 ^ (prefixWord ++ tailWord_264671).sum := by decide
  have hdescent : baseEnd_264671 < baseStart_264671 := by decide
  rcases family_descends (prefixWord ++ tailWord_264671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_264674 : List Nat := [3, 3, 3, 2, 1, 1, 2, 1, 5]
def baseStart_264674 : Nat := 118140960795 + 264674 * 2 ^ 59
def prefixEnd_264674 : Nat := 4983230072969 + 3 ^ 40 * 264674 * 2
def baseEnd_264674 : Nat := 60402212776978975759019

theorem tailTrace_264674 : CollatzResearch.WordTrace tailWord_264674 prefixEnd_264674 60402212776978975759019 := by
  unfold tailWord_264674
  simp only [CollatzResearch.WordTrace]
  refine ⟨2413363460784693891384269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6435635895425850377024717 2413363460784693891384269)
  ·
    refine ⟨905011297794260209269101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2413363460784693891384269 905011297794260209269101)
    ·
      refine ⟨339379236672847578475913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 905011297794260209269101 339379236672847578475913)
      ·
        refine ⟨254534427504635683856935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 339379236672847578475913 254534427504635683856935)
        ·
          refine ⟨381801641256953525785403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 254534427504635683856935 381801641256953525785403)
          ·
            refine ⟨572702461885430288678105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 381801641256953525785403 572702461885430288678105)
            ·
              refine ⟨429526846414072716508579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 572702461885430288678105 429526846414072716508579)
              ·
                refine ⟨644290269621109074762869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 429526846414072716508579 644290269621109074762869)
                ·
                  refine ⟨60402212776978975759019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 644290269621109074762869 60402212776978975759019)
                  ·
                    rfl

theorem cell21_264674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 1, 1, 2, 1, 5].length) (baseStart_264674 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_264674 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_264674 prefixEnd_264674 := by exact prefixLift 264674
  have htrace : WordTrace (prefixWord ++ tailWord_264674) baseStart_264674 baseEnd_264674 := by
    simpa [prefixWord, tailWord_264674, baseEnd_264674] using wordTrace_append hprefix tailTrace_264674
  have hstable : (prefixWord ++ tailWord_264674).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_264674).length < 2 ^ (prefixWord ++ tailWord_264674).sum := by decide
  have hdescent : baseEnd_264674 < baseStart_264674 := by decide
  rcases family_descends (prefixWord ++ tailWord_264674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_264789 : List Nat := [1, 3, 2, 2, 1, 1, 2, 3, 6]
def baseStart_264789 : Nat := 118140960795 + 264789 * 2 ^ 59
def prefixEnd_264789 : Nat := 4983230072969 + 3 ^ 40 * 264789 * 2
def baseEnd_264789 : Nat := 60428457343764331342117

theorem tailTrace_264789 : CollatzResearch.WordTrace tailWord_264789 prefixEnd_264789 60428457343764331342117 := by
  unfold tailWord_264789
  simp only [CollatzResearch.WordTrace]
  refine ⟨9657648237722150205973421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6438432158481433470648947 9657648237722150205973421)
  ·
    refine ⟨3621618089145806327240033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9657648237722150205973421 3621618089145806327240033)
    ·
      refine ⟨2716213566859354745430025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3621618089145806327240033 2716213566859354745430025)
      ·
        refine ⟨2037160175144516059072519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2716213566859354745430025 2037160175144516059072519)
        ·
          refine ⟨3055740262716774088608779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2037160175144516059072519 3055740262716774088608779)
          ·
            refine ⟨4583610394075161132913169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3055740262716774088608779 4583610394075161132913169)
            ·
              refine ⟨3437707795556370849684877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4583610394075161132913169 3437707795556370849684877)
              ·
                refine ⟨1289140423333639068631829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3437707795556370849684877 1289140423333639068631829)
                ·
                  refine ⟨60428457343764331342117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1289140423333639068631829 60428457343764331342117)
                  ·
                    rfl

theorem cell21_264789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 2, 3, 6].length) (baseStart_264789 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_264789 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_264789 prefixEnd_264789 := by exact prefixLift 264789
  have htrace : WordTrace (prefixWord ++ tailWord_264789) baseStart_264789 baseEnd_264789 := by
    simpa [prefixWord, tailWord_264789, baseEnd_264789] using wordTrace_append hprefix tailTrace_264789
  have hstable : (prefixWord ++ tailWord_264789).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_264789).length < 2 ^ (prefixWord ++ tailWord_264789).sum := by decide
  have hdescent : baseEnd_264789 < baseStart_264789 := by decide
  rcases family_descends (prefixWord ++ tailWord_264789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_264871 : List Nat := [1, 1, 6, 3, 1, 2, 2, 5]
def baseStart_264871 : Nat := 118140960795 + 264871 * 2 ^ 59
def prefixEnd_264871 : Nat := 4983230072969 + 3 ^ 40 * 264871 * 2
def baseEnd_264871 : Nat := 20149056953650136991761

theorem tailTrace_264871 : CollatzResearch.WordTrace tailWord_264871 prefixEnd_264871 20149056953650136991761 := by
  unfold tailWord_264871
  simp only [CollatzResearch.WordTrace]
  refine ⟨9660639023425078210458467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6440426015616718806972311 9660639023425078210458467)
  ·
    refine ⟨14490958535137617315687701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9660639023425078210458467 14490958535137617315687701)
    ·
      refine ⟨679263681334575811672861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 14490958535137617315687701 679263681334575811672861)
      ·
        refine ⟨254723880500465929377323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 679263681334575811672861 254723880500465929377323)
        ·
          refine ⟨382085820750698894065985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 254723880500465929377323 382085820750698894065985)
          ·
            refine ⟨286564365563024170549489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 382085820750698894065985 286564365563024170549489)
            ·
              refine ⟨214923274172268127912117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 286564365563024170549489 214923274172268127912117)
              ·
                refine ⟨20149056953650136991761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 214923274172268127912117 20149056953650136991761)
                ·
                  rfl

theorem cell21_264871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 1, 2, 2, 5].length) (baseStart_264871 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_264871 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_264871 prefixEnd_264871 := by exact prefixLift 264871
  have htrace : WordTrace (prefixWord ++ tailWord_264871) baseStart_264871 baseEnd_264871 := by
    simpa [prefixWord, tailWord_264871, baseEnd_264871] using wordTrace_append hprefix tailTrace_264871
  have hstable : (prefixWord ++ tailWord_264871).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_264871).length < 2 ^ (prefixWord ++ tailWord_264871).sum := by decide
  have hdescent : baseEnd_264871 < baseStart_264871 := by decide
  rcases family_descends (prefixWord ++ tailWord_264871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_264885 : List Nat := [1, 3, 3, 3, 1, 1, 3, 3, 3]
def baseStart_264885 : Nat := 118140960795 + 264885 * 2 ^ 59
def prefixEnd_264885 : Nat := 4983230072969 + 3 ^ 40 * 264885 * 2
def baseEnd_264885 : Nat := 60450365851689497741921

theorem tailTrace_264885 : CollatzResearch.WordTrace tailWord_264885 prefixEnd_264885 60450365851689497741921 := by
  unfold tailWord_264885
  simp only [CollatzResearch.WordTrace]
  refine ⟨9661149645374358601468109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6440766430249572400978739 9661149645374358601468109)
  ·
    refine ⟨3622931117015384475550541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9661149645374358601468109 3622931117015384475550541)
    ·
      refine ⟨1358599168880769178331453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3622931117015384475550541 1358599168880769178331453)
      ·
        refine ⟨509474688330288441874295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1358599168880769178331453 509474688330288441874295)
        ·
          refine ⟨764212032495432662811443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 509474688330288441874295 764212032495432662811443)
          ·
            refine ⟨1146318048743148994217165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 764212032495432662811443 1146318048743148994217165)
            ·
              refine ⟨429869268278680872831437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1146318048743148994217165 429869268278680872831437)
              ·
                refine ⟨161200975604505327311789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 429869268278680872831437 161200975604505327311789)
                ·
                  refine ⟨60450365851689497741921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 161200975604505327311789 60450365851689497741921)
                  ·
                    rfl

theorem cell21_264885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 3, 3, 3].length) (baseStart_264885 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_264885 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_264885 prefixEnd_264885 := by exact prefixLift 264885
  have htrace : WordTrace (prefixWord ++ tailWord_264885) baseStart_264885 baseEnd_264885 := by
    simpa [prefixWord, tailWord_264885, baseEnd_264885] using wordTrace_append hprefix tailTrace_264885
  have hstable : (prefixWord ++ tailWord_264885).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_264885).length < 2 ^ (prefixWord ++ tailWord_264885).sum := by decide
  have hdescent : baseEnd_264885 < baseStart_264885 := by decide
  rcases family_descends (prefixWord ++ tailWord_264885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_264896 : List Nat := [2, 1, 1, 2, 4, 4, 7]
def baseStart_264896 : Nat := 118140960795 + 264896 * 2 ^ 59
def prefixEnd_264896 : Nat := 4983230072969 + 3 ^ 40 * 264896 * 2
def baseEnd_264896 : Nat := 6716986244617324784285

theorem tailTrace_264896 : CollatzResearch.WordTrace tailWord_264896 prefixEnd_264896 6716986244617324784285 := by
  unfold tailWord_264896
  simp only [CollatzResearch.WordTrace]
  refine ⟨4830775424167253740059271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6441033898889671653412361 4830775424167253740059271)
  ·
    refine ⟨7246163136250880610088907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4830775424167253740059271 7246163136250880610088907)
    ·
      refine ⟨10869244704376320915133361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7246163136250880610088907 10869244704376320915133361)
      ·
        refine ⟨8151933528282240686350021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10869244704376320915133361 8151933528282240686350021)
        ·
          refine ⟨1528487536552920128690629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8151933528282240686350021 1528487536552920128690629)
          ·
            refine ⟨286591413103672524129493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1528487536552920128690629 286591413103672524129493)
            ·
              refine ⟨6716986244617324784285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 286591413103672524129493 6716986244617324784285)
              ·
                rfl

theorem cell21_264896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 4, 7].length) (baseStart_264896 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_264896 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_264896 prefixEnd_264896 := by exact prefixLift 264896
  have htrace : WordTrace (prefixWord ++ tailWord_264896) baseStart_264896 baseEnd_264896 := by
    simpa [prefixWord, tailWord_264896, baseEnd_264896] using wordTrace_append hprefix tailTrace_264896
  have hstable : (prefixWord ++ tailWord_264896).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_264896).length < 2 ^ (prefixWord ++ tailWord_264896).sum := by decide
  have hdescent : baseEnd_264896 < baseStart_264896 := by decide
  rcases family_descends (prefixWord ++ tailWord_264896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_265003 : List Nat := [1, 1, 1, 1, 2, 1, 2, 9, 3]
def baseStart_265003 : Nat := 118140960795 + 265003 * 2 ^ 59
def prefixEnd_265003 : Nat := 4983230072969 + 3 ^ 40 * 265003 * 2
def baseEnd_265003 : Nat := 60477295059347514775013

theorem tailTrace_265003 : CollatzResearch.WordTrace tailWord_265003 prefixEnd_265003 60477295059347514775013 := by
  unfold tailWord_265003
  simp only [CollatzResearch.WordTrace]
  refine ⟨9665453458946864754263663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6443635639297909836175775 9665453458946864754263663)
  ·
    refine ⟨14498180188420297131395495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9665453458946864754263663 14498180188420297131395495)
    ·
      refine ⟨21747270282630445697093243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14498180188420297131395495 21747270282630445697093243)
      ·
        refine ⟨32620905423945668545639865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21747270282630445697093243 32620905423945668545639865)
        ·
          refine ⟨24465679067959251409229899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32620905423945668545639865 24465679067959251409229899)
          ·
            refine ⟨36698518601938877113844849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24465679067959251409229899 36698518601938877113844849)
            ·
              refine ⟨27523888951454157835383637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36698518601938877113844849 27523888951454157835383637)
              ·
                refine ⟨161272786824926706066701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 27523888951454157835383637 161272786824926706066701)
                ·
                  refine ⟨60477295059347514775013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 161272786824926706066701 60477295059347514775013)
                  ·
                    rfl

theorem cell21_265003_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 9, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 9, 3].length) (baseStart_265003 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_265003 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_265003 prefixEnd_265003 := by exact prefixLift 265003
  have htrace : WordTrace (prefixWord ++ tailWord_265003) baseStart_265003 baseEnd_265003 := by
    simpa [prefixWord, tailWord_265003, baseEnd_265003] using wordTrace_append hprefix tailTrace_265003
  have hstable : (prefixWord ++ tailWord_265003).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_265003).length < 2 ^ (prefixWord ++ tailWord_265003).sum := by decide
  have hdescent : baseEnd_265003 < baseStart_265003 := by decide
  rcases family_descends (prefixWord ++ tailWord_265003) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_265031 : List Nat := [1, 1, 4, 1, 2, 1, 1, 10]
def baseStart_265031 : Nat := 118140960795 + 265031 * 2 ^ 59
def prefixEnd_265031 : Nat := 4983230072969 + 3 ^ 40 * 265031 * 2
def baseEnd_265031 : Nat := 20161228346941896102763

theorem tailTrace_265031 : CollatzResearch.WordTrace tailWord_265031 prefixEnd_265031 20161228346941896102763 := by
  unfold tailWord_265031
  simp only [CollatzResearch.WordTrace]
  refine ⟨9666474702845425536282947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6444316468563617024188631 9666474702845425536282947)
  ·
    refine ⟨14499712054268138304424421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9666474702845425536282947 14499712054268138304424421)
    ·
      refine ⟨2718696010175275932079579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 14499712054268138304424421 2718696010175275932079579)
      ·
        refine ⟨4078044015262913898119369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2718696010175275932079579 4078044015262913898119369)
        ·
          refine ⟨3058533011447185423589527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4078044015262913898119369 3058533011447185423589527)
          ·
            refine ⟨4587799517170778135384291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3058533011447185423589527 4587799517170778135384291)
            ·
              refine ⟨6881699275756167203076437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4587799517170778135384291 6881699275756167203076437)
              ·
                refine ⟨20161228346941896102763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 6881699275756167203076437 20161228346941896102763)
                ·
                  rfl

theorem cell21_265031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 1, 10].length) (baseStart_265031 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_265031 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_265031 prefixEnd_265031 := by exact prefixLift 265031
  have htrace : WordTrace (prefixWord ++ tailWord_265031) baseStart_265031 baseEnd_265031 := by
    simpa [prefixWord, tailWord_265031, baseEnd_265031] using wordTrace_append hprefix tailTrace_265031
  have hstable : (prefixWord ++ tailWord_265031).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_265031).length < 2 ^ (prefixWord ++ tailWord_265031).sum := by decide
  have hdescent : baseEnd_265031 < baseStart_265031 := by decide
  rcases family_descends (prefixWord ++ tailWord_265031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_265079 : List Nat := [1, 1, 3, 1, 1, 2, 1, 8, 3]
def baseStart_265079 : Nat := 118140960795 + 265079 * 2 ^ 59
def prefixEnd_265079 : Nat := 4983230072969 + 3 ^ 40 * 265079 * 2
def baseEnd_265079 : Nat := 60494639294788271508191

theorem tailTrace_265079 : CollatzResearch.WordTrace tailWord_265079 prefixEnd_265079 60494639294788271508191 := by
  unfold tailWord_265079
  simp only [CollatzResearch.WordTrace]
  refine ⟨9668225406671529734030291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6445483604447686489353527 9668225406671529734030291)
  ·
    refine ⟨14502338110007294601045437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9668225406671529734030291 14502338110007294601045437)
    ·
      refine ⟨5438376791252735475392039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14502338110007294601045437 5438376791252735475392039)
      ·
        refine ⟨8157565186879103213088059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5438376791252735475392039 8157565186879103213088059)
        ·
          refine ⟨12236347780318654819632089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8157565186879103213088059 12236347780318654819632089)
          ·
            refine ⟨9177260835238991114724067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12236347780318654819632089 9177260835238991114724067)
            ·
              refine ⟨13765891252858486672086101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9177260835238991114724067 13765891252858486672086101)
              ·
                refine ⟨161319038119435390688509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 13765891252858486672086101 161319038119435390688509)
                ·
                  refine ⟨60494639294788271508191, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 161319038119435390688509 60494639294788271508191)
                  ·
                    rfl

theorem cell21_265079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 8, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 8, 3].length) (baseStart_265079 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_265079 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_265079 prefixEnd_265079 := by exact prefixLift 265079
  have htrace : WordTrace (prefixWord ++ tailWord_265079) baseStart_265079 baseEnd_265079 := by
    simpa [prefixWord, tailWord_265079, baseEnd_265079] using wordTrace_append hprefix tailTrace_265079
  have hstable : (prefixWord ++ tailWord_265079).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_265079).length < 2 ^ (prefixWord ++ tailWord_265079).sum := by decide
  have hdescent : baseEnd_265079 < baseStart_265079 := by decide
  rcases family_descends (prefixWord ++ tailWord_265079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_265127 : List Nat := [1, 1, 6, 1, 3, 1, 2, 2, 4]
def baseStart_265127 : Nat := 118140960795 + 265127 * 2 ^ 59
def prefixEnd_265127 : Nat := 4983230072969 + 3 ^ 40 * 265127 * 2
def baseEnd_265127 : Nat := 60505593548750854708093

theorem tailTrace_265127 : CollatzResearch.WordTrace tailWord_265127 prefixEnd_265127 60505593548750854708093 := by
  unfold tailWord_265127
  simp only [CollatzResearch.WordTrace]
  refine ⟨9669976110497633931777635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6446650740331755954518423 9669976110497633931777635)
  ·
    refine ⟨14504964165746450897666453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9669976110497633931777635 14504964165746450897666453)
    ·
      refine ⟨679920195269364885828115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 14504964165746450897666453 679920195269364885828115)
      ·
        refine ⟨1019880292904047328742173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 679920195269364885828115 1019880292904047328742173)
        ·
          refine ⟨382455109839017748278315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1019880292904047328742173 382455109839017748278315)
          ·
            refine ⟨573682664758526622417473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 382455109839017748278315 573682664758526622417473)
            ·
              refine ⟨430261998568894966813105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 573682664758526622417473 430261998568894966813105)
              ·
                refine ⟨322696498926671225109829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 430261998568894966813105 322696498926671225109829)
                ·
                  refine ⟨60505593548750854708093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 322696498926671225109829 60505593548750854708093)
                  ·
                    rfl

theorem cell21_265127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 3, 1, 2, 2, 4].length) (baseStart_265127 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_265127 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_265127 prefixEnd_265127 := by exact prefixLift 265127
  have htrace : WordTrace (prefixWord ++ tailWord_265127) baseStart_265127 baseEnd_265127 := by
    simpa [prefixWord, tailWord_265127, baseEnd_265127] using wordTrace_append hprefix tailTrace_265127
  have hstable : (prefixWord ++ tailWord_265127).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_265127).length < 2 ^ (prefixWord ++ tailWord_265127).sum := by decide
  have hdescent : baseEnd_265127 < baseStart_265127 := by decide
  rcases family_descends (prefixWord ++ tailWord_265127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_265172 : List Nat := [2, 4, 1, 2, 1, 2, 1, 5, 3]
def baseStart_265172 : Nat := 118140960795 + 265172 * 2 ^ 59
def prefixEnd_265172 : Nat := 4983230072969 + 3 ^ 40 * 265172 * 2
def baseEnd_265172 : Nat := 60515863161840776458001

theorem tailTrace_265172 : CollatzResearch.WordTrace tailWord_265172 prefixEnd_265172 60515863161840776458001 := by
  unfold tailWord_265172
  simp only [CollatzResearch.WordTrace]
  refine ⟨4835808697667303308582885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6447744930223071078110513 4835808697667303308582885)
  ·
    refine ⟨906714130812619370359291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4835808697667303308582885 906714130812619370359291)
    ·
      refine ⟨1360071196218929055538937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 906714130812619370359291 1360071196218929055538937)
      ·
        refine ⟨1020053397164196791654203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1360071196218929055538937 1020053397164196791654203)
        ·
          refine ⟨1530080095746295187481305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1020053397164196791654203 1530080095746295187481305)
          ·
            refine ⟨1147560071809721390610979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1530080095746295187481305 1147560071809721390610979)
            ·
              refine ⟨1721340107714582085916469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1147560071809721390610979 1721340107714582085916469)
              ·
                refine ⟨161375635098242070554669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1721340107714582085916469 161375635098242070554669)
                ·
                  refine ⟨60515863161840776458001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 161375635098242070554669 60515863161840776458001)
                  ·
                    rfl

theorem cell21_265172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 1, 5, 3].length) (baseStart_265172 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_265172 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_265172 prefixEnd_265172 := by exact prefixLift 265172
  have htrace : WordTrace (prefixWord ++ tailWord_265172) baseStart_265172 baseEnd_265172 := by
    simpa [prefixWord, tailWord_265172, baseEnd_265172] using wordTrace_append hprefix tailTrace_265172
  have hstable : (prefixWord ++ tailWord_265172).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_265172).length < 2 ^ (prefixWord ++ tailWord_265172).sum := by decide
  have hdescent : baseEnd_265172 < baseStart_265172 := by decide
  rcases family_descends (prefixWord ++ tailWord_265172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_265217 : List Nat := [1, 2, 4, 1, 2, 4, 2, 5]
def baseStart_265217 : Nat := 118140960795 + 265217 * 2 ^ 59
def prefixEnd_265217 : Nat := 4983230072969 + 3 ^ 40 * 265217 * 2
def baseEnd_265217 : Nat := 20175377591643566069303

theorem tailTrace_265217 : CollatzResearch.WordTrace tailWord_265217 prefixEnd_265217 20175377591643566069303 := by
  unfold tailWord_265217
  simp only [CollatzResearch.WordTrace]
  refine ⟨9673258680171579302553905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6448839120114386201702603 9673258680171579302553905)
  ·
    refine ⟨7254944010128684476915429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9673258680171579302553905 7254944010128684476915429)
    ·
      refine ⟨1360302001899128339421643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7254944010128684476915429 1360302001899128339421643)
      ·
        refine ⟨2040453002848692509132465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1360302001899128339421643 2040453002848692509132465)
        ·
          refine ⟨1530339752136519381849349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2040453002848692509132465 1530339752136519381849349)
          ·
            refine ⟨286938703525597384096753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1530339752136519381849349 286938703525597384096753)
            ·
              refine ⟨215204027644198038072565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 286938703525597384096753 215204027644198038072565)
              ·
                refine ⟨20175377591643566069303, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 215204027644198038072565 20175377591643566069303)
                ·
                  rfl

theorem cell21_265217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 4, 2, 5].length) (baseStart_265217 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_265217 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_265217 prefixEnd_265217 := by exact prefixLift 265217
  have htrace : WordTrace (prefixWord ++ tailWord_265217) baseStart_265217 baseEnd_265217 := by
    simpa [prefixWord, tailWord_265217, baseEnd_265217] using wordTrace_append hprefix tailTrace_265217
  have hstable : (prefixWord ++ tailWord_265217).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_265217).length < 2 ^ (prefixWord ++ tailWord_265217).sum := by decide
  have hdescent : baseEnd_265217 < baseStart_265217 := by decide
  rcases family_descends (prefixWord ++ tailWord_265217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_265259 : List Nat := [1, 1, 1, 1, 2, 1, 8, 6]
def baseStart_265259 : Nat := 118140960795 + 265259 * 2 ^ 59
def prefixEnd_265259 : Nat := 4983230072969 + 3 ^ 40 * 265259 * 2
def baseEnd_265259 : Nat := 20178572582382652835941

theorem tailTrace_265259 : CollatzResearch.WordTrace tailWord_265259 prefixEnd_265259 20178572582382652835941 := by
  unfold tailWord_265259
  simp only [CollatzResearch.WordTrace]
  refine ⟨9674790546019420475582831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6449860364012946983721887 9674790546019420475582831)
  ·
    refine ⟨14512185819029130713374247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9674790546019420475582831 14512185819029130713374247)
    ·
      refine ⟨21768278728543696070061371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14512185819029130713374247 21768278728543696070061371)
      ·
        refine ⟨32652418092815544105092057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21768278728543696070061371 32652418092815544105092057)
        ·
          refine ⟨24489313569611658078819043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32652418092815544105092057 24489313569611658078819043)
          ·
            refine ⟨36733970354417487118228565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24489313569611658078819043 36733970354417487118228565)
            ·
              refine ⟨430476215090829927166741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 36733970354417487118228565 430476215090829927166741)
              ·
                refine ⟨20178572582382652835941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 430476215090829927166741 20178572582382652835941)
                ·
                  rfl

theorem cell21_265259_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 8, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 8, 6].length) (baseStart_265259 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_265259 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_265259 prefixEnd_265259 := by exact prefixLift 265259
  have htrace : WordTrace (prefixWord ++ tailWord_265259) baseStart_265259 baseEnd_265259 := by
    simpa [prefixWord, tailWord_265259, baseEnd_265259] using wordTrace_append hprefix tailTrace_265259
  have hstable : (prefixWord ++ tailWord_265259).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_265259).length < 2 ^ (prefixWord ++ tailWord_265259).sum := by decide
  have hdescent : baseEnd_265259 < baseStart_265259 := by decide
  rcases family_descends (prefixWord ++ tailWord_265259) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_265262 : List Nat := [4, 1, 3, 1, 1, 1, 3, 3, 4]
def baseStart_265262 : Nat := 118140960795 + 265262 * 2 ^ 59
def prefixEnd_265262 : Nat := 4983230072969 + 3 ^ 40 * 265262 * 2
def baseEnd_265262 : Nat := 60536402388020619957817

theorem tailTrace_265262 : CollatzResearch.WordTrace tailWord_265262 prefixEnd_265262 60536402388020619957817 := by
  unfold tailWord_265262
  simp only [CollatzResearch.WordTrace]
  refine ⟨1209362495626068998492755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 6449933310005701325294693 1209362495626068998492755)
  ·
    refine ⟨1814043743439103497739133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1209362495626068998492755 1814043743439103497739133)
    ·
      refine ⟨680266403789663811652175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1814043743439103497739133 680266403789663811652175)
      ·
        refine ⟨1020399605684495717478263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 680266403789663811652175 1020399605684495717478263)
        ·
          refine ⟨1530599408526743576217395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1020399605684495717478263 1530599408526743576217395)
          ·
            refine ⟨2295899112790115364326093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1530599408526743576217395 2295899112790115364326093)
            ·
              refine ⟨860962167296293261622285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2295899112790115364326093 860962167296293261622285)
              ·
                refine ⟨322860812736109973108357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 860962167296293261622285 322860812736109973108357)
                ·
                  refine ⟨60536402388020619957817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 322860812736109973108357 60536402388020619957817)
                  ·
                    rfl

theorem cell21_265262_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 3, 3, 4].length) (baseStart_265262 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_265262 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_265262 prefixEnd_265262 := by exact prefixLift 265262
  have htrace : WordTrace (prefixWord ++ tailWord_265262) baseStart_265262 baseEnd_265262 := by
    simpa [prefixWord, tailWord_265262, baseEnd_265262] using wordTrace_append hprefix tailTrace_265262
  have hstable : (prefixWord ++ tailWord_265262).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_265262).length < 2 ^ (prefixWord ++ tailWord_265262).sum := by decide
  have hdescent : baseEnd_265262 < baseStart_265262 := by decide
  rcases family_descends (prefixWord ++ tailWord_265262) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_265310 : List Nat := [4, 4, 1, 1, 1, 1, 3, 6]
def baseStart_265310 : Nat := 118140960795 + 265310 * 2 ^ 59
def prefixEnd_265310 : Nat := 4983230072969 + 3 ^ 40 * 265310 * 2
def baseEnd_265310 : Nat := 20182452213994401052573

theorem tailTrace_265310 : CollatzResearch.WordTrace tailWord_265310 prefixEnd_265310 20182452213994401052573 := by
  unfold tailWord_265310
  simp only [CollatzResearch.WordTrace]
  refine ⟨1209581333604332023211173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 6451100445889770790459589 1209581333604332023211173)
  ·
    refine ⟨226796500050812254352095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1209581333604332023211173 226796500050812254352095)
    ·
      refine ⟨340194750076218381528143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 226796500050812254352095 340194750076218381528143)
      ·
        refine ⟨510292125114327572292215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 340194750076218381528143 510292125114327572292215)
        ·
          refine ⟨765438187671491358438323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 510292125114327572292215 765438187671491358438323)
          ·
            refine ⟨1148157281507237037657485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 765438187671491358438323 1148157281507237037657485)
            ·
              refine ⟨430558980565213889121557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1148157281507237037657485 430558980565213889121557)
              ·
                refine ⟨20182452213994401052573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 430558980565213889121557 20182452213994401052573)
                ·
                  rfl

theorem cell21_265310_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 3, 6].length) (baseStart_265310 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_265310 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_265310 prefixEnd_265310 := by exact prefixLift 265310
  have htrace : WordTrace (prefixWord ++ tailWord_265310) baseStart_265310 baseEnd_265310 := by
    simpa [prefixWord, tailWord_265310, baseEnd_265310] using wordTrace_append hprefix tailTrace_265310
  have hstable : (prefixWord ++ tailWord_265310).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_265310).length < 2 ^ (prefixWord ++ tailWord_265310).sum := by decide
  have hdescent : baseEnd_265310 < baseStart_265310 := by decide
  rcases family_descends (prefixWord ++ tailWord_265310) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_265321 : List Nat := [1, 2, 1, 1, 1, 6, 2, 3, 4]
def baseStart_265321 : Nat := 118140960795 + 265321 * 2 ^ 59
def prefixEnd_265321 : Nat := 4983230072969 + 3 ^ 40 * 265321 * 2
def baseEnd_265321 : Nat := 60549866991849628474363

theorem tailTrace_265321 : CollatzResearch.WordTrace tailWord_265321 prefixEnd_265321 60549866991849628474363 := by
  unfold tailWord_265321
  simp only [CollatzResearch.WordTrace]
  refine ⟨9677051871794805064339817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6451367914529870042893211 9677051871794805064339817)
  ·
    refine ⟨7257788903846103798254863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9677051871794805064339817 7257788903846103798254863)
    ·
      refine ⟨10886683355769155697382295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7257788903846103798254863 10886683355769155697382295)
      ·
        refine ⟨16330025033653733546073443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10886683355769155697382295 16330025033653733546073443)
        ·
          refine ⟨24495037550480600319110165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16330025033653733546073443 24495037550480600319110165)
          ·
            refine ⟨1148204885178778139958289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 24495037550480600319110165 1148204885178778139958289)
            ·
              refine ⟨861153663884083604968717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1148204885178778139958289 861153663884083604968717)
              ·
                refine ⟨322932623956531351863269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 861153663884083604968717 322932623956531351863269)
                ·
                  refine ⟨60549866991849628474363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 322932623956531351863269 60549866991849628474363)
                  ·
                    rfl

theorem cell21_265321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 2, 3, 4].length) (baseStart_265321 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_265321 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_265321 prefixEnd_265321 := by exact prefixLift 265321
  have htrace : WordTrace (prefixWord ++ tailWord_265321) baseStart_265321 baseEnd_265321 := by
    simpa [prefixWord, tailWord_265321, baseEnd_265321] using wordTrace_append hprefix tailTrace_265321
  have hstable : (prefixWord ++ tailWord_265321).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_265321).length < 2 ^ (prefixWord ++ tailWord_265321).sum := by decide
  have hdescent : baseEnd_265321 < baseStart_265321 := by decide
  rcases family_descends (prefixWord ++ tailWord_265321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_265352 : List Nat := [2, 1, 3, 4, 2, 1, 8]
def baseStart_265352 : Nat := 118140960795 + 265352 * 2 ^ 59
def prefixEnd_265352 : Nat := 4983230072969 + 3 ^ 40 * 265352 * 2
def baseEnd_265352 : Nat := 6728549068244495939737

theorem tailTrace_265352 : CollatzResearch.WordTrace tailWord_265352 prefixEnd_265352 6728549068244495939737 := by
  unfold tailWord_265352
  simp only [CollatzResearch.WordTrace]
  refine ⟨4839091267341248679359155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6452121689788331572478873 4839091267341248679359155)
  ·
    refine ⟨7258636901011873019038733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4839091267341248679359155 7258636901011873019038733)
    ·
      refine ⟨2721988837879452382139525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7258636901011873019038733 2721988837879452382139525)
      ·
        refine ⟨510372907102397321651161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2721988837879452382139525 510372907102397321651161)
        ·
          refine ⟨382779680326797991238371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 510372907102397321651161 382779680326797991238371)
          ·
            refine ⟨574169520490196986857557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 382779680326797991238371 574169520490196986857557)
            ·
              refine ⟨6728549068244495939737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 574169520490196986857557 6728549068244495939737)
              ·
                rfl

theorem cell21_265352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 2, 1, 8].length) (baseStart_265352 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_265352 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_265352 prefixEnd_265352 := by exact prefixLift 265352
  have htrace : WordTrace (prefixWord ++ tailWord_265352) baseStart_265352 baseEnd_265352 := by
    simpa [prefixWord, tailWord_265352, baseEnd_265352] using wordTrace_append hprefix tailTrace_265352
  have hstable : (prefixWord ++ tailWord_265352).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_265352).length < 2 ^ (prefixWord ++ tailWord_265352).sum := by decide
  have hdescent : baseEnd_265352 < baseStart_265352 := by decide
  rcases family_descends (prefixWord ++ tailWord_265352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_265383 : List Nat := [1, 1, 6, 2, 1, 1, 2, 2, 5]
def baseStart_265383 : Nat := 118140960795 + 265383 * 2 ^ 59
def prefixEnd_265383 : Nat := 4983230072969 + 3 ^ 40 * 265383 * 2
def baseEnd_265383 : Nat := 60564016236551298440903

theorem tailTrace_265383 : CollatzResearch.WordTrace tailWord_265383 prefixEnd_265383 60564016236551298440903 := by
  unfold tailWord_265383
  simp only [CollatzResearch.WordTrace]
  refine ⟨9679313197570189653096803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6452875465046793102064535 9679313197570189653096803)
  ·
    refine ⟨14518969796355284479645205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9679313197570189653096803 14518969796355284479645205)
    ·
      refine ⟨680576709204153959983369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 14518969796355284479645205 680576709204153959983369)
      ·
        refine ⟨510432531903115469987527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 680576709204153959983369 510432531903115469987527)
        ·
          refine ⟨765648797854673204981291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 510432531903115469987527 765648797854673204981291)
          ·
            refine ⟨1148473196782009807471937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 765648797854673204981291 1148473196782009807471937)
            ·
              refine ⟨861354897586507355603953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1148473196782009807471937 861354897586507355603953)
              ·
                refine ⟨646016173189880516702965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 861354897586507355603953 646016173189880516702965)
                ·
                  refine ⟨60564016236551298440903, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 646016173189880516702965 60564016236551298440903)
                  ·
                    rfl

theorem cell21_265383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 2, 2, 5].length) (baseStart_265383 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_265383 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_265383 prefixEnd_265383 := by exact prefixLift 265383
  have htrace : WordTrace (prefixWord ++ tailWord_265383) baseStart_265383 baseEnd_265383 := by
    simpa [prefixWord, tailWord_265383, baseEnd_265383] using wordTrace_append hprefix tailTrace_265383
  have hstable : (prefixWord ++ tailWord_265383).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_265383).length < 2 ^ (prefixWord ++ tailWord_265383).sum := by decide
  have hdescent : baseEnd_265383 < baseStart_265383 := by decide
  rcases family_descends (prefixWord ++ tailWord_265383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_265386 : List Nat := [3, 1, 5, 1, 1, 3, 2, 5]
def baseStart_265386 : Nat := 118140960795 + 265386 * 2 ^ 59
def prefixEnd_265386 : Nat := 4983230072969 + 3 ^ 40 * 265386 * 2
def baseEnd_265386 : Nat := 20188233625807986630299

theorem tailTrace_265386 : CollatzResearch.WordTrace tailWord_265386 prefixEnd_265386 20188233625807986630299 := by
  unfold tailWord_265386
  simp only [CollatzResearch.WordTrace]
  refine ⟨2419855654139830291364003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6452948411039547443637341 2419855654139830291364003)
  ·
    refine ⟨3629783481209745437046005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2419855654139830291364003 3629783481209745437046005)
    ·
      refine ⟨340292201363413634723063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 3629783481209745437046005 340292201363413634723063)
      ·
        refine ⟨510438302045120452084595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 340292201363413634723063 510438302045120452084595)
        ·
          refine ⟨765657453067680678126893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 510438302045120452084595 765657453067680678126893)
          ·
            refine ⟨287121544900380254297585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 765657453067680678126893 287121544900380254297585)
            ·
              refine ⟨215341158675285190723189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 287121544900380254297585 215341158675285190723189)
              ·
                refine ⟨20188233625807986630299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 215341158675285190723189 20188233625807986630299)
                ·
                  rfl

theorem cell21_265386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 3, 2, 5].length) (baseStart_265386 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_265386 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_265386 prefixEnd_265386 := by exact prefixLift 265386
  have htrace : WordTrace (prefixWord ++ tailWord_265386) baseStart_265386 baseEnd_265386 := by
    simpa [prefixWord, tailWord_265386, baseEnd_265386] using wordTrace_append hprefix tailTrace_265386
  have hstable : (prefixWord ++ tailWord_265386).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_265386).length < 2 ^ (prefixWord ++ tailWord_265386).sum := by decide
  have hdescent : baseEnd_265386 < baseStart_265386 := by decide
  rcases family_descends (prefixWord ++ tailWord_265386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_265473 : List Nat := [1, 2, 4, 1, 1, 3, 1, 4, 4]
def baseStart_265473 : Nat := 118140960795 + 265473 * 2 ^ 59
def prefixEnd_265473 : Nat := 4983230072969 + 3 ^ 40 * 265473 * 2
def baseEnd_265473 : Nat := 60584555462731141940719

theorem tailTrace_265473 : CollatzResearch.WordTrace tailWord_265473 prefixEnd_265473 60584555462731141940719 := by
  unfold tailWord_265473
  simp only [CollatzResearch.WordTrace]
  refine ⟨9682595767244135023873073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6455063844829423349248715 9682595767244135023873073)
  ·
    refine ⟨7261946825433101267904805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9682595767244135023873073 7261946825433101267904805)
    ·
      refine ⟨1361615029768706487732151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7261946825433101267904805 1361615029768706487732151)
      ·
        refine ⟨2042422544653059731598227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1361615029768706487732151 2042422544653059731598227)
        ·
          refine ⟨3063633816979589597397341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2042422544653059731598227 3063633816979589597397341)
          ·
            refine ⟨1148862681367346099024003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3063633816979589597397341 1148862681367346099024003)
            ·
              refine ⟨1723294022051019148536005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1148862681367346099024003 1723294022051019148536005)
              ·
                refine ⟨323117629134566090350501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1723294022051019148536005 323117629134566090350501)
                ·
                  refine ⟨60584555462731141940719, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 323117629134566090350501 60584555462731141940719)
                  ·
                    rfl

theorem cell21_265473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 1, 4, 4].length) (baseStart_265473 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_265473 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_265473 prefixEnd_265473 := by exact prefixLift 265473
  have htrace : WordTrace (prefixWord ++ tailWord_265473) baseStart_265473 baseEnd_265473 := by
    simpa [prefixWord, tailWord_265473, baseEnd_265473] using wordTrace_append hprefix tailTrace_265473
  have hstable : (prefixWord ++ tailWord_265473).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_265473).length < 2 ^ (prefixWord ++ tailWord_265473).sum := by decide
  have hdescent : baseEnd_265473 < baseStart_265473 := by decide
  rcases family_descends (prefixWord ++ tailWord_265473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_265476 : List Nat := [2, 3, 2, 2, 2, 2, 1, 4, 3]
def baseStart_265476 : Nat := 118140960795 + 265476 * 2 ^ 59
def prefixEnd_265476 : Nat := 4983230072969 + 3 ^ 40 * 265476 * 2
def baseEnd_265476 : Nat := 60585240103603803390713

theorem tailTrace_265476 : CollatzResearch.WordTrace tailWord_265476 prefixEnd_265476 60585240103603803390713 := by
  unfold tailWord_265476
  simp only [CollatzResearch.WordTrace]
  refine ⟨4841352593116633268116141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6455136790822177690821521 4841352593116633268116141)
  ·
    refine ⟨1815507222418737475543553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4841352593116633268116141 1815507222418737475543553)
    ·
      refine ⟨1361630416814053106657665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1815507222418737475543553 1361630416814053106657665)
      ·
        refine ⟨1021222812610539829993249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1361630416814053106657665 1021222812610539829993249)
        ·
          refine ⟨765917109457904872494937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1021222812610539829993249 765917109457904872494937)
          ·
            refine ⟨574437832093428654371203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 765917109457904872494937 574437832093428654371203)
            ·
              refine ⟨861656748140142981556805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 574437832093428654371203 861656748140142981556805)
              ·
                refine ⟨161560640276276809041901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 861656748140142981556805 161560640276276809041901)
                ·
                  refine ⟨60585240103603803390713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 161560640276276809041901 60585240103603803390713)
                  ·
                    rfl

theorem cell21_265476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 2, 1, 4, 3].length) (baseStart_265476 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_265476 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_265476 prefixEnd_265476 := by exact prefixLift 265476
  have htrace : WordTrace (prefixWord ++ tailWord_265476) baseStart_265476 baseEnd_265476 := by
    simpa [prefixWord, tailWord_265476, baseEnd_265476] using wordTrace_append hprefix tailTrace_265476
  have hstable : (prefixWord ++ tailWord_265476).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_265476).length < 2 ^ (prefixWord ++ tailWord_265476).sum := by decide
  have hdescent : baseEnd_265476 < baseStart_265476 := by decide
  rcases family_descends (prefixWord ++ tailWord_265476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_265535 : List Nat := [1, 1, 2, 2, 4, 2, 2, 4, 3]
def baseStart_265535 : Nat := 118140960795 + 265535 * 2 ^ 59
def prefixEnd_265535 : Nat := 4983230072969 + 3 ^ 40 * 265535 * 2
def baseEnd_265535 : Nat := 60598704707432811907259

theorem tailTrace_265535 : CollatzResearch.WordTrace tailWord_265535 prefixEnd_265535 60598704707432811907259 := by
  unfold tailWord_265535
  simp only [CollatzResearch.WordTrace]
  refine ⟨9684857093019519612630059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6456571395346346408420039 9684857093019519612630059)
  ·
    refine ⟨14527285639529279418945089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9684857093019519612630059 14527285639529279418945089)
    ·
      refine ⟨10895464229646959564208817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14527285639529279418945089 10895464229646959564208817)
      ·
        refine ⟨8171598172235219673156613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10895464229646959564208817 8171598172235219673156613)
        ·
          refine ⟨1532174657294103688716865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8171598172235219673156613 1532174657294103688716865)
          ·
            refine ⟨1149130992970577766537649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1532174657294103688716865 1149130992970577766537649)
            ·
              refine ⟨861848244727933324903237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1149130992970577766537649 861848244727933324903237)
              ·
                refine ⟨161596545886487498419357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 861848244727933324903237 161596545886487498419357)
                ·
                  refine ⟨60598704707432811907259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 161596545886487498419357 60598704707432811907259)
                  ·
                    rfl

theorem cell21_265535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 2, 4, 3].length) (baseStart_265535 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_265535 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_265535 prefixEnd_265535 := by exact prefixLift 265535
  have htrace : WordTrace (prefixWord ++ tailWord_265535) baseStart_265535 baseEnd_265535 := by
    simpa [prefixWord, tailWord_265535, baseEnd_265535] using wordTrace_append hprefix tailTrace_265535
  have hstable : (prefixWord ++ tailWord_265535).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_265535).length < 2 ^ (prefixWord ++ tailWord_265535).sum := by decide
  have hdescent : baseEnd_265535 < baseStart_265535 := by decide
  rcases family_descends (prefixWord ++ tailWord_265535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_265645 : List Nat := [1, 5, 2, 2, 1, 1, 4, 2, 3]
def baseStart_265645 : Nat := 118140960795 + 265645 * 2 ^ 59
def prefixEnd_265645 : Nat := 4983230072969 + 3 ^ 40 * 265645 * 2
def baseEnd_265645 : Nat := 60623808206097065073701

theorem tailTrace_265645 : CollatzResearch.WordTrace tailWord_265645 prefixEnd_265645 60623808206097065073701 := by
  unfold tailWord_265645
  simp only [CollatzResearch.WordTrace]
  refine ⟨9688869122621008399134389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6459246081747338932756259 9688869122621008399134389)
  ·
    refine ⟨908331480245719537418849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 9688869122621008399134389 908331480245719537418849)
    ·
      refine ⟨681248610184289653064137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 908331480245719537418849 681248610184289653064137)
      ·
        refine ⟨510936457638217239798103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 681248610184289653064137 510936457638217239798103)
        ·
          refine ⟨766404686457325859697155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 510936457638217239798103 766404686457325859697155)
          ·
            refine ⟨1149607029685988789545733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 766404686457325859697155 1149607029685988789545733)
            ·
              refine ⟨215551318066122898039825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1149607029685988789545733 215551318066122898039825)
              ·
                refine ⟨161663488549592173529869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 215551318066122898039825 161663488549592173529869)
                ·
                  refine ⟨60623808206097065073701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 161663488549592173529869 60623808206097065073701)
                  ·
                    rfl

theorem cell21_265645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 4, 2, 3].length) (baseStart_265645 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_265645 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_265645 prefixEnd_265645 := by exact prefixLift 265645
  have htrace : WordTrace (prefixWord ++ tailWord_265645) baseStart_265645 baseEnd_265645 := by
    simpa [prefixWord, tailWord_265645, baseEnd_265645] using wordTrace_append hprefix tailTrace_265645
  have hstable : (prefixWord ++ tailWord_265645).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_265645).length < 2 ^ (prefixWord ++ tailWord_265645).sum := by decide
  have hdescent : baseEnd_265645 < baseStart_265645 := by decide
  rcases family_descends (prefixWord ++ tailWord_265645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_265701 : List Nat := [1, 3, 1, 5, 1, 2, 1, 1, 6]
def baseStart_265701 : Nat := 118140960795 + 265701 * 2 ^ 59
def prefixEnd_265701 : Nat := 4983230072969 + 3 ^ 40 * 265701 * 2
def baseEnd_265701 : Nat := 60636588169053412140253

theorem tailTrace_265701 : CollatzResearch.WordTrace tailWord_265701 prefixEnd_265701 60636588169053412140253 := by
  unfold tailWord_265701
  simp only [CollatzResearch.WordTrace]
  refine ⟨9690911610418129963172957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6460607740278753308781971 9690911610418129963172957)
  ·
    refine ⟨3634091853906798736189859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9690911610418129963172957 3634091853906798736189859)
    ·
      refine ⟨5451137780860198104284789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3634091853906798736189859 5451137780860198104284789)
      ·
        refine ⟨511044166955643572276699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 5451137780860198104284789 511044166955643572276699)
        ·
          refine ⟨766566250433465358415049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 511044166955643572276699 766566250433465358415049)
          ·
            refine ⟨574924687825099018811287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 766566250433465358415049 574924687825099018811287)
            ·
              refine ⟨862387031737648528216931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 574924687825099018811287 862387031737648528216931)
              ·
                refine ⟨1293580547606472792325397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 862387031737648528216931 1293580547606472792325397)
                ·
                  refine ⟨60636588169053412140253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1293580547606472792325397 60636588169053412140253)
                  ·
                    rfl

theorem cell21_265701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 2, 1, 1, 6].length) (baseStart_265701 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_265701 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_265701 prefixEnd_265701 := by exact prefixLift 265701
  have htrace : WordTrace (prefixWord ++ tailWord_265701) baseStart_265701 baseEnd_265701 := by
    simpa [prefixWord, tailWord_265701, baseEnd_265701] using wordTrace_append hprefix tailTrace_265701
  have hstable : (prefixWord ++ tailWord_265701).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_265701).length < 2 ^ (prefixWord ++ tailWord_265701).sum := by decide
  have hdescent : baseEnd_265701 < baseStart_265701 := by decide
  rcases family_descends (prefixWord ++ tailWord_265701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_265732 : List Nat := [2, 3, 2, 3, 2, 1, 1, 7]
def baseStart_265732 : Nat := 118140960795 + 265732 * 2 ^ 59
def prefixEnd_265732 : Nat := 4983230072969 + 3 ^ 40 * 265732 * 2
def baseEnd_265732 : Nat := 20214554263801415707841

theorem tailTrace_265732 : CollatzResearch.WordTrace tailWord_265732 prefixEnd_265732 20214554263801415707841 := by
  unfold tailWord_265732
  simp only [CollatzResearch.WordTrace]
  refine ⟨4846021136652911128775725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6461361515537214838367633 4846021136652911128775725)
  ·
    refine ⟨1817257926244841673290897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4846021136652911128775725 1817257926244841673290897)
    ·
      refine ⟨1362943444683631254968173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1817257926244841673290897 1362943444683631254968173)
      ·
        refine ⟨511103791756361720613065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1362943444683631254968173 511103791756361720613065)
        ·
          refine ⟨383327843817271290459799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 511103791756361720613065 383327843817271290459799)
          ·
            refine ⟨574991765725906935689699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 383327843817271290459799 574991765725906935689699)
            ·
              refine ⟨862487648588860403534549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 574991765725906935689699 862487648588860403534549)
              ·
                refine ⟨20214554263801415707841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 862487648588860403534549 20214554263801415707841)
                ·
                  rfl

theorem cell21_265732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 2, 1, 1, 7].length) (baseStart_265732 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_265732 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_265732 prefixEnd_265732 := by exact prefixLift 265732
  have htrace : WordTrace (prefixWord ++ tailWord_265732) baseStart_265732 baseEnd_265732 := by
    simpa [prefixWord, tailWord_265732, baseEnd_265732] using wordTrace_append hprefix tailTrace_265732
  have hstable : (prefixWord ++ tailWord_265732).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_265732).length < 2 ^ (prefixWord ++ tailWord_265732).sum := by decide
  have hdescent : baseEnd_265732 < baseStart_265732 := by decide
  rcases family_descends (prefixWord ++ tailWord_265732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_265763 : List Nat := [1, 1, 1, 4, 5, 2, 1, 1, 5]
def baseStart_265763 : Nat := 118140960795 + 265763 * 2 ^ 59
def prefixEnd_265763 : Nat := 4983230072969 + 3 ^ 40 * 265763 * 2
def baseEnd_265763 : Nat := 60650737413755082106793

theorem tailTrace_265763 : CollatzResearch.WordTrace tailWord_265763 prefixEnd_265763 60650737413755082106793 := by
  unfold tailWord_265763
  simp only [CollatzResearch.WordTrace]
  refine ⟨9693172936193514551929943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6462115290795676367953295 9693172936193514551929943)
  ·
    refine ⟨14539759404290271827894915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9693172936193514551929943 14539759404290271827894915)
    ·
      refine ⟨21809639106435407741842373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14539759404290271827894915 21809639106435407741842373)
      ·
        refine ⟨4089307332456638951595445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 21809639106435407741842373 4089307332456638951595445)
        ·
          refine ⟨383372562417809901712073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 4089307332456638951595445 383372562417809901712073)
          ·
            refine ⟨287529421813357426284055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 383372562417809901712073 287529421813357426284055)
            ·
              refine ⟨431294132720036139426083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 287529421813357426284055 431294132720036139426083)
              ·
                refine ⟨646941199080054209139125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 431294132720036139426083 646941199080054209139125)
                ·
                  refine ⟨60650737413755082106793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 646941199080054209139125 60650737413755082106793)
                  ·
                    rfl

theorem cell21_265763_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 5, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 5, 2, 1, 1, 5].length) (baseStart_265763 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_265763 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_265763 prefixEnd_265763 := by exact prefixLift 265763
  have htrace : WordTrace (prefixWord ++ tailWord_265763) baseStart_265763 baseEnd_265763 := by
    simpa [prefixWord, tailWord_265763, baseEnd_265763] using wordTrace_append hprefix tailTrace_265763
  have hstable : (prefixWord ++ tailWord_265763).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_265763).length < 2 ^ (prefixWord ++ tailWord_265763).sum := by decide
  have hdescent : baseEnd_265763 < baseStart_265763 := by decide
  rcases family_descends (prefixWord ++ tailWord_265763) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_265814 : List Nat := [5, 2, 2, 2, 1, 1, 1, 4, 3]
def baseStart_265814 : Nat := 118140960795 + 265814 * 2 ^ 59
def prefixEnd_265814 : Nat := 4983230072969 + 3 ^ 40 * 265814 * 2
def baseEnd_265814 : Nat := 60662376308590326756689

theorem tailTrace_265814 : CollatzResearch.WordTrace tailWord_265814 prefixEnd_265814 60662376308590326756689 := by
  unfold tailWord_265814
  simp only [CollatzResearch.WordTrace]
  refine ⟨605939566188046891377281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 6463355372672500174690997 605939566188046891377281)
  ·
    refine ⟨454454674641035168532961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 605939566188046891377281 454454674641035168532961)
    ·
      refine ⟨340841005980776376399721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 454454674641035168532961 340841005980776376399721)
      ·
        refine ⟨255630754485582282299791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 340841005980776376399721 255630754485582282299791)
        ·
          refine ⟨383446131728373423449687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 255630754485582282299791 383446131728373423449687)
          ·
            refine ⟨575169197592560135174531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 383446131728373423449687 575169197592560135174531)
            ·
              refine ⟨862753796388840202761797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 575169197592560135174531 862753796388840202761797)
              ·
                refine ⟨161766336822907538017837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 862753796388840202761797 161766336822907538017837)
                ·
                  refine ⟨60662376308590326756689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 161766336822907538017837 60662376308590326756689)
                  ·
                    rfl

theorem cell21_265814_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 1, 1, 1, 4, 3].length) (baseStart_265814 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_265814 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_265814 prefixEnd_265814 := by exact prefixLift 265814
  have htrace : WordTrace (prefixWord ++ tailWord_265814) baseStart_265814 baseEnd_265814 := by
    simpa [prefixWord, tailWord_265814, baseEnd_265814] using wordTrace_append hprefix tailTrace_265814
  have hstable : (prefixWord ++ tailWord_265814).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_265814).length < 2 ^ (prefixWord ++ tailWord_265814).sum := by decide
  have hdescent : baseEnd_265814 < baseStart_265814 := by decide
  rcases family_descends (prefixWord ++ tailWord_265814) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_265870 : List Nat := [4, 1, 1, 3, 1, 4, 1, 2, 4]
def baseStart_265870 : Nat := 118140960795 + 265870 * 2 ^ 59
def prefixEnd_265870 : Nat := 4983230072969 + 3 ^ 40 * 265870 * 2
def baseEnd_265870 : Nat := 60675156271546673823241

theorem tailTrace_265870 : CollatzResearch.WordTrace tailWord_265870 prefixEnd_265870 60675156271546673823241 := by
  unfold tailWord_265870
  simp only [CollatzResearch.WordTrace]
  refine ⟨1212134443350733978259383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 6464717031203914550716709 1212134443350733978259383)
  ·
    refine ⟨1818201665026100967389075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1212134443350733978259383 1818201665026100967389075)
    ·
      refine ⟨2727302497539151451083613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1818201665026100967389075 2727302497539151451083613)
      ·
        refine ⟨1022738436577181794156355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2727302497539151451083613 1022738436577181794156355)
        ·
          refine ⟨1534107654865772691234533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1022738436577181794156355 1534107654865772691234533)
          ·
            refine ⟨287645185287332379606475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1534107654865772691234533 287645185287332379606475)
            ·
              refine ⟨431467777930998569409713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 287645185287332379606475 431467777930998569409713)
              ·
                refine ⟨323600833448248927057285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 431467777930998569409713 323600833448248927057285)
                ·
                  refine ⟨60675156271546673823241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 323600833448248927057285 60675156271546673823241)
                  ·
                    rfl

theorem cell21_265870_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 4, 1, 2, 4].length) (baseStart_265870 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_265870 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_265870 prefixEnd_265870 := by exact prefixLift 265870
  have htrace : WordTrace (prefixWord ++ tailWord_265870) baseStart_265870 baseEnd_265870 := by
    simpa [prefixWord, tailWord_265870, baseEnd_265870] using wordTrace_append hprefix tailTrace_265870
  have hstable : (prefixWord ++ tailWord_265870).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_265870).length < 2 ^ (prefixWord ++ tailWord_265870).sum := by decide
  have hdescent : baseEnd_265870 < baseStart_265870 := by decide
  rcases family_descends (prefixWord ++ tailWord_265870) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_265887 : List Nat := [1, 1, 2, 7, 1, 1, 3, 1, 4]
def baseStart_265887 : Nat := 118140960795 + 265887 * 2 ^ 59
def prefixEnd_265887 : Nat := 4983230072969 + 3 ^ 40 * 265887 * 2
def baseEnd_265887 : Nat := 60679035903158422039873

theorem tailTrace_265887 : CollatzResearch.WordTrace tailWord_265887 prefixEnd_265887 60679035903158422039873 := by
  unfold tailWord_265887
  simp only [CollatzResearch.WordTrace]
  refine ⟨9697695587744283729443915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6465130391829522486295943 9697695587744283729443915)
  ·
    refine ⟨14546543381616425594165873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9697695587744283729443915 14546543381616425594165873)
    ·
      refine ⟨10909907536212319195624405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14546543381616425594165873 10909907536212319195624405)
      ·
        refine ⟨255700957879976231147447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 10909907536212319195624405 255700957879976231147447)
        ·
          refine ⟨383551436819964346721171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 255700957879976231147447 383551436819964346721171)
          ·
            refine ⟨575327155229946520081757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 383551436819964346721171 575327155229946520081757)
            ·
              refine ⟨215747683211229945030659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 575327155229946520081757 215747683211229945030659)
              ·
                refine ⟨323621524816844917545989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 215747683211229945030659 323621524816844917545989)
                ·
                  refine ⟨60679035903158422039873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 323621524816844917545989 60679035903158422039873)
                  ·
                    rfl

theorem cell21_265887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 1, 1, 3, 1, 4].length) (baseStart_265887 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_265887 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_265887 prefixEnd_265887 := by exact prefixLift 265887
  have htrace : WordTrace (prefixWord ++ tailWord_265887) baseStart_265887 baseEnd_265887 := by
    simpa [prefixWord, tailWord_265887, baseEnd_265887] using wordTrace_append hprefix tailTrace_265887
  have hstable : (prefixWord ++ tailWord_265887).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_265887).length < 2 ^ (prefixWord ++ tailWord_265887).sum := by decide
  have hdescent : baseEnd_265887 < baseStart_265887 := by decide
  rcases family_descends (prefixWord ++ tailWord_265887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_265932 : List Nat := [2, 2, 1, 5, 3, 1, 1, 1, 5]
def baseStart_265932 : Nat := 118140960795 + 265932 * 2 ^ 59
def prefixEnd_265932 : Nat := 4983230072969 + 3 ^ 40 * 265932 * 2
def baseEnd_265932 : Nat := 60689305516248343789781

theorem tailTrace_265932 : CollatzResearch.WordTrace tailWord_265932 prefixEnd_265932 60689305516248343789781 := by
  unfold tailWord_265932
  simp only [CollatzResearch.WordTrace]
  refine ⟨4849668436290628207416025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6466224581720837609888033 4849668436290628207416025)
  ·
    refine ⟨3637251327217971155562019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4849668436290628207416025 3637251327217971155562019)
    ·
      refine ⟨5455876990826956733343029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3637251327217971155562019 5455876990826956733343029)
      ·
        refine ⟨511488467890027193750909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 5455876990826956733343029 511488467890027193750909)
        ·
          refine ⟨191808175458760197656591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 511488467890027193750909 191808175458760197656591)
          ·
            refine ⟨287712263188140296484887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 191808175458760197656591 287712263188140296484887)
            ·
              refine ⟨431568394782210444727331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 287712263188140296484887 431568394782210444727331)
              ·
                refine ⟨647352592173315667090997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 431568394782210444727331 647352592173315667090997)
                ·
                  refine ⟨60689305516248343789781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 647352592173315667090997 60689305516248343789781)
                  ·
                    rfl

theorem cell21_265932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 3, 1, 1, 1, 5].length) (baseStart_265932 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_265932 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_265932 prefixEnd_265932 := by exact prefixLift 265932
  have htrace : WordTrace (prefixWord ++ tailWord_265932) baseStart_265932 baseEnd_265932 := by
    simpa [prefixWord, tailWord_265932, baseEnd_265932] using wordTrace_append hprefix tailTrace_265932
  have hstable : (prefixWord ++ tailWord_265932).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_265932).length < 2 ^ (prefixWord ++ tailWord_265932).sum := by decide
  have hdescent : baseEnd_265932 < baseStart_265932 := by decide
  rcases family_descends (prefixWord ++ tailWord_265932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_265946 : List Nat := [3, 1, 1, 2, 2, 5, 2, 1, 4]
def baseStart_265946 : Nat := 118140960795 + 265946 * 2 ^ 59
def prefixEnd_265946 : Nat := 4983230072969 + 3 ^ 40 * 265946 * 2
def baseEnd_265946 : Nat := 60692500506987430556419

theorem tailTrace_265946 : CollatzResearch.WordTrace tailWord_265946 prefixEnd_265946 60692500506987430556419 := by
  unfold tailWord_265946
  simp only [CollatzResearch.WordTrace]
  refine ⟨2424961873632634201460423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6466564996353691203894461 2424961873632634201460423)
  ·
    refine ⟨3637442810448951302190635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2424961873632634201460423 3637442810448951302190635)
    ·
      refine ⟨5456164215673426953285953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3637442810448951302190635 5456164215673426953285953)
      ·
        refine ⟨4092123161755070214964465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5456164215673426953285953 4092123161755070214964465)
        ·
          refine ⟨3069092371316302661223349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4092123161755070214964465 3069092371316302661223349)
          ·
            refine ⟨287727409810903374489689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 3069092371316302661223349 287727409810903374489689)
            ·
              refine ⟨215795557358177530867267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 287727409810903374489689 215795557358177530867267)
              ·
                refine ⟨323693336037266296300901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 215795557358177530867267 323693336037266296300901)
                ·
                  refine ⟨60692500506987430556419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 323693336037266296300901 60692500506987430556419)
                  ·
                    rfl

theorem cell21_265946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 5, 2, 1, 4].length) (baseStart_265946 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_265946 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_265946 prefixEnd_265946 := by exact prefixLift 265946
  have htrace : WordTrace (prefixWord ++ tailWord_265946) baseStart_265946 baseEnd_265946 := by
    simpa [prefixWord, tailWord_265946, baseEnd_265946] using wordTrace_append hprefix tailTrace_265946
  have hstable : (prefixWord ++ tailWord_265946).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_265946).length < 2 ^ (prefixWord ++ tailWord_265946).sum := by decide
  have hdescent : baseEnd_265946 < baseStart_265946 := by decide
  rcases family_descends (prefixWord ++ tailWord_265946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_265957 : List Nat := [1, 3, 1, 4, 1, 1, 2, 1, 7]
def baseStart_265957 : Nat := 118140960795 + 265957 * 2 ^ 59
def prefixEnd_265957 : Nat := 4983230072969 + 3 ^ 40 * 265957 * 2
def baseEnd_265957 : Nat := 60695010856853855873063

theorem tailTrace_265957 : CollatzResearch.WordTrace tailWord_265957 prefixEnd_265957 60695010856853855873063 := by
  unfold tailWord_265957
  simp only [CollatzResearch.WordTrace]
  refine ⟨9700248697490685684492125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6466832464993790456328083 9700248697490685684492125)
  ·
    refine ⟨3637593261559007131684547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9700248697490685684492125 3637593261559007131684547)
    ·
      refine ⟨5456389892338510697526821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3637593261559007131684547 5456389892338510697526821)
      ·
        refine ⟨1023073104813470755786279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5456389892338510697526821 1023073104813470755786279)
        ·
          refine ⟨1534609657220206133679419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1023073104813470755786279 1534609657220206133679419)
          ·
            refine ⟨2301914485830309200519129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1534609657220206133679419 2301914485830309200519129)
            ·
              refine ⟨1726435864372731900389347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2301914485830309200519129 1726435864372731900389347)
              ·
                refine ⟨2589653796559097850584021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1726435864372731900389347 2589653796559097850584021)
                ·
                  refine ⟨60695010856853855873063, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2589653796559097850584021 60695010856853855873063)
                  ·
                    rfl

theorem cell21_265957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 2, 1, 7].length) (baseStart_265957 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_265957 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_265957 prefixEnd_265957 := by exact prefixLift 265957
  have htrace : WordTrace (prefixWord ++ tailWord_265957) baseStart_265957 baseEnd_265957 := by
    simpa [prefixWord, tailWord_265957, baseEnd_265957] using wordTrace_append hprefix tailTrace_265957
  have hstable : (prefixWord ++ tailWord_265957).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_265957).length < 2 ^ (prefixWord ++ tailWord_265957).sum := by decide
  have hdescent : baseEnd_265957 < baseStart_265957 := by decide
  rcases family_descends (prefixWord ++ tailWord_265957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_265971 : List Nat := [1, 1, 1, 2, 2, 3, 2, 1, 8]
def baseStart_265971 : Nat := 118140960795 + 265971 * 2 ^ 59
def prefixEnd_265971 : Nat := 4983230072969 + 3 ^ 40 * 265971 * 2
def baseEnd_265971 : Nat := 60698205847592942639701

theorem tailTrace_265971 : CollatzResearch.WordTrace tailWord_265971 prefixEnd_265971 60698205847592942639701 := by
  unfold tailWord_265971
  simp only [CollatzResearch.WordTrace]
  refine ⟨9700759319439966075501767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6467172879626644050334511 9700759319439966075501767)
  ·
    refine ⟨14551138979159949113252651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9700759319439966075501767 14551138979159949113252651)
    ·
      refine ⟨21826708468739923669878977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14551138979159949113252651 21826708468739923669878977)
      ·
        refine ⟨16370031351554942752409233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21826708468739923669878977 16370031351554942752409233)
        ·
          refine ⟨12277523513666207064306925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16370031351554942752409233 12277523513666207064306925)
          ·
            refine ⟨4604071317624827649115097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12277523513666207064306925 4604071317624827649115097)
            ·
              refine ⟨3453053488218620736836323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4604071317624827649115097 3453053488218620736836323)
              ·
                refine ⟨5179580232327931105254485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3453053488218620736836323 5179580232327931105254485)
                ·
                  refine ⟨60698205847592942639701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 5179580232327931105254485 60698205847592942639701)
                  ·
                    rfl

theorem cell21_265971_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 2, 1, 8].length) (baseStart_265971 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_265971 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_265971 prefixEnd_265971 := by exact prefixLift 265971
  have htrace : WordTrace (prefixWord ++ tailWord_265971) baseStart_265971 baseEnd_265971 := by
    simpa [prefixWord, tailWord_265971, baseEnd_265971] using wordTrace_append hprefix tailTrace_265971
  have hstable : (prefixWord ++ tailWord_265971).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_265971).length < 2 ^ (prefixWord ++ tailWord_265971).sum := by decide
  have hdescent : baseEnd_265971 < baseStart_265971 := by decide
  rcases family_descends (prefixWord ++ tailWord_265971) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_266084 : List Nat := [2, 3, 1, 1, 5, 2, 1, 3, 3]
def baseStart_266084 : Nat := 118140960795 + 266084 * 2 ^ 59
def prefixEnd_266084 : Nat := 4983230072969 + 3 ^ 40 * 266084 * 2
def baseEnd_266084 : Nat := 60723993987129857256137

theorem tailTrace_266084 : CollatzResearch.WordTrace tailWord_266084 prefixEnd_266084 60723993987129857256137 := by
  unfold tailWord_266084
  simp only [CollatzResearch.WordTrace]
  refine ⟨4852440384015293187182653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6469920512020390916243537 4852440384015293187182653)
  ·
    refine ⟨1819665144005734945193495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4852440384015293187182653 1819665144005734945193495)
    ·
      refine ⟨2729497716008602417790243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1819665144005734945193495 2729497716008602417790243)
      ·
        refine ⟨4094246574012903626685365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2729497716008602417790243 4094246574012903626685365)
        ·
          refine ⟨383835616313709715001753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 4094246574012903626685365 383835616313709715001753)
          ·
            refine ⟨287876712235282286251315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 383835616313709715001753 287876712235282286251315)
            ·
              refine ⟨431815068352923429376973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 287876712235282286251315 431815068352923429376973)
              ·
                refine ⟨161930650632346286016365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 431815068352923429376973 161930650632346286016365)
                ·
                  refine ⟨60723993987129857256137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 161930650632346286016365 60723993987129857256137)
                  ·
                    rfl

theorem cell21_266084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 5, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 5, 2, 1, 3, 3].length) (baseStart_266084 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_266084 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_266084 prefixEnd_266084 := by exact prefixLift 266084
  have htrace : WordTrace (prefixWord ++ tailWord_266084) baseStart_266084 baseEnd_266084 := by
    simpa [prefixWord, tailWord_266084, baseEnd_266084] using wordTrace_append hprefix tailTrace_266084
  have hstable : (prefixWord ++ tailWord_266084).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_266084).length < 2 ^ (prefixWord ++ tailWord_266084).sum := by decide
  have hdescent : baseEnd_266084 < baseStart_266084 := by decide
  rcases family_descends (prefixWord ++ tailWord_266084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_266199 : List Nat := [1, 1, 3, 2, 1, 1, 4, 2, 6]
def baseStart_266199 : Nat := 118140960795 + 266199 * 2 ^ 59
def prefixEnd_266199 : Nat := 4983230072969 + 3 ^ 40 * 266199 * 2
def baseEnd_266199 : Nat := 60750238553915212839235

theorem tailTrace_266199 : CollatzResearch.WordTrace tailWord_266199 prefixEnd_266199 60750238553915212839235 := by
  unfold tailWord_266199
  simp only [CollatzResearch.WordTrace]
  refine ⟨9709075162613961014801651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6472716775075974009867767 9709075162613961014801651)
  ·
    refine ⟨14563612743920941522202477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9709075162613961014801651 14563612743920941522202477)
    ·
      refine ⟨5461354778970353070825929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14563612743920941522202477 5461354778970353070825929)
      ·
        refine ⟨4096016084227764803119447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5461354778970353070825929 4096016084227764803119447)
        ·
          refine ⟨6144024126341647204679171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4096016084227764803119447 6144024126341647204679171)
          ·
            refine ⟨9216036189512470807018757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6144024126341647204679171 9216036189512470807018757)
            ·
              refine ⟨1728006785533588276316017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9216036189512470807018757 1728006785533588276316017)
              ·
                refine ⟨1296005089150191207237013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1728006785533588276316017 1296005089150191207237013)
                ·
                  refine ⟨60750238553915212839235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1296005089150191207237013 60750238553915212839235)
                  ·
                    rfl

theorem cell21_266199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 4, 2, 6].length) (baseStart_266199 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_266199 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_266199 prefixEnd_266199 := by exact prefixLift 266199
  have htrace : WordTrace (prefixWord ++ tailWord_266199) baseStart_266199 baseEnd_266199 := by
    simpa [prefixWord, tailWord_266199, baseEnd_266199] using wordTrace_append hprefix tailTrace_266199
  have hstable : (prefixWord ++ tailWord_266199).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_266199).length < 2 ^ (prefixWord ++ tailWord_266199).sum := by decide
  have hdescent : baseEnd_266199 < baseStart_266199 := by decide
  rcases family_descends (prefixWord ++ tailWord_266199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_266233 : List Nat := [1, 2, 1, 3, 1, 5, 3, 1, 4]
def baseStart_266233 : Nat := 118140960795 + 266233 * 2 ^ 59
def prefixEnd_266233 : Nat := 4983230072969 + 3 ^ 40 * 266233 * 2
def baseEnd_266233 : Nat := 60757997817138709272499

theorem tailTrace_266233 : CollatzResearch.WordTrace tailWord_266233 prefixEnd_266233 60757997817138709272499 := by
  unfold tailWord_266233
  simp only [CollatzResearch.WordTrace]
  refine ⟨9710315244490784821539353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6473543496327189881026235 9710315244490784821539353)
  ·
    refine ⟨7282736433368088616154515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9710315244490784821539353 7282736433368088616154515)
    ·
      refine ⟨10924104650052132924231773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7282736433368088616154515 10924104650052132924231773)
      ·
        refine ⟨4096539243769549846586915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10924104650052132924231773 4096539243769549846586915)
        ·
          refine ⟨6144808865654324769880373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4096539243769549846586915 6144808865654324769880373)
          ·
            refine ⟨576075831155092947176285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 6144808865654324769880373 576075831155092947176285)
            ·
              refine ⟨216028436683159855191107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 576075831155092947176285 216028436683159855191107)
              ·
                refine ⟨324042655024739782786661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 216028436683159855191107 324042655024739782786661)
                ·
                  refine ⟨60757997817138709272499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 324042655024739782786661 60757997817138709272499)
                  ·
                    rfl

theorem cell21_266233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 5, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 5, 3, 1, 4].length) (baseStart_266233 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_266233 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_266233 prefixEnd_266233 := by exact prefixLift 266233
  have htrace : WordTrace (prefixWord ++ tailWord_266233) baseStart_266233 baseEnd_266233 := by
    simpa [prefixWord, tailWord_266233, baseEnd_266233] using wordTrace_append hprefix tailTrace_266233
  have hstable : (prefixWord ++ tailWord_266233).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_266233).length < 2 ^ (prefixWord ++ tailWord_266233).sum := by decide
  have hdescent : baseEnd_266233 < baseStart_266233 := by decide
  rcases family_descends (prefixWord ++ tailWord_266233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_266247 : List Nat := [1, 1, 4, 3, 1, 2, 4, 5]
def baseStart_266247 : Nat := 118140960795 + 266247 * 2 ^ 59
def prefixEnd_266247 : Nat := 4983230072969 + 3 ^ 40 * 266247 * 2
def baseEnd_266247 : Nat := 20253730935959265346379

theorem tailTrace_266247 : CollatzResearch.WordTrace tailWord_266247 prefixEnd_266247 20253730935959265346379 := by
  unfold tailWord_266247
  simp only [CollatzResearch.WordTrace]
  refine ⟨9710825866440065212548995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6473883910960043475032663 9710825866440065212548995)
  ·
    refine ⟨14566238799660097818823493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9710825866440065212548995 14566238799660097818823493)
    ·
      refine ⟨2731169774936268341029405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 14566238799660097818823493 2731169774936268341029405)
      ·
        refine ⟨1024188665601100627886027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2731169774936268341029405 1024188665601100627886027)
        ·
          refine ⟨1536282998401650941829041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1024188665601100627886027 1536282998401650941829041)
          ·
            refine ⟨1152212248801238206371781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1536282998401650941829041 1152212248801238206371781)
            ·
              refine ⟨216039796650232163694709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1152212248801238206371781 216039796650232163694709)
              ·
                refine ⟨20253730935959265346379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 216039796650232163694709 20253730935959265346379)
                ·
                  rfl

theorem cell21_266247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 4, 5].length) (baseStart_266247 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_266247 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_266247 prefixEnd_266247 := by exact prefixLift 266247
  have htrace : WordTrace (prefixWord ++ tailWord_266247) baseStart_266247 baseEnd_266247 := by
    simpa [prefixWord, tailWord_266247, baseEnd_266247] using wordTrace_append hprefix tailTrace_266247
  have hstable : (prefixWord ++ tailWord_266247).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_266247).length < 2 ^ (prefixWord ++ tailWord_266247).sum := by decide
  have hdescent : baseEnd_266247 < baseStart_266247 := by decide
  rcases family_descends (prefixWord ++ tailWord_266247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_266275 : List Nat := [1, 1, 1, 4, 3, 1, 1, 3, 6]
def baseStart_266275 : Nat := 118140960795 + 266275 * 2 ^ 59
def prefixEnd_266275 : Nat := 4983230072969 + 3 ^ 40 * 266275 * 2
def baseEnd_266275 : Nat := 60767582789355969572413

theorem tailTrace_266275 : CollatzResearch.WordTrace tailWord_266275 prefixEnd_266275 60767582789355969572413 := by
  unfold tailWord_266275
  simp only [CollatzResearch.WordTrace]
  refine ⟨9711847110338625994568279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6474564740225750663045519 9711847110338625994568279)
  ·
    refine ⟨14567770665507938991852419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9711847110338625994568279 14567770665507938991852419)
    ·
      refine ⟨21851655998261908487778629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14567770665507938991852419 21851655998261908487778629)
      ·
        refine ⟨4097185499674107841458493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 21851655998261908487778629 4097185499674107841458493)
        ·
          refine ⟨1536444562377790440546935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4097185499674107841458493 1536444562377790440546935)
          ·
            refine ⟨2304666843566685660820403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1536444562377790440546935 2304666843566685660820403)
            ·
              refine ⟨3457000265350028491230605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2304666843566685660820403 3457000265350028491230605)
              ·
                refine ⟨1296375099506260684211477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3457000265350028491230605 1296375099506260684211477)
                ·
                  refine ⟨60767582789355969572413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1296375099506260684211477 60767582789355969572413)
                  ·
                    rfl

theorem cell21_266275_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 1, 3, 6].length) (baseStart_266275 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_266275 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_266275 prefixEnd_266275 := by exact prefixLift 266275
  have htrace : WordTrace (prefixWord ++ tailWord_266275) baseStart_266275 baseEnd_266275 := by
    simpa [prefixWord, tailWord_266275, baseEnd_266275] using wordTrace_append hprefix tailTrace_266275
  have hstable : (prefixWord ++ tailWord_266275).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_266275).length < 2 ^ (prefixWord ++ tailWord_266275).sum := by decide
  have hdescent : baseEnd_266275 < baseStart_266275 := by decide
  rcases family_descends (prefixWord ++ tailWord_266275) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_266326 : List Nat := [5, 2, 2, 1, 1, 1, 1, 4, 4]
def baseStart_266326 : Nat := 118140960795 + 266326 * 2 ^ 59
def prefixEnd_266326 : Nat := 4983230072969 + 3 ^ 40 * 266326 * 2
def baseEnd_266326 : Nat := 60779221684191214222309

theorem tailTrace_266326 : CollatzResearch.WordTrace tailWord_266326 prefixEnd_266326 60779221684191214222309 := by
  unfold tailWord_266326
  simp only [CollatzResearch.WordTrace]
  refine ⟨607106702072116356542177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 6475804822102574469783221 607106702072116356542177)
  ·
    refine ⟨455330026554087267406633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 607106702072116356542177 455330026554087267406633)
    ·
      refine ⟨341497519915565450554975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 455330026554087267406633 341497519915565450554975)
      ·
        refine ⟨512246279873348175832463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 341497519915565450554975 512246279873348175832463)
        ·
          refine ⟨768369419810022263748695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 512246279873348175832463 768369419810022263748695)
          ·
            refine ⟨1152554129715033395623043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 768369419810022263748695 1152554129715033395623043)
            ·
              refine ⟨1728831194572550093434565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1152554129715033395623043 1728831194572550093434565)
              ·
                refine ⟨324155848982353142518981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1728831194572550093434565 324155848982353142518981)
                ·
                  refine ⟨60779221684191214222309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 324155848982353142518981 60779221684191214222309)
                  ·
                    rfl

theorem cell21_266326_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 1, 4, 4].length) (baseStart_266326 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_266326 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_266326 prefixEnd_266326 := by exact prefixLift 266326
  have htrace : WordTrace (prefixWord ++ tailWord_266326) baseStart_266326 baseEnd_266326 := by
    simpa [prefixWord, tailWord_266326, baseEnd_266326] using wordTrace_append hprefix tailTrace_266326
  have hstable : (prefixWord ++ tailWord_266326).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_266326).length < 2 ^ (prefixWord ++ tailWord_266326).sum := by decide
  have hdescent : baseEnd_266326 < baseStart_266326 := by decide
  rcases family_descends (prefixWord ++ tailWord_266326) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_266402 : List Nat := [3, 3, 1, 3, 1, 2, 3, 1, 4]
def baseStart_266402 : Nat := 118140960795 + 266402 * 2 ^ 59
def prefixEnd_266402 : Nat := 4983230072969 + 3 ^ 40 * 266402 * 2
def baseEnd_266402 : Nat := 60796565919631970955487

theorem tailTrace_266402 : CollatzResearch.WordTrace tailWord_266402 prefixEnd_266402 60796565919631970955487 := by
  unfold tailWord_266402
  simp only [CollatzResearch.WordTrace]
  refine ⟨2429119795219631671110365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6477652787252351122960973 2429119795219631671110365)
  ·
    refine ⟨910919923207361876666387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2429119795219631671110365 910919923207361876666387)
    ·
      refine ⟨1366379884811042814999581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 910919923207361876666387 1366379884811042814999581)
      ·
        refine ⟨512392456804141055624843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1366379884811042814999581 512392456804141055624843)
        ·
          refine ⟨768588685206211583437265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 512392456804141055624843 768588685206211583437265)
          ·
            refine ⟨576441513904658687577949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 768588685206211583437265 576441513904658687577949)
            ·
              refine ⟨216165567714247007841731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 576441513904658687577949 216165567714247007841731)
              ·
                refine ⟨324248351571370511762597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 216165567714247007841731 324248351571370511762597)
                ·
                  refine ⟨60796565919631970955487, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 324248351571370511762597 60796565919631970955487)
                  ·
                    rfl

theorem cell21_266402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 2, 3, 1, 4].length) (baseStart_266402 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_266402 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_266402 prefixEnd_266402 := by exact prefixLift 266402
  have htrace : WordTrace (prefixWord ++ tailWord_266402) baseStart_266402 baseEnd_266402 := by
    simpa [prefixWord, tailWord_266402, baseEnd_266402] using wordTrace_append hprefix tailTrace_266402
  have hstable : (prefixWord ++ tailWord_266402).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_266402).length < 2 ^ (prefixWord ++ tailWord_266402).sum := by decide
  have hdescent : baseEnd_266402 < baseStart_266402 := by decide
  rcases family_descends (prefixWord ++ tailWord_266402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_266461 : List Nat := [1, 4, 3, 2, 1, 2, 1, 3, 4]
def baseStart_266461 : Nat := 118140960795 + 266461 * 2 ^ 59
def prefixEnd_266461 : Nat := 4983230072969 + 3 ^ 40 * 266461 * 2
def baseEnd_266461 : Nat := 60810030523460979472033

theorem tailTrace_266461 : CollatzResearch.WordTrace tailWord_266461 prefixEnd_266461 60810030523460979472033 := by
  unfold tailWord_266461
  simp only [CollatzResearch.WordTrace]
  refine ⟨9718631087664779760839237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6479087391776519840559491 9718631087664779760839237)
  ·
    refine ⟨1822243328937146205157357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 9718631087664779760839237 1822243328937146205157357)
    ·
      refine ⟨683341248351429826934009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1822243328937146205157357 683341248351429826934009)
      ·
        refine ⟨512505936263572370200507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 683341248351429826934009 512505936263572370200507)
        ·
          refine ⟨768758904395358555300761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 512505936263572370200507 768758904395358555300761)
          ·
            refine ⟨576569178296518916475571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 768758904395358555300761 576569178296518916475571)
            ·
              refine ⟨864853767444778374713357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 576569178296518916475571 864853767444778374713357)
              ·
                refine ⟨324320162791791890517509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 864853767444778374713357 324320162791791890517509)
                ·
                  refine ⟨60810030523460979472033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 324320162791791890517509 60810030523460979472033)
                  ·
                    rfl

theorem cell21_266461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 2, 1, 3, 4].length) (baseStart_266461 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_266461 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_266461 prefixEnd_266461 := by exact prefixLift 266461
  have htrace : WordTrace (prefixWord ++ tailWord_266461) baseStart_266461 baseEnd_266461 := by
    simpa [prefixWord, tailWord_266461, baseEnd_266461] using wordTrace_append hprefix tailTrace_266461
  have hstable : (prefixWord ++ tailWord_266461).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_266461).length < 2 ^ (prefixWord ++ tailWord_266461).sum := by decide
  have hdescent : baseEnd_266461 < baseStart_266461 := by decide
  rcases family_descends (prefixWord ++ tailWord_266461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_266599 : List Nat := [1, 1, 5, 1, 3, 3, 1, 3, 3]
def baseStart_266599 : Nat := 118140960795 + 266599 * 2 ^ 59
def prefixEnd_266599 : Nat := 4983230072969 + 3 ^ 40 * 266599 * 2
def baseEnd_266599 : Nat := 60841524003603406171751

theorem tailTrace_266599 : CollatzResearch.WordTrace tailWord_266599 prefixEnd_266599 60841524003603406171751 := by
  unfold tailWord_266599
  simp only [CollatzResearch.WordTrace]
  refine ⟨9723664361164829329362851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6482442907443219552908567 9723664361164829329362851)
  ·
    refine ⟨14585496541747243994044277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9723664361164829329362851 14585496541747243994044277)
    ·
      refine ⟨1367390300788804124441651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 14585496541747243994044277 1367390300788804124441651)
      ·
        refine ⟨2051085451183206186662477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1367390300788804124441651 2051085451183206186662477)
        ·
          refine ⟨769157044193702319998429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2051085451183206186662477 769157044193702319998429)
          ·
            refine ⟨288433891572638369999411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 769157044193702319998429 288433891572638369999411)
            ·
              refine ⟨432650837358957554999117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 288433891572638369999411 432650837358957554999117)
              ·
                refine ⟨162244064009609083124669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 432650837358957554999117 162244064009609083124669)
                ·
                  refine ⟨60841524003603406171751, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 162244064009609083124669 60841524003603406171751)
                  ·
                    rfl

theorem cell21_266599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 3, 1, 3, 3].length) (baseStart_266599 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_266599 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_266599 prefixEnd_266599 := by exact prefixLift 266599
  have htrace : WordTrace (prefixWord ++ tailWord_266599) baseStart_266599 baseEnd_266599 := by
    simpa [prefixWord, tailWord_266599, baseEnd_266599] using wordTrace_append hprefix tailTrace_266599
  have hstable : (prefixWord ++ tailWord_266599).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_266599).length < 2 ^ (prefixWord ++ tailWord_266599).sum := by decide
  have hdescent : baseEnd_266599 < baseStart_266599 := by decide
  rcases family_descends (prefixWord ++ tailWord_266599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_266610 : List Nat := [3, 2, 1, 2, 1, 5, 7]
def baseStart_266610 : Nat := 118140960795 + 266610 * 2 ^ 59
def prefixEnd_266610 : Nat := 4983230072969 + 3 ^ 40 * 266610 * 2
def baseEnd_266610 : Nat := 6760448261496647943155

theorem tailTrace_266610 : CollatzResearch.WordTrace tailWord_266610 prefixEnd_266610 6760448261496647943155 := by
  unfold tailWord_266610
  simp only [CollatzResearch.WordTrace]
  refine ⟨2431016391031244552003321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6482710376083318805342189 2431016391031244552003321)
  ·
    refine ⟨1823262293273433414002491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2431016391031244552003321 1823262293273433414002491)
    ·
      refine ⟨2734893439910150121003737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1823262293273433414002491 2734893439910150121003737)
      ·
        refine ⟨2051170079932612590752803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2734893439910150121003737 2051170079932612590752803)
        ·
          refine ⟨3076755119898918886129205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2051170079932612590752803 3076755119898918886129205)
          ·
            refine ⟨288445792490523645574613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 3076755119898918886129205 288445792490523645574613)
            ·
              refine ⟨6760448261496647943155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 288445792490523645574613 6760448261496647943155)
              ·
                rfl

theorem cell21_266610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 5, 7].length) (baseStart_266610 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_266610 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_266610 prefixEnd_266610 := by exact prefixLift 266610
  have htrace : WordTrace (prefixWord ++ tailWord_266610) baseStart_266610 baseEnd_266610 := by
    simpa [prefixWord, tailWord_266610, baseEnd_266610] using wordTrace_append hprefix tailTrace_266610
  have hstable : (prefixWord ++ tailWord_266610).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_266610).length < 2 ^ (prefixWord ++ tailWord_266610).sum := by decide
  have hdescent : baseEnd_266610 < baseStart_266610 := by decide
  rcases family_descends (prefixWord ++ tailWord_266610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_266658 : List Nat := [3, 3, 1, 2, 1, 1, 2, 5, 3]
def baseStart_266658 : Nat := 118140960795 + 266658 * 2 ^ 59
def prefixEnd_266658 : Nat := 4983230072969 + 3 ^ 40 * 266658 * 2
def baseEnd_266658 : Nat := 60854988607432414688297

theorem tailTrace_266658 : CollatzResearch.WordTrace tailWord_266658 prefixEnd_266658 60854988607432414688297 := by
  unfold tailWord_266658
  simp only [CollatzResearch.WordTrace]
  refine ⟨2431454066987770601440157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6483877511967388270507085 2431454066987770601440157)
  ·
    refine ⟨911795275120413975540059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2431454066987770601440157 911795275120413975540059)
    ·
      refine ⟨1367692912680620963310089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 911795275120413975540059 1367692912680620963310089)
      ·
        refine ⟨1025769684510465722482567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1367692912680620963310089 1025769684510465722482567)
        ·
          refine ⟨1538654526765698583723851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1025769684510465722482567 1538654526765698583723851)
          ·
            refine ⟨2307981790148547875585777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1538654526765698583723851 2307981790148547875585777)
            ·
              refine ⟨1730986342611410906689333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2307981790148547875585777 1730986342611410906689333)
              ·
                refine ⟨162279969619819772502125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1730986342611410906689333 162279969619819772502125)
                ·
                  refine ⟨60854988607432414688297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 162279969619819772502125 60854988607432414688297)
                  ·
                    rfl

theorem cell21_266658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 2, 5, 3].length) (baseStart_266658 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_266658 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_266658 prefixEnd_266658 := by exact prefixLift 266658
  have htrace : WordTrace (prefixWord ++ tailWord_266658) baseStart_266658 baseEnd_266658 := by
    simpa [prefixWord, tailWord_266658, baseEnd_266658] using wordTrace_append hprefix tailTrace_266658
  have hstable : (prefixWord ++ tailWord_266658).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_266658).length < 2 ^ (prefixWord ++ tailWord_266658).sum := by decide
  have hdescent : baseEnd_266658 < baseStart_266658 := by decide
  rcases family_descends (prefixWord ++ tailWord_266658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan21Incremental
